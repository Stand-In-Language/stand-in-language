{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections   #-}

-- | The net's low-level runtime: 'Telomare.IC''s compilation, with the net
-- reduced by C over flat arrays of words (cbits/tel_ic.c) rather than over
-- 'Data.IntMap.IntMap's.
--
-- The C and its rule table are printed from the @bend@ branch's Bend, where
-- the table is proven to be the Bend net's rules. That net differs from this
-- module's sibling in one way, and this module makes up the difference: a user
-- @if@ builds only the branch its scrutinee chooses ('chosenIfs'), where
-- 'Telomare.IC' builds both and parks their applications. So the C has no
-- parking and no guided erasure, and its interaction counts are not
-- 'Telomare.IC''s, which --ic --meter still reports.
--
-- This module holds what the C needs and cannot do: it lays the compiled net
-- out as words, names the stuck values (their messages are Haskell strings),
-- and reads the result back through 'Telomare.IC.readback'.
module Telomare.IC.Native
  ( chosenIfs
  , icEvalNative
  , icNativeSession
  , icRunNative
  ) where

import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Monad (forM_, unless)
import Control.Monad.Except (runExceptT, throwError)
import qualified Control.Monad.State.Strict as State
import Crypto.Hash (Digest, SHA256)
import Data.Bits (shiftR, (.&.))
import Data.Foldable (toList)
import Data.Int (Int32)
import qualified Data.IntMap.Strict as IntMap
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import Data.List (isPrefixOf)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Word (Word32)
import Foreign.ForeignPtr (ForeignPtr, mallocForeignPtrArray, withForeignPtr)
import Foreign.Marshal.Alloc (alloca, callocBytes, free)
import Foreign.Marshal.Array (advancePtr, allocaArray, copyArray, mallocArray,
                              pokeArray)
import Foreign.Marshal.Utils (fillBytes)
import Foreign.Ptr (Ptr)
import Foreign.Storable (peek, peekElemOff, poke, pokeElemOff)
import System.IO.Unsafe (unsafePerformIO)
import Telomare.EAL (CapShape (..), Step (..))
import Telomare.IC
import Telomare.IR.Base (AbortOrigin, AbortableF (..), BasicExpr,
                         BasicExprF (..), FunctionIndex, StuckF (..), forget,
                         isData, messageData, pattern PairB, pattern SetEnvB,
                         pattern StuckEE, pattern ZeroB)
import Telomare.IR.Core (CompiledExpr, CompiledExprF (..), RunTimeError)
import Telomare.Machine (twiddleB, unsizedStepMEInd, unsizedStepMTInd)
import Telomare.Resolve (KeyedExpr, keyDefers)

foreign import ccall unsafe "tel_ic.h tel_ic_reduce"
  c_reduce :: Ptr (Ptr Word32) -> Ptr Word32 -> Ptr Word32 -> IO ()

foreign import ccall unsafe "tel_ic.h tel_ic_stuck"
  c_stuck :: Ptr (Ptr Word32) -> Ptr Word32 -> Ptr Word32 -> Word32 -> Word32 -> Word32
          -> Word32 -> Word32 -> Word32 -> Word32 -> Word32 -> IO ()

-- * The if the net runs

-- | Rewrite every user @if@ so only the chosen branch is built. A branch becomes
-- a closure over just the parts of the environment the two branches use,
-- captured as a list; the gate chooses a closure, which is then applied to the
-- list. An existing closure keeps its keys, which name it as it was written,
-- so EAL's per-hash guidance still finds it. @Bend@: IC.bend's @collect@.
chosenIfs :: KeyedExpr -> KeyedExpr
chosenIfs = \case
  _ :< CompiledExprS (SetEnvSF
      (_ :< CompiledExprB (PairSF
        (_ :< CompiledExprS (SetEnvSF
          (_ :< CompiledExprB (PairSF (_ :< CompiledExprS GateSF) s))))
        (_ :< CompiledExprB (PairSF l r)))))
    -> let l' = chosenIfs l
           r' = chosenIfs r
           ps = captured (Map.unionWith (+) (envUsage (forget l')) (envUsage (forget r')))
       in setEnv (pair
            (setEnv (pair
              (setEnv (pair (Nothing :< CompiledExprS GateSF) (chosenIfs s)))
              (pair (branch unsizedStepMEInd (trimmed ps [] l'))
                    (branch unsizedStepMTInd (trimmed ps [] r')))))
            (capture ps))
  a :< x -> a :< fmap chosenIfs x
  where
    setEnv = (Nothing :<) . CompiledExprS . SetEnvSF
    pair x y = Nothing :< CompiledExprB (PairSF x y)

-- | A branch as a closure, keyed like any other.
branch :: Int -> KeyedExpr -> KeyedExpr
branch ind body = keys :< CompiledExprS (DeferSF fi body)
  where
    fi = toEnum ind :: FunctionIndex
    keys = case keyDefers (StuckEE (DeferSF fi (forget body))) of
      k :< _ -> k

-- | The environment paths in use with none used above them.
captured :: Map [Step] Int -> [[Step]]
captured us = filter (\p -> not (any (\q -> q /= p && q `isPrefixOf` p) ps)) ps
  where ps = Map.keys us

-- | x projected along a path, its first step innermost.
proj :: [Step] -> KeyedExpr -> KeyedExpr
proj path x = foldl (\y s -> Nothing :< CompiledExprS (step s y)) x path
  where
    step SL = LeftSF
    step SR = RightSF

env :: KeyedExpr
env = Nothing :< CompiledExprS EnvSF

-- | The captured parts, as a list.
capture :: [[Step]] -> KeyedExpr
capture = \case
  [] -> Nothing :< CompiledExprB ZeroSF
  p : rest -> Nothing :< CompiledExprB (PairSF (proj p env) (capture rest))

-- | Where the environment path q is in the captured list.
moved :: [[Step]] -> [Step] -> [Step]
moved ps q = go ps []
  where
    go [] _ = q
    go (p : rest) at
      | p `isPrefixOf` q = at <> (SL : drop (length p) q)
      | otherwise = go rest (at <> [SR])

-- | A branch's code reading the captured list instead of the environment,
-- carrying the projections over a node down to the Env they start from.
trimmed :: [[Step]] -> [Step] -> KeyedExpr -> KeyedExpr
trimmed ps path = \case
  _ :< CompiledExprS EnvSF -> proj (moved ps path) env
  _ :< CompiledExprS (LeftSF c) -> trimmed ps (SL : path) c
  _ :< CompiledExprS (RightSF c) -> trimmed ps (SR : path) c
  a :< CompiledExprB (PairSF x y) ->
    proj path (a :< CompiledExprB (PairSF (trimmed ps [] x) (trimmed ps [] y)))
  a :< CompiledExprS (SetEnvSF c) -> proj path (a :< CompiledExprS (SetEnvSF (trimmed ps [] c)))
  a :< CompiledExprA (AbortF o m) -> proj path (a :< CompiledExprA (AbortF o (trimmed ps [] m)))
  other -> proj path other

-- * Words

kRoot, kExt, kEra, kZero, kGate, kConst, kRef, kPair, kAborted, kDup, kSplit,
  kSetEnv, kApply, kScrut, kLeft, kRight, kStuck :: Word32
kRoot = 1
kExt = 2
kEra = 3
kZero = 4
kGate = 5
kConst = 6
kRef = 7
kPair = 8
kAborted = 9
kDup = 10
kSplit = 11
kSetEnv = 12
kApply = 13
kScrut = 14
kLeft = 16
kRight = 17
kStuck = 18

-- | The two tables Haskell keeps for the words: the constants' words, built
-- backward, placed from @lyBase@; and each aborted agent's origin.
data Layout = Layout
  { lyBase    :: !Word32
  , lyConsts  :: [Word32]
  , lyCount   :: !Word32
  , lyOrigins :: IntMap.IntMap AbortOrigin
  }

type Lay = State.State Layout

word :: Enum a => a -> Word32
word = fromIntegral . (fromIntegral :: Int -> Int32) . fromEnum

-- | Closed data's word: 0 for 0, else where its two parts are in the store.
constWord :: BasicExpr -> Lay Word32
constWord = \case
  ZeroB -> pure 0
  PairB a b -> do
    wa <- constWord a
    wb <- constWord b
    ly <- State.get
    let at = lyBase ly + lyCount ly
    State.put ly { lyConsts = wb : wa : lyConsts ly, lyCount = lyCount ly + 2 }
    pure at
  _notData -> pure 0

-- | Data's word and the words it needs, placed from at.
dataWords :: Word32 -> BasicExpr -> (Word32, [Word32])
dataWords at d =
  let (w, ly) = State.runState (constWord d) (Layout at [] 0 IntMap.empty)
  in (w, reverse (lyConsts ly))

kindWords :: ICKind -> Lay (Word32, Word32, Word32)
kindWords = \case
  ICRoot -> leaf kRoot
  ICExt -> leaf kExt
  ICEra -> leaf kEra
  ICZero -> leaf kZero
  ICGate -> leaf kGate
  ICRef tid fi -> pure (kRef, fromIntegral tid, word fi)
  ICPair -> leaf kPair
  ICConst d -> (kConst, , 0) <$> constWord d
  ICAborted o -> do
    ly <- State.get
    let i = IntMap.size (lyOrigins ly)
    State.put ly { lyOrigins = IntMap.insert i o (lyOrigins ly) }
    pure (kAborted, fromIntegral i, 0)
  ICDup l -> pure (kDup, fromIntegral l, 0)
  ICSplit -> leaf kSplit
  ICSetEnv -> leaf kSetEnv
  ICApply -> leaf kApply
  ICScrut -> leaf kScrut
  ICLeft -> leaf kLeft
  ICRight -> leaf kRight
  ICStuckV _ -> leaf kStuck
  where leaf k = pure (k, 0, 0)

-- | The store's words for one template: agents, boundary, labels and wires,
-- then (kind, a, b) per agent, then each wire once. @Bend@: IC.bend's @ser.*@.
templateWords :: Template -> Lay [Word32]
templateWords tpl = do
  triples <- traverse (kindWords . nodeKind) nodes
  let wires = [ (portW n s, portW q qs)
              | (n, nd) <- IntMap.toList (tplNodes tpl)
              , (s, q') <- IntMap.toList (nodePorts nd)
              , Port n s < q'
              , let Port q qs = q' ]
  pure $ [ fromIntegral (IntMap.size (tplNodes tpl))
         , fromIntegral (tplExt tpl)
         , fromIntegral (tplLabels tpl)
         , fromIntegral (length wires) ]
      <> concat [ [k, a, b] | (k, a, b) <- toList triples ]
      <> concat [ [p, q] | (p, q) <- wires ]
  where
    nodes = IntMap.elems (tplNodes tpl)
    portW n s = fromIntegral (n * 4 + s)

shapeSize :: CapShape -> Word32
shapeSize = \case
  CapPair a b -> 2 + shapeSize a + shapeSize b
  _leaf -> 1

-- | A capture shape's words, placed at offset at.
shapeWords :: CapShape -> Word32 -> [Word32]
shapeWords shape at = case shape of
  CapData -> [1]
  CapCode -> [2]
  CapOther -> [3]
  CapPair a b ->
    let at2 = at + 2 + shapeSize a
    in 4 : at2 : shapeWords a (at + 2) <> shapeWords b at2

-- | The template store: count, scratch map's base, each template's offset, each
-- template's plan (0: none), constants, templates, plans, scratch.
storeWords :: IntMap.IntMap Template -> Map (Digest SHA256) CapShape
           -> [Node] -> ([Word32], [(Word32, Word32, Word32)], IntMap.IntMap AbortOrigin)
storeWords tpls guidance entry =
  ( [t, at + fromIntegral (length plans)]
      <> offsets <> planOffs
      <> reverse (lyConsts ly)
      <> concat bodies <> plans
      <> replicate maxK 0
  , triples, lyOrigins ly )
  where
    t = fromIntegral (IntMap.size tpls) :: Word32
    base = 2 + 2 * t
    ((bodies, triples), ly) = State.runState build (Layout base [] 0 IntMap.empty)
    build = do
      bs <- traverse templateWords (IntMap.elems tpls)
      ts <- traverse (kindWords . nodeKind) entry
      pure (bs, ts)
    first = base + lyCount ly
    lens = fmap (fromIntegral . length) bodies :: [Word32]
    offsets = init (scanl (+) first lens)
    at = first + sum lens
    plan tpl = Map.lookup (tplHash tpl) guidance
    (planOffs, plans) =
      let step (o, offs, ws) tpl = case plan tpl of
            Nothing -> (o, 0 : offs, ws)
            Just s ->
              let shape = CapPair CapCode s
              in (o + shapeSize shape, o : offs, ws <> shapeWords shape o)
          (_, offs', ws') = foldl step (at, [], []) (IntMap.elems tpls)
      in (reverse offs', ws')
    maxK = maximum (0 : fmap (IntMap.size . tplNodes) (IntMap.elems tpls))

-- * Running

-- | A program laid out once, to run on many inputs: the store and the agents
-- before the input is in, and the input's agent to fill in (if it has one).
data Prepared = Prepared
  { prState   :: ICState
  , prRoot    :: Int
  , prHole    :: Maybe Int
  , prStore   :: ForeignPtr Word32
  , prLen     :: Int
  , prMem     :: ForeignPtr Word32
  , prMemLen  :: Int
  , prCount   :: Int
  , prPairs   :: Int
  , prOrigins :: IntMap.IntMap AbortOrigin
  }

-- | Lay a compiled net out as words. @compile@ returned the root and the input's
-- agent, if it left one to fill in.
layout :: Map (Digest SHA256) CapShape -> (Int, Maybe Int) -> ICState -> Prepared
layout guidance (root, hole) st = unsafePerformIO $ do
  let nodes = IntMap.toList (icNodes st)
      (store, triples, origins) =
        storeWords (icTemplates st) guidance (fmap snd nodes)
      count = length nodes + 1
      pairs = reverse (toList (icParked st)) <> reverse (icActive st)
      memLen = max count (length pairs + 1) * agentWords
      lenStore = length store
  storeP <- mallocForeignPtrArray lenStore
  withForeignPtr storeP (`pokeArray` store)
  memP <- mallocForeignPtrArray memLen
  withForeignPtr memP $ \mem -> do
    fillBytes mem 0 (memLen * 4)
    forM_ (zip nodes triples) $ \((n, nd), (k, a, b)) -> do
      let at = (n + 1) * agentWords
      pokeElemOff mem at k
      pokeElemOff mem (at + 4) a
      pokeElemOff mem (at + 5) b
      forM_ (IntMap.toList (nodePorts nd)) $ \(s, q) ->
        pokeElemOff mem (at + 1 + s) (entryPort q)
    forM_ (zip [0 ..] pairs) $ \(i, (a, b)) -> do
      pokeElemOff mem (i * agentWords + 6) (fromIntegral (a + 1))
      pokeElemOff mem (i * agentWords + 7) (fromIntegral (b + 1))
  pure Prepared
    { prState = st, prRoot = root, prHole = hole
    , prStore = storeP, prLen = lenStore
    , prMem = memP, prMemLen = memLen
    , prCount = count, prPairs = length pairs, prOrigins = origins }

prepared :: Map (Digest SHA256) CapShape -> Int -> ICM (Int, Maybe Int)
         -> Either ICError Prepared
prepared guidance fuel build =
  case State.runState (runExceptT build) (emptyState guidance fuel) of
    (Left e, _)   -> Left e
    (Right r, st) -> Right (layout guidance r st)

-- | One closed term on the C, under per-hash capture layouts: the raw outcome,
-- and the interactions spent.
icRunNative :: Map (Digest SHA256) CapShape -> Int -> CompiledExpr
            -> (Either ICError CompiledExpr, Int)
icRunNative guidance fuel term =
  case prepared guidance fuel build of
    Left e  -> (Left e, 0)
    Right p -> unsafePerformIO (runPrepared p fuel Nothing)
  where
    keyed = chosenIfs (keyDefers term)
    build = do
      unless (Map.null (envUsage (forget keyed))) . throwError $
        ICStuck "unbound Env at top level"
      setupSelectors
      root <- newNode ICRoot
      p <- compileTerm keyed
      connect (Port root 0) p
      pure (root, Nothing)

-- | An evaluator for a session of the given functions: each is compiled once,
-- and its applications to data ('appB', as the iteration loop makes them) only
-- fill in the input. Anything else is compiled as it comes.
icNativeSession :: Map (Digest SHA256) CapShape -> [CompiledExpr] -> Int -> CompiledExpr
                -> (Either ICError CompiledExpr, Int)
icNativeSession guidance funs = \fuel term -> case term of
  SetEnvB (SetEnvB (PairB _ (PairB input fun)))
    | isData input, Just (Right p) <- lookup fun programs ->
        unsafePerformIO (runPrepared p fuel (Just (messageData input)))
  _other -> icRunNative guidance fuel term
  where
    programs = [(f, prepared guidance 0 (applied f)) | f <- funs]
    applied f = do
      setupSelectors
      root <- newNode ICRoot
      hole <- newNode ICZero
      inner <- newNode ICPair
      connect (Port inner 1) (Port hole 0)
      connect (Port inner 2) =<< compileTerm (chosenIfs (keyDefers f))
      outer <- newNode ICPair
      connect (Port outer 1) =<< compileTerm (keyDefers twiddleB)
      connect (Port outer 2) (Port inner 0)
      pair <- newNode ICSetEnv
      connect (Port pair 0) (Port outer 0)
      run <- newNode ICSetEnv
      connect (Port run 0) (Port pair 1)
      connect (Port root 0) (Port run 1)
      pure (root, Just hole)

-- | Evaluate under the reference evaluator's contract ('icOutcome').
icEvalNative :: CompiledExpr -> Either RunTimeError CompiledExpr
icEvalNative = icOutcome . fst . icRunNative mempty defaultFuel

ctlSp, ctlFuel, ctlErr, ctlWhy :: Int
ctlSp = 0
ctlFuel = 4
ctlErr = 5
ctlWhy = 7

agentWords :: Int
agentWords = 8

-- | A port's word in the entry net: agent 0 is never used, so node n is n + 1.
entryPort :: Port -> Word32
entryPort (Port n s) = fromIntegral ((n + 1) * 4 + s)

-- | One run: the agents and the store are copied, since the run writes both, and
-- the input goes in.
runPrepared :: Prepared -> Int -> Maybe BasicExpr -> IO (Either ICError CompiledExpr, Int)
runPrepared p fuel input = do
  let inputWords = maybe (0, []) (dataWords (fromIntegral (prLen p))) input
      total = prLen p + length (snd inputWords)
      cap = until (>= 2 * max (prCount p) (prMemLen p `div` agentWords) + 2) (* 2) 8192
  storeP <- mallocArray total :: IO (Ptr Word32)
  withForeignPtr (prStore p) $ \s -> copyArray storeP s (prLen p)
  pokeArray (advancePtr storeP (prLen p)) (snd inputWords)
  mem <- callocBytes (cap * agentWords * 4) :: IO (Ptr Word32)
  withForeignPtr (prMem p) $ \m -> copyArray mem m (prMemLen p)
  forM_ (prHole p) $ \hole -> do
    let at = (hole + 1) * agentWords
    case fst inputWords of
      0 -> pure ()
      w -> do
        pokeElemOff mem at kConst
        pokeElemOff mem (at + 4) w
  msgs <- newIORef IntMap.empty
  r <- allocaArray 8 $ \ctl -> alloca $ \pm -> do
    pokeArray ctl
      [ fromIntegral (prPairs p), fromIntegral (prCount p), 0
      , fromIntegral (icNextLabel (prState p)), fromIntegral fuel, 0
      , fromIntegral cap, 0 ]
    poke pm mem
    stop <- runLoop (prOrigins p) storeP pm ctl msgs
    left <- peekElemOff ctl ctlFuel
    let spent = fuel - fromIntegral left
    out <- case stop of
      Just e -> pure (Left e)
      Nothing -> do
        err <- peekElemOff ctl ctlErr
        why <- peekElemOff ctl ctlWhy
        case err of
          0 -> finish (prRoot p) (prState p) (prOrigins p) storeP pm msgs
          1 -> pure . Left $ ICFuelExhausted spent
          _ -> pure . Left . ICInternal $ whyMessage why
    peek pm >>= free
    pure (out, spent)
  free storeP
  pure r

whyMessage :: Word32 -> String
whyMessage = \case
  1 -> "dupRegion: nothing to pair"
  2 -> "dup-closure: no copies"
  n -> "unknown internal error " <> show n

-- | Fire until the C leaves nothing: what it leaves on top of the stack is a
-- stuck rule, whose message needs Haskell, or a pair with no rule.
runLoop :: IntMap.IntMap AbortOrigin -> Ptr Word32 -> Ptr (Ptr Word32) -> Ptr Word32
        -> IORef (IntMap.IntMap String) -> IO (Maybe ICError)
runLoop origins t pm ctl msgs = do
  c_reduce pm t ctl
  sp <- peekElemOff ctl ctlSp
  err <- peekElemOff ctl ctlErr
  if err /= 0 || sp == 0
    then pure Nothing
    else do
      m <- peek pm
      let top = fromIntegral sp - 1
      a <- peekElemOff m (top * agentWords + 6)
      b <- peekElemOff m (top * agentWords + 7)
      ka <- agentWord m a 0
      kb <- agentWord m b 0
      case (isConsumer ka, isConsumer kb) of
        (True, False) -> fireStuck a ka b kb sp >> runLoop origins t pm ctl msgs
        (False, True) -> fireStuck b kb a ka sp >> runLoop origins t pm ctl msgs
        _noRule -> do
          sa <- decodeKind origins t msgs m a
          sb <- decodeKind origins t msgs m b
          pure . Just . ICInternal $
            "no interaction rule for " <> show sa <> " meeting " <> show sb
  where
    fireStuck n kn v kv sp = do
      m <- peek pm
      shown <- show <$> decodeKind origins t msgs m v
      r1 <- agentWord m n 1
      r2 <- agentWord m n 2
      let target = "projection target is " <> shown <> ", not a pair"
      (msg, res1, res2, es) <-
        if kn == kSetEnv then pure ("SetEnv operand is " <> shown <> ", not a pair", r1, 0, [])
        else if kn == kApply then do
          shape <- describe origins t msgs m 6 v
          comps <- if kv == kPair
            then traverse (agentWord m v) [1, 2]
            else pure []
          pure ( "applied value is " <> shown <> ", not a function: " <> shape
               , r2, 0, r1 : comps )
        else if kn == kScrut then pure ("gate scrutinee is " <> shown <> ", not data", r1, 0, [])
        else if kn == kSplit then pure (target, r1, r2, [])
        else pure (target, r1, 0, [])
      number <- IntMap.size <$> readIORef msgs
      modifyIORef' msgs (IntMap.insert number msg)
      pokeElemOff ctl ctlSp (sp - 1)
      let e i = case drop i es of
            x : _ -> x
            []    -> 0
      c_stuck pm t ctl n v (fromIntegral number) res1 res2 (e 0) (e 1) (e 2)

isConsumer :: Word32 -> Bool
isConsumer k = k `elem` [kSplit, kSetEnv, kApply, kScrut, kLeft, kRight]

-- | Word i of an agent: 0 its kind, 1 and 2 the peers of its ports 1 and 2, as
-- the C numbers them.
agentWord :: Ptr Word32 -> Word32 -> Int -> IO Word32
agentWord m n i = peekElemOff m (fromIntegral n * agentWords + wordAt)
  where
    wordAt = case i of
      0 -> 0
      _ -> 1 + i

payload :: Ptr Word32 -> Word32 -> Int -> IO Word32
payload m n i = peekElemOff m (fromIntegral n * agentWords + 4 + i)

decodeKind :: IntMap.IntMap AbortOrigin -> Ptr Word32 -> IORef (IntMap.IntMap String)
           -> Ptr Word32 -> Word32 -> IO ICKind
decodeKind origins t msgs m n = do
  k <- agentWord m n 0
  a <- payload m n 0
  b <- payload m n 1
  if k == kRoot then pure ICRoot
  else if k == kExt then pure ICExt
  else if k == kEra then pure ICEra
  else if k == kZero then pure ICZero
  else if k == kGate then pure ICGate
  else if k == kConst then ICConst <$> constAt t a
  else if k == kRef then pure (ICRef (fromIntegral a) (toEnum (fromIntegral (fromIntegral b :: Int32))))
  else if k == kPair then pure ICPair
  else if k == kAborted then case IntMap.lookup (fromIntegral a) origins of
    Just o  -> pure (ICAborted o)
    Nothing -> ioError (userError "no such abort origin")
  else if k == kDup then pure (ICDup (fromIntegral a))
  else if k == kSplit then pure ICSplit
  else if k == kSetEnv then pure ICSetEnv
  else if k == kApply then pure ICApply
  else if k == kScrut then pure ICScrut
  else if k == kLeft then pure ICLeft
  else if k == kRight then pure ICRight
  else if k == kStuck then do
    ms <- readIORef msgs
    pure (ICStuckV (IntMap.findWithDefault "stuck" (fromIntegral a) ms))
  else ioError (userError ("no such agent kind " <> show k))

-- | Closed data from its word in the store.
constAt :: Ptr Word32 -> Word32 -> IO BasicExpr
constAt t w
  | w == 0 = pure ZeroB
  | otherwise = do
      a <- peekElemOff t (fromIntegral w) >>= constAt t
      b <- peekElemOff t (fromIntegral w + 1) >>= constAt t
      pure (PairB a b)

-- | A bounded sketch of a value, for error messages ('describeValue').
describe :: IntMap.IntMap AbortOrigin -> Ptr Word32 -> IORef (IntMap.IntMap String)
         -> Ptr Word32 -> Int -> Word32 -> IO String
describe origins t msgs m depth n
  | depth <= 0 = pure "..."
  | otherwise = do
      k <- agentWord m n 0
      if k == kZero then pure "0"
      else if k == kPair then do
        a <- agentWord m n 1
        b <- agentWord m n 2
        sa <- describe origins t msgs m (depth - 1) (node a)
        sb <- describe origins t msgs m (depth - 1) (node b)
        pure $ "(" <> sa <> "," <> sb <> ")"
      else if k == kRef then ("ref" <>) . show <$> payload m n 0
      else if k == kDup then do
        l <- payload m n 0
        src <- peekElemOff m (fromIntegral n * agentWords + 1)
        s <- describe origins t msgs m (depth - 1) (node src)
        pure $ "dup" <> show l <> "[" <> s <> "]"
      else show <$> decodeKind origins t msgs m n
  where node p = p `shiftR` 2

-- | Read the finished net back: what is reachable from the root becomes
-- 'Telomare.IC''s nodes again, and 'readback' says what it means.
finish :: Int -> ICState -> IntMap.IntMap AbortOrigin -> Ptr Word32 -> Ptr (Ptr Word32)
       -> IORef (IntMap.IntMap String) -> IO (Either ICError CompiledExpr)
finish root st origins t pm msgs = do
  m <- peek pm
  let rootId = fromIntegral root + 1 :: Word32
  start <- peekElemOff m (fromIntegral rootId * agentWords + 1)
  nodes <- reach m IntMap.empty [start `shiftR` 2]
  let port p = Port (fromIntegral (p `shiftR` 2)) (fromIntegral (p .&. 3))
      st' = st { icNodes = nodes, icActive = [] }
      (r, _) = State.runState (runExceptT (readback (port start))) st'
  pure $! r
  where
    reach _ seen [] = pure seen
    reach m seen (n : rest)
      | IntMap.member (fromIntegral n) seen = reach m seen rest
      | otherwise = do
          k <- decodeKind origins t msgs m n
          let portsOf = case k of
                ICPair      -> [1, 2]
                ICAborted _ -> [1]
                _leaf       -> []
          peers <- traverse (\s -> (,) s <$> agentWord m n s) portsOf
          let ports = IntMap.fromList
                [ (s, Port (fromIntegral (p `shiftR` 2)) (fromIntegral (p .&. 3)))
                | (s, p) <- peers ]
              seen' = IntMap.insert (fromIntegral n) (Node k ports) seen
          reach m seen' (fmap ((`shiftR` 2) . snd) peers <> rest)
