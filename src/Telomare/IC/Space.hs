{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE MultiWayIf      #-}
{-# LANGUAGE PatternSynonyms #-}

-- | How much the interaction-net runtime ('Telomare.IC') can hold, worked
-- out before the program runs: the most storage one iteration's net
-- reaches, over every input it can be given.
--
-- The runtime keeps an iteration's input whole, as one 'ICData' node, and
-- takes it apart one layer at a time, only when a consumer needs its shape
-- ('Telomare.IC.revealData'). So what a run does depends on the input only
-- through the shapes the program actually looks at. This module runs the
-- runtime's own net with an input whose shape is unknown: the unknown part
-- is an 'ICData' node holding a /path/ instead of a value ('DataPart'),
-- every pair fires by the runtime's own code, in the runtime's own order
-- (it schedules through 'Telomare.IC.nextPair'), and when a consumer needs
-- the shape of an input part nobody has looked at yet, the walk splits in
-- two: one copy goes on as if that part is Zero, the other as if it is a
-- pair. A copy of the walk is a /world/: a set of input shapes, all of
-- which the runtime runs identically, interaction for interaction.
--
-- Two scopes ('SpaceScope'):
--
-- * 'EveryInput': one iteration on any data at all.
-- * 'Sessions': every iteration of every session the driver can run. The
--   first iteration's input is Zero; every later one is a pair of what the
--   user typed (unknown: any data) and the state the previous iteration
--   returned (known). The walk starts from the first iteration, reads the
--   next state back from every world that finishes, and walks each new
--   state in turn, until no new state turns up. Only reachable states are
--   walked, and all of them are.
--
-- Worlds rejoin: at some of the moments the runtime is about to fire a
-- parked instantiation (no eager work left), a world takes a fingerprint
-- of its whole net, up to renaming of nodes and labels, together with what
-- it has committed to about every input part the net still holds. A world
-- that reaches a net some world already reached, having done at least as
-- many interactions, stops: from there on the two run identically (the
-- runtime is a function of the net), so the other world's run already
-- covers its future, and its own past is recorded where it stops. Which
-- moments qualify depends only on the net's own counters, so two worlds in
-- the same net take a fingerprint at the same moment.
--
-- That keeps the figures exact, not just limits: every figure is the peak
-- of some world's real run, and every input's run is covered. The walk
-- runs worlds in parallel, on every core GHC is given.
--
-- The walk has an explicit budget of interactions, worlds and states;
-- running out of any of them gives 'SpaceUnknown', never a partial figure.
module Telomare.IC.Space
  ( SpaceBudget (..)
  , defaultSpaceBudget
  , SpaceScope (..)
  , Peak (..)
  , SpaceCertificate (..)
  , SpaceOutcome (..)
  , certifySpace
  , certificateCovers
  , renderSpace
  , renderData
  ) where

import Control.Concurrent (forkIO, getNumCapabilities)
import Control.Concurrent.MVar (modifyMVar, modifyMVar_, newEmptyMVar, newMVar,
                                putMVar, takeMVar, tryPutMVar)
import Control.Exception (SomeException, evaluate, try)
import Control.Monad (forM_, replicateM, void, when)
import Control.Monad.Except (catchError, runExceptT)
import qualified Control.Monad.State.Strict as State
import Crypto.Hash (Digest, SHA256, hashlazy)
import qualified Data.ByteString.Builder as B
import Data.Either (lefts, rights)
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef)
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import Telomare.EAL (CapShape)
import Telomare.IC
import Telomare.IR.Base (BasicExpr, pattern PairB, pattern ZeroB)
import Telomare.IR.Core (CompiledExpr)

-- | How much walking to do before giving up.
data SpaceBudget = SpaceBudget
  { budgetInteractions :: !Int
    -- ^ interactions over all worlds together
  , budgetWorlds       :: !Int
    -- ^ worlds over all iterations
  , budgetStates       :: !Int
    -- ^ distinct states a session can carry ('Sessions' only)
  , budgetCheckEvery   :: !Int
    -- ^ how rarely a world fingerprints its net to rejoin another: at the
    -- parked pairs where its counters hash to 0 modulo this; 0 never
  } deriving (Eq, Show)

defaultSpaceBudget :: SpaceBudget
defaultSpaceBudget = SpaceBudget 4000000000 4000000 100000 2048

-- | Which inputs the walk covers.
data SpaceScope
  = EveryInput  -- ^ one iteration, any data as its input
  | Sessions    -- ^ every iteration of every session the driver can run
  deriving (Eq, Show)

-- | The largest figure some input reaches, and one input that reaches it.
data Peak = Peak
  { peakValue :: !Int
  , peakInput :: BasicExpr
  } deriving (Eq, Show)

-- | What the walk established. Each storage component has its own worst
-- input; they need not be the same input.
data SpaceCertificate = SpaceCertificate
  { certAgents       :: Peak
  , certPorts        :: Peak
  , certWork         :: Peak
  , certTemplates    :: Resources
    -- ^ the template table: the same on every iteration and every input
  , certWorlds       :: !Int
    -- ^ input shapes the program tells apart (worlds walked)
  , certErrorWorlds  :: !Int
    -- ^ of those, how many end in a runtime error before finishing
  , certInteractions :: !Int
    -- ^ interactions the walk performed over all worlds
  , certStates       :: !Int
    -- ^ states a session can carry, walked ('Sessions'); 0 for 'EveryInput'
  , certMerged       :: !Int
    -- ^ worlds that stopped because another world had reached their net
  } deriving (Eq, Show)

data SpaceOutcome
  = SpaceBound SpaceCertificate
  | SpaceUnknown String Int Int
    -- ^ why, worlds finished, interactions performed
  deriving (Eq, Show)

-- | What a world's iteration gets as its input.
data Input
  = FirstTurn          -- ^ Zero: a session's first iteration
  | Turn BasicExpr     -- ^ (anything, this state): path 0 is the pair, path
                       --   1 what the user typed, the state is known
  | AnyData            -- ^ anything at all, from path 0

-- | A copy of the walk, and the input shapes it has committed to, by path:
-- True for a pair.
data World = World
  { worldNet    :: ICState
  , worldRoot   :: !Int
  , worldInput  :: Input
  , worldShapes :: Map Integer Bool
  , worldResume :: !Bool
    -- ^ stopped for a fingerprint at the pair it would fire next: do not
    -- stop there again
  }

-- | Why a world stopped advancing.
data Stop = Finished | Failed | NeedShape Integer | OutOfInteractions
          | Checkpoint

-- | Work out, before running, the most storage an iteration of @main@
-- reaches on the net, under the guidance a session runs with
-- ('Telomare.Eval.IC.icPlanLayouts').
certifySpace :: SpaceBudget -> SpaceScope -> Map (Digest SHA256) CapShape
             -> CompiledExpr -> IO SpaceOutcome
certifySpace budget scope guidance mainTerm =
  case (build ICZero, build (ICData (DataPart 0))) of
    (Left err, _) -> pure $ unbuilt err
    (_, Left err) -> pure $ unbuilt err
    (Right zeroNet, Right partNet) -> do
      let world input (root, st) shapes = World st root input shapes False
          firstTurn = world FirstTurn zeroNet Map.empty
          turn s = world (Turn s) partNet (Map.singleton 0 True)
      table <- newIORef Map.empty
      case scope of
        EveryInput -> do
          r <- walkPool budget table 0
                 [firstTurn, world AnyData partNet (Map.singleton 0 True)]
          pure $ either id (\(acc, _) -> SpaceBound (finish 0 acc)) r
        Sessions -> sessions table turn [firstTurn] Map.empty emptyAcc
  where
    build kind = case runNet (buildApplied mainTerm kind)
                              (emptyState guidance defaultFuel) of
      (Left err, _)    -> Left err
      (Right root, st) -> Right (root, st)
    unbuilt err = SpaceUnknown ("the net could not be built: " <> show err) 0 0

    -- breadth first over the states a session can carry
    sessions table turn worlds seen acc0 = do
      r <- walkPool budget { budgetInteractions =
                               budgetInteractions budget - accInteractions acc0
                           , budgetWorlds = budgetWorlds budget - accWorlds acc0 }
                    table (accInteractions acc0) worlds
      case r of
        Left unknown -> pure (bump acc0 unknown)
        Right (acc, next) -> do
          let acc' = acc0 <> acc
              fresh = Map.difference next seen
              seen' = Map.union seen fresh
          if | Map.size seen' > budgetStates budget ->
                 pure $ SpaceUnknown
                   ("the check ran out of its state budget: sessions can carry more "
                      <> "than " <> commas (budgetStates budget) <> " states")
                   (accWorlds acc') (accInteractions acc')
             | Map.null fresh -> pure . SpaceBound $ finish (Map.size seen') acc'
             | otherwise -> sessions table turn (turn <$> Map.elems fresh)
                              seen' acc'
    bump acc = \case
      SpaceUnknown why w i -> SpaceUnknown why (accWorlds acc + w) i
      done -> done

    finish states acc = SpaceCertificate
      { certAgents = accAgents acc
      , certPorts = accPorts acc
      , certWork = accWork acc
      , certTemplates = accTemplates acc
      , certWorlds = accWorlds acc
      , certErrorWorlds = accErrors acc
      , certInteractions = accInteractions acc
      , certStates = states
      , certMerged = accMerged acc
      }

runNet :: ICM a -> ICState -> (Either ICError a, ICState)
runNet action = State.runState (runExceptT action)

-- * The parallel walk

-- | Walk the given worlds, and every world they split into, on every core.
-- Returns what the finished worlds reached and, keyed by fingerprint, the
-- states they hand to a next iteration.
walkPool :: SpaceBudget -> IORef (Map (Digest SHA256) Int) -> Int -> [World]
         -> IO (Either SpaceOutcome (Acc, Map (Digest SHA256) BasicExpr))
walkPool budget table spentBefore worlds0 = do
  cores <- getNumCapabilities
  queue <- newMVar (worlds0, 0 :: Int)
  -- poked whenever the queue gains a world or a worker goes idle
  wake <- newEmptyMVar
  spent <- newIORef (0 :: Int)
  started <- newIORef (length worlds0)
  failure <- newIORef (Nothing :: Maybe String)
  dones <- replicateM (max 1 cores) newEmptyMVar
  forM_ dones $ \done -> forkIO $ do
    r <- try (worker queue wake spent started failure emptyWalked)
    -- whoever leaves wakes the next, so every idle worker sees the end
    _ <- tryPutMVar wake ()
    putMVar done (r :: Either SomeException Walked)
  results <- mapM takeMVar dones
  stopped <- readIORef failure
  total <- readIORef spent
  let crashed = show <$> lefts results
      walked = mconcat (rights results)
  pure $ case (crashed, stopped) of
    (e : _, _) -> Left $ SpaceUnknown ("internal error in the walk: " <> e)
                    (accWorlds (wAcc walked)) (spentBefore + total)
    ([], Just why) -> Left $ SpaceUnknown why (accWorlds (wAcc walked))
                        (spentBefore + total)
    ([], Nothing) -> Right ((wAcc walked) { accInteractions = total }, wNext walked)
  where
    chunk = 1000000

    worker queue wake spent started failure walked = do
      next <- modifyMVar queue $ \(ws, busy) -> pure $ case ws of
        w : rest -> ((rest, busy + 1), Right (w, not (null rest)))
        []       -> ((ws, busy), Left (busy == 0))
      case next of
        Right (w, more) -> do
          when more . void $ tryPutMVar wake ()
          walked' <- runWorld queue wake spent started failure w walked
          modifyMVar_ queue $ \(ws, busy) -> pure (ws, busy - 1)
          _ <- tryPutMVar wake ()
          worker queue wake spent started failure walked'
        Left True -> pure walked
        Left False -> takeMVar wake >> worker queue wake spent started failure walked

    stop failure why = atomicModifyIORef' failure $ \case
      Nothing -> (Just why, ())
      already -> (already, ())

    runWorld queue wake spent started failure w walked =
      readIORef failure >>= \case
        Just _ -> pure walked
        Nothing -> do
          let (r, st) = runNet (drive (budgetCheckEvery budget) w chunk)
                               (worldNet w)
          outcome <- evaluate (r `seq` IntMap.size (icNodes st) `seq` r)
          let used = either (const 0) snd outcome
          total <- atomicModifyIORef' spent $ \n -> (n + used, n + used)
          let continue w' = runWorld queue wake spent started failure w' walked
          if total > budgetInteractions budget
            then do
              stop failure ("the check ran out of its interaction budget before it "
                              <> "covered every input shape")
              pure walked
            else case outcome of
              Left err -> do
                stop failure ("internal error in the walk: " <> show err)
                pure walked
              Right (Failed, _) -> pure $! recordWorld True w st Nothing walked
              Right (Finished, _) -> case nextState w st of
                Left why   -> stop failure why >> pure walked
                Right next -> pure $! recordWorld False w st next walked
              Right (OutOfInteractions, _) -> continue w { worldNet = st, worldResume = False }
              Right (Checkpoint, _) -> do
                let key = fingerprint w st
                    mine = icSpent st
                merge <- evaluate key >>= \k -> atomicModifyIORef' table $ \t ->
                  case Map.lookup k t of
                    Just theirs | theirs <= mine -> (t, True)
                    _otherwise                   -> (Map.insert k mine t, False)
                if merge
                  then pure $! recordMerged w st walked
                  else continue w { worldNet = st, worldResume = True }
              Right (NeedShape path, _) -> do
                n <- atomicModifyIORef' started $ \k -> (k + 1, k + 1)
                if n > budgetWorlds budget
                  then do
                    stop failure ("the check ran out of its world budget before it "
                                    <> "covered every input shape")
                    pure walked
                  else do
                    let child isPair = w { worldNet = st, worldResume = False
                                         , worldShapes = Map.insert path isPair (worldShapes w) }
                    modifyMVar_ queue $ \(ws, busy) -> pure (child True : ws, busy)
                    _ <- tryPutMVar wake ()
                    continue (child False)

-- | Fire pairs in the runtime's order until the net is done, the budget is
-- spent, a consumer needs the shape of an input part this world has not
-- committed to, or the world should fingerprint its net. A pair is only
-- taken off its queue once it can fire, so a world that stops resumes at
-- the same pair. Returns how many pairs fired.
drive :: Int -> World -> Int -> ICM (Stop, Int)
drive every w limit = go 0 (worldResume w)
  where
    shapes = worldShapes w
    -- one pair at a time, each under its own handler: a rule that fails
    -- ends the world where the runtime's run would end
    go k skip
      | k >= limit = pure (OutOfInteractions, k)
      | otherwise = ((Right <$> step skip) `catchError` (pure . Left)) >>= \case
          Left _err        -> pure (Failed, k)
          Right (Just why) -> pure (why, k)
          Right Nothing    -> go (k + 1) False
    step skip = nextPair >>= \case
      Nothing -> pure (Just Finished)
      Just next@(Parked _ _)
        | not skip, every > 0 -> State.gets icResident >>= \r ->
            if checkpoint every r
              then pure (Just Checkpoint)
              else fireIt next
      Just next -> demanded next >>= \case
        Just (n, path) -> case Map.lookup path shapes of
          Nothing -> pure (Just (NeedShape path))
          Just isPair -> do
            popNext next
            -- exactly what 'fire' does with a known value of this shape
            revealData n $ if isPair then Just (partsOf (worldInput w) path)
                                     else Nothing
            fireNext next
            pure Nothing
        Nothing -> fireIt next
    fireIt next = popNext next >> fireNext next >> pure Nothing
    -- parked pairs are applications meeting code: never data
    demanded = \case
      Eager a b -> demandedData a b >>= \case
        Just (n, DataPart path) -> pure (Just (n, path))
        _known -> pure Nothing
      Parked _ _ -> pure Nothing

-- | The parts of the input part at a path, once it is known to be a pair.
partsOf :: Input -> Integer -> (DataSrc, DataSrc)
partsOf input path = case input of
  Turn s | path == 0 -> (DataPart 1, DataKnown s)
  _other             -> (DataPart (2 * path + 1), DataPart (2 * path + 2))

-- | Whether a world at a parked pair, holding this much, fingerprints its
-- net. A function of the counters alone, so two worlds in the same net
-- agree. A fingerprint costs as much as the net is big, so a bigger net
-- takes one more rarely: about one parked pair in @every@ per thousand
-- agents, which keeps fingerprinting a fixed share of the walk.
checkpoint :: Int -> Resources -> Bool
checkpoint every (Resources a p w) =
  (a * 1000003 + p * 7919 + w) `mod` (every * (1 + a `div` 1024)) == 0

-- * Fingerprints

-- | The world's net up to renaming of nodes and dup labels: every node, by
-- kind, and every wire, numbered in the order a walk from the root and the
-- parked queue meets them; the parked queue; and, for every input part the
-- net still holds, what the world has committed to about it.
fingerprint :: World -> ICState -> Digest SHA256
fingerprint w st = hashlazy (B.toLazyByteString (header <> body))
  where
    nodes = icNodes st
    parked = toList (icParked st)
    roots = worldRoot w : concat [ [a, b] | (a, b) <- parked ]
    order = discover roots
    canon = IntMap.fromList (zip order [0 :: Int ..])
    -- nodes no walk reaches, in id order: rare, and only ever a reason
    -- not to rejoin
    stray = [ n | n <- IntMap.keys nodes, not (IntMap.member n canon) ]
    allNodes = order <> stray
    canonAll = IntMap.fromList (zip allNodes [0 :: Int ..])
    labels = foldl' (\m l -> if Map.member l m then m else Map.insert l (Map.size m) m)
               Map.empty [ l | n <- allNodes, Just (Node (ICDup l) _) <- [IntMap.lookup n nodes] ]
    header = B.int64LE (fromIntegral (length allNodes))
      <> B.int64LE (fromIntegral (length (icActive st)))
      <> foldMap (\(a, b) -> ref a <> ref b) parked
      <> B.word8 255
      <> case worldInput w of
           Turn s -> B.word8 1 <> datum s
           _other -> B.word8 0
    ref n = maybe (B.int64LE (-1)) (B.int64LE . fromIntegral) (IntMap.lookup n canonAll)
    body = foldMap node allNodes
    node n = case IntMap.lookup n nodes of
      Nothing -> B.word8 0
      Just (Node k ports) -> kind k <> B.int64LE (fromIntegral (IntMap.size ports))
        <> foldMap (\(s, Port m s') -> B.int64LE (fromIntegral s) <> ref m
                                         <> B.int64LE (fromIntegral s'))
             (IntMap.toList ports)
    kind = \case
      ICDup l -> B.word8 1 <> B.int64LE (fromIntegral (Map.findWithDefault (-1) l labels))
      ICData (DataKnown e) -> B.word8 2 <> datum e
      ICData (DataPart p) -> B.word8 3 <> B.integerDec p <> B.word8 255
        <> committed (worldShapes w) p
      k -> B.word8 4 <> B.stringUtf8 (show k) <> B.word8 255
    discover = go IntMap.empty [] . Seq.fromList
      where
        go seen acc queue = case Seq.viewl queue of
          Seq.EmptyL -> reverse acc
          n Seq.:< rest
            | IntMap.member n seen -> go seen acc rest
            | otherwise -> case IntMap.lookup n nodes of
                Nothing -> go seen acc rest
                Just (Node _ ports) -> go (IntMap.insert n () seen) (n : acc)
                  (rest Seq.>< Seq.fromList [ m | Port m _ <- IntMap.elems ports ])

-- | A data value, cell by cell.
datum :: BasicExpr -> B.Builder
datum = \case
  PairB a b -> B.word8 1 <> datum a <> datum b
  _zero     -> B.word8 0

-- | What a world has committed to about the input part at a path.
committed :: Map Integer Bool -> Integer -> B.Builder
committed shapes = go
  where
    go p = case Map.lookup p shapes of
      Nothing    -> B.word8 2
      Just False -> B.word8 0
      Just True  -> B.word8 1 <> go (2 * p + 1) <> go (2 * p + 2)

-- * Next states

-- | The state a finished world hands to the next iteration: Nothing if the
-- session ends there (an error, an abort anywhere in the result, or state
-- Zero). The state must be the same for every input in the world; if it
-- carries an input part nothing looked at, the states cannot be listed.
nextState :: World -> ICState -> Either String (Maybe (Digest SHA256, BasicExpr))
nextState w st = case worldInput w of
  AnyData -> Right Nothing
  _turn -> case (result ZeroB, result (PairB ZeroB ZeroB)) of
    (Right a, Right b) -> case (stateOf a, stateOf b) of
      (Just sa, Just sb)
        | B.toLazyByteString (datum sa) /= B.toLazyByteString (datum sb) -> Left
            "a session's state carries part of what the user typed that the program \
            \never looked at, so the states it can carry cannot be listed"
      (Just ZeroB, _) -> Right Nothing
      (Just s, _) -> Right (Just (hashlazy (B.toLazyByteString (datum s)), s))
      _noState -> Right Nothing
    _ended -> Right Nothing
  where
    result fill = icOutcome . fst $ runNet
      (State.modify' (\s -> s { icNodes = IntMap.map (known fill) (icNodes s) })
         >> (readback =<< peer (Port (worldRoot w) 0)))
      st
    known fill nd = case nodeKind nd of
      ICData (DataPart p) -> nd { nodeKind = ICData (DataKnown (valueAt fill p)) }
      _other              -> nd
    valueAt fill p = case worldInput w of
      Turn s | p == 0 -> PairB (valueAt fill 1) s
      _other -> case Map.lookup p (worldShapes w) of
        Just True  -> PairB (valueAt fill (2 * p + 1)) (valueAt fill (2 * p + 2))
        Just False -> ZeroB
        Nothing    -> fill
    stateOf :: CompiledExpr -> Maybe BasicExpr
    stateOf = \case
      PairB _ s -> asData s
      _notPair  -> Nothing
    asData :: CompiledExpr -> Maybe BasicExpr
    asData = \case
      ZeroB     -> Just ZeroB
      PairB a b -> PairB <$> asData a <*> asData b
      _code     -> Nothing

-- * Accumulating worlds

data Acc = Acc
  { accAgents       :: !Peak
  , accPorts        :: !Peak
  , accWork         :: !Peak
  , accTemplates    :: !Resources
  , accWorlds       :: !Int
  , accErrors       :: !Int
  , accInteractions :: !Int
  , accMerged       :: !Int
  }

instance Semigroup Acc where
  a <> b = Acc
    { accAgents = higher (accAgents a) (accAgents b)
    , accPorts = higher (accPorts a) (accPorts b)
    , accWork = higher (accWork a) (accWork b)
    , accTemplates = maxResources (accTemplates a) (accTemplates b)
    , accWorlds = accWorlds a + accWorlds b
    , accErrors = accErrors a + accErrors b
    , accInteractions = accInteractions a + accInteractions b
    , accMerged = accMerged a + accMerged b
    }
    where higher x y = if peakValue y > peakValue x then y else x

instance Monoid Acc where
  mempty = emptyAcc

emptyAcc :: Acc
emptyAcc = Acc none none none noResources 0 0 0 0
  where none = Peak (-1) ZeroB

-- | What one worker walked: its worlds, and the states they hand on.
data Walked = Walked
  { wAcc  :: !Acc
  , wNext :: !(Map (Digest SHA256) BasicExpr)
  }

instance Semigroup Walked where
  Walked a n <> Walked b m = Walked (a <> b) (Map.union n m)

instance Monoid Walked where
  mempty = emptyWalked

emptyWalked :: Walked
emptyWalked = Walked emptyAcc Map.empty

recordWorld :: Bool -> World -> ICState -> Maybe (Digest SHA256, BasicExpr)
            -> Walked -> Walked
recordWorld failed w st next (Walked acc nexts) = Walked
  (acc <> (peaksOf w st)
     { accWorlds = 1, accErrors = if failed then 1 else 0 })
  (maybe nexts (\(k, s) -> Map.insert k s nexts) next)

recordMerged :: World -> ICState -> Walked -> Walked
recordMerged w st (Walked acc nexts) =
  Walked (acc <> (peaksOf w st) { accWorlds = 1, accMerged = 1 }) nexts

-- | A world's own peaks so far, with the input it stands for.
peaksOf :: World -> ICState -> Acc
peaksOf w st = emptyAcc
  { accAgents = Peak (resAgents peak) input
  , accPorts = Peak (resPorts peak) input
  , accWork = Peak (resWork peak) input
  , accTemplates = templateStorage st
  }
  where
    peak = icPeak st
    input = witness w

-- | The input a world stands for, with Zero wherever nothing looked.
witness :: World -> BasicExpr
witness w = case worldInput w of
  FirstTurn -> ZeroB
  Turn s    -> PairB (go 1) s
  AnyData   -> go 0
  where
    go :: Integer -> BasicExpr
    go path
      | Map.lookup path (worldShapes w) == Just True =
          PairB (go (2 * path + 1)) (go (2 * path + 2))
      | otherwise = ZeroB

-- | Whether a measured run stays within the certificate. Unknown never
-- does.
certificateCovers :: Resources -> SpaceOutcome -> Bool
certificateCovers measured = \case
  SpaceBound c -> resAgents measured <= peakValue (certAgents c)
    && resPorts measured <= peakValue (certPorts c)
    && resWork measured <= peakValue (certWork c)
  SpaceUnknown {} -> False

-- * Rendering

-- | An input the way a reader writes it: @input 0@, @input (0,(0,0))@; a
-- large one by its size.
renderData :: BasicExpr -> String
renderData e
  | length shown <= 60 = "input " <> shown
  | otherwise = "an input of " <> show (cells e) <> " cells"
  where
    shown = go e
    go :: BasicExpr -> String
    go = \case
      PairB a b -> "(" <> go a <> "," <> go b <> ")"
      _zero     -> "0"
    cells :: BasicExpr -> Int
    cells = \case
      PairB a b -> 1 + cells a + cells b
      _zero     -> 1

renderSpace :: SpaceOutcome -> String
renderSpace = \case
  SpaceBound c -> unlines $
    [ "IC storage certificate", "" ]
    <> para (if certStates c > 0 || certWorlds c == 1
               then "Run this program on the interaction-net runtime (--ic), and on every "
                      <> "iteration of every session, whatever the user types, the net "
                      <> "holds at most:"
               else "Run this program on the interaction-net runtime (--ic), and on every "
                      <> "iteration, whatever its input, the net holds at most:")
    <> [ ""
       , row "agents" (certAgents c)
       , row "port entries" (certPorts c)
       , row "pending pairs" (certWork c)
       , "" ]
    <> para ("These are exact worst cases, not estimates: some input reaches each "
             <> "figure, and the input shown is one that does. The check ran the "
             <> "runtime's own net for every way the program can take its input apart ("
             <> plural (certWorlds c) "input shape"
             <> (if certStates c > 0
                   then " over " <> plural (certStates c) "session state"
                          <> " reachable from the first iteration"
                   else "")
             <> ", " <> commas (certInteractions c) <> " interactions in all)."
             <> (if certMerged c > 0
                   then " " <> plural (certMerged c) "input shape"
                          <> " reached a net another one had already reached, and "
                          <> "stopped there: from that net on, the two run identically."
                   else "")
             <> (if certErrorWorlds c > 0
                   then " " <> plural (certErrorWorlds c) "input shape"
                          <> " end the run in a runtime error; the figures cover "
                          <> "them up to the error."
                   else ""))
    <> [""]
    <> para ("Agents are the nodes in the net, port entries the wire ends it stores, "
             <> "and pending pairs the interactions waiting to fire.")
    <> [""]
    <> para ("Not counted: the input itself, which the net holds whole until the "
             <> "program takes it apart; the template table (code, and constants counted "
             <> "cell by cell), the same on every iteration ("
             <> commas (resAgents (certTemplates c)) <> " agents, "
             <> commas (resPorts (certTemplates c)) <> " port entries); reading back "
             <> "the result; and the Haskell runtime's own memory (GC, the process).")
  SpaceUnknown why worlds interactions -> unlines $
    [ "IC storage certificate", "" ]
    <> para ("No limit could be worked out: " <> why <> ".")
    <> [""]
    <> para ("The check runs the net once for every way the program can take its "
             <> "input apart. It covered " <> plural worlds "input shape" <> " in "
             <> commas interactions <> " interactions and did not finish, so it "
             <> "claims nothing.")
  where
    row name pk = "    " <> pad 15 name <> pad 12 (commas (peakValue pk))
      <> "reached by " <> renderData (peakInput pk)
    pad n str = str <> replicate (n - length str) ' '
    plural n what = commas n <> " " <> what <> (if n == 1 then "" else "s")

-- | A paragraph, indented two spaces and wrapped at 76 columns.
para :: String -> [String]
para = fmap ("  " <>) . go [] 0 . words
  where
    width = 74
    go line _ [] = [unwords (reverse line) | not (null line)]
    go [] _ (w : ws) = go [w] (length w) ws
    go line n (w : ws)
      | n + 1 + length w > width = unwords (reverse line) : go [w] (length w) ws
      | otherwise = go (w : line) (n + 1 + length w) ws

-- | 1234567 as 1,234,567.
commas :: Int -> String
commas n
  | n < 0 = '-' : commas (negate n)
  | otherwise = reverse . go . reverse $ show n
  where
    go (a : b : c : rest@(_ : _)) = a : b : c : ',' : go rest
    go xs                         = xs
