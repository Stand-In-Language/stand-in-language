{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

-- |The sizing pass: telomare's totality checker. 'sizeTermM' abstractly
-- interprets the program over a symbolic input ('initialInput', bounded by
-- the refinement-derived 'InputRestrictions' from 'getInputLimits') and
-- infers, per unsized recursion site, an iteration count that holds for
-- every input - then bakes those counts into the term as church towers.
-- A program that cannot be sized does not compile ('SizingFailure').
module Telomare.Size where

import Control.Applicative
import qualified Control.Comonad.Trans.Cofree as CofreeT (CofreeF (..))
import Data.Either (isLeft, rights)
import Data.Foldable
import Data.Functor.Foldable
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (isNothing)
-- import Data.SBV ((.<), (.>))
import Control.Exception (Exception)
import Control.Exception.Base (throw)
import Control.Monad (when)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import qualified Control.Monad.State.Strict as State
import Data.Functor.Identity (Identity, runIdentity)
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace
import Telomare.Error
import Telomare.IR.Base
import Telomare.IR.Core
import Telomare.IR.Loc
import Telomare.Machine hiding (debug, debugTrace)
import Telomare.PrettyPrint
import Telomare.Size.IR

debug :: Bool
debug = False

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

data SizingSettings = SizingSettings
  { maxSizingSize :: Int
  , doCap         :: Bool
  } deriving (Eq, Ord, Show)

data InputRestrictions
  = InputRestrictions {zeroes :: Set Integer, pairs :: Set Integer}
  deriving Show

instance Semigroup InputRestrictions where
  (<>) (InputRestrictions za pa) (InputRestrictions zb pb) = InputRestrictions (za <> zb) (pa <> pb)
instance Monoid InputRestrictions where
  mempty = InputRestrictions mempty mempty

extractInputRestrictions :: InputSizingExpr -> InputRestrictions
extractInputRestrictions = cleanup . f Nothing where
  f expected = f' expected . project
  irIntersection (InputRestrictions za pa) (InputRestrictions zb pb) = InputRestrictions (za <> zb) (pa <> pb)
  f' :: Maybe Bool -> InputSizingExprF InputSizingExpr -> Maybe (StrictAccum InputRestrictions InputSizingExpr)
  f' expected = \case
    z@(BasicFW ZeroSF) -> case expected of
      Just True -> Nothing
      _         -> pure . pure $ embed z
    p@(BasicFW (PairSF _ _)) -> case expected of
      Just False -> Nothing
      _          -> pure . pure $ embed p
    IndexedFW (IVarF n) -> case expected of
      Just False -> Just (StrictAccum (InputRestrictions (Set.singleton n) mempty) ZeroB)
      Just True  -> Just (StrictAccum (InputRestrictions mempty (Set.singleton n)) $ PairB ZeroB ZeroB)
      _          -> Just (StrictAccum mempty ZeroB) -- is this ok?
    -- a function value is neither impossible nor restricting
    d@(StuckFW (DeferSF _ _)) | isNothing expected -> pure . pure $ embed d
    GateSwitch l r s ->
      let nl = f expected l
          nr = f expected r
      in case (nl, nr) of
        (Nothing, Nothing) -> debugTrace "extractZeroes gate nothing" Nothing
        (Just (StrictAccum sta x), Just (StrictAccum stb _)) -> debugTrace "extractZeroes gate both" $ case f Nothing s of
          Nothing -> Nothing
          Just (StrictAccum st _) -> pure $ StrictAccum (st <> irIntersection sta stb) x
        (Just (StrictAccum sta x), _) -> case f (Just False) s of
          Nothing                  -> Nothing
          Just (StrictAccum stb _) -> pure $ StrictAccum (sta <> stb) x
        (_, Just (StrictAccum sta x)) -> case f (Just True) s of
          Nothing                  -> Nothing
          Just (StrictAccum stb _) -> pure $ StrictAccum (sta <> stb) x
    -- an abort never yields a value, so a gate path ending in one is ruled
    -- out: a refinement check @if r then c else abort (1, c)@ restricts @r@ to
    -- a pair
    AbortFW _ -> Nothing
    _ -> Nothing
  cleanup = \case
    Just (StrictAccum s _) -> s
    _ -> mempty

-- |At each refinement check met during a symbolic run, run its check
-- function over the symbolic values and report the result: a residual
-- over the input, Zero where the check fails. The check's value goes on
-- unchanged.
checkResultStepM :: Monoid w => (AbortOrigin -> InputSizingExpr -> w)
  -> (InputSizingExprF InputSizingExpr -> StrictAccum w InputSizingExpr)
  -> InputSizingExprF InputSizingExpr -> StrictAccum w InputSizingExpr
checkResultStepM report handleOther x = f x where
  f = \case
    UnsizedFW (RefinementWrapperF o tc c) ->
      StrictAccum (report o (transformNoDefer refinementCheckStep $ appB tc c)) c
    _ -> handleOther x

-- |What a check result says about the input: the zeros and pairs it
-- needs in order to pass.
checkRestrictions :: AbortOrigin -> InputSizingExpr -> InputRestrictions
checkRestrictions o r = extractInputRestrictions . cata stripBarrier
  -- only whether the check passes matters here, not the value it guards
  $ refinementGate o r ZeroB
  where
    stripBarrier = \case
      DeferredFW (BarrierF inner) -> inner
      other -> embed other

-- |@if r then c else abort (1, c)@ over an evaluated check result @r@ and value
-- @c@: what a refinement check reduces to once its check function has run.
--
-- An undecided @r@ leaves a barrier-wrapped gate switch with @r@ itself as
-- the scrutinee. Gating on @r@ the usual way would push the gate into
-- @r@'s own residual gates, copying @c@ onto every path that passes, and
-- nested checks would multiply the copies. Left whole, @c@ appears once,
-- and whatever is done to the guarded value later goes into just its two
-- branches, one of which stays an abort.
refinementGate :: AbortOrigin -> InputSizingExpr -> InputSizingExpr -> InputSizingExpr
refinementGate o r c = case r of
  BasicEE ZeroSF       -> aborted
  a@(AbortEE _)        -> a
  BasicEE (PairSF _ _) -> c
  _                    -> deferredEE . BarrierF $ GateSwitchEE aborted c r
  where aborted = refinementCheckStep . AbortFW . AbortF o $ PairB (PairB ZeroB ZeroB) c

-- |Evaluates a refinement check function against symbolic input, leaving
-- input-dependent gates as barrier-wrapped residuals for
-- 'extractInputRestrictions'.
--
-- A refinement nested inside the check (e.g. a check calling a Prelude
-- function whose arguments are refined) is evaluated in place: a decided
-- check reduces to its value or an abort, an undecided one to a gate
-- switch with an abort branch, so its restrictions apply only on the gate
-- paths where the nested check actually runs.
refinementCheckStep :: InputSizingExprF InputSizingExpr -> InputSizingExpr
refinementCheckStep = basicStep (stuckStep (abortStep (gateSwitchStep (sameBranchStep (deferredEvalStep (indexedInputStep Set.empty handleOther)))))) where
  step = refinementCheckStep
  barrier = deferredEE . BarrierF
  -- an undecided gate yields one of its branches, so anything always done to
  -- its result can be done to each branch instead, keeping the result
  -- analyzable (e.g. Bool's @left vv@ when vv is @toBool x@). An abort
  -- branch stays an abort, since aborts propagate.
  gateSwitchStep handleOther' = \case
    StuckFW (LeftSF (DeferredEE (BarrierF (GateSwitchEE l r s)))) ->
      switch (step . StuckFW $ LeftSF l) (step . StuckFW $ LeftSF r) s
    StuckFW (RightSF (DeferredEE (BarrierF (GateSwitchEE l r s)))) ->
      switch (step . StuckFW $ RightSF l) (step . StuckFW $ RightSF r) s
    StuckFW (SetEnvSF (DeferredEE (BarrierF (GateSwitchEE l r s)))) ->
      switch (step . StuckFW $ SetEnvSF l) (step . StuckFW $ SetEnvSF r) s
    FillFunction GateB (DeferredEE (BarrierF (GateSwitchEE l r s))) ->
      switch (step $ FillFunction GateB l) (step $ FillFunction GateB r) s
    FillFunction (DeferredEE (BarrierF (GateSwitchEE l r s))) e ->
      switch (step $ FillFunction l e) (step $ FillFunction r e) s
    other -> handleOther' other
  -- a gate whose branches are the same is that branch, unless its
  -- scrutinee can abort: a nested check that passes whichever way an
  -- input bit goes then reduces to Zero rather than staying a residual
  switch l r s
    | l == r && abortFree s = l
    | otherwise             = barrier $ GateSwitchEE l r s
  abortFree = cata $ \case
    AbortFW _ -> False
    x         -> and x
  sameBranchStep handleOther' = \case
    FillFunction (DeferredEE (BarrierF (FillFunctionEE GateB s))) (PairB l r)
      | l == r && abortFree s -> l
    other -> handleOther' other
  handleOther = \case
    FillFunction GateB i@(IndexedEE _) -> deferredEE . BarrierF . embed $ FillFunction GateB i
    UnsizedFW (RefinementWrapperF o tc c) -> refinementGate o (app tc c) c
    other -> error $ "refinementCheckStep eval unexpected:\n" <> prettyPrint other
  -- 'appB' over already-evaluated operands: tc is a closure, so twiddle it
  -- into (function, (input, env)) before applying
  app tc c = step . StuckFW . SetEnvSF . step $ FillFunction twiddleB (PairB c tc)

term3ToUnsizedExpr :: Term3 -> UnsizedExpr
term3ToUnsizedExpr = runIdentity . cata conv where
  conv :: CofreeT.CofreeF Term3F LocTag (Identity UnsizedExpr) -> Identity UnsizedExpr
  conv = convertBasic (convertStuck (convertAbort convertOther))
  convertOther (_ CofreeT.:< g) = case g of
    Term3Unsized urt -> pure . unsizedEE . UnsizedStubF urt $ EnvB
    Term3CheckingWrapper o tc c -> unsizedEE <$> (RefinementWrapperF o <$> tc <*> c)
    _z -> error "term3ToUnsizedExpr could not convert"

-- get simple input limits derived from refinements
-- returns a set of guaranteed Zeros, where the Integer is the encoded path from root of intput
getInputLimits :: UnsizedExpr -> InputRestrictions
getInputLimits = symbolicChecks checkRestrictions

-- |Run a term over a symbolic input, reporting the result of every
-- refinement check it meets ('checkResultStepM'). A gate on the input
-- itself is not split, but read as an unknown value, as is an unsized
-- recursion.
symbolicChecks :: Monoid w => (AbortOrigin -> InputSizingExpr -> w) -> UnsizedExpr -> w
symbolicChecks report = getAccum . transformNoDeferM evalStep . convertIS where
  convertU = \case
    UnsizedFW (UnsizedStubF _ _) -> pure $ indexedEE AnyF
    UnsizedFW (RecursionTestF _ x) -> x
    UnsizedFW rw@(RefinementWrapperF _ _ _) -> unsizedEE <$> sequence rw
    x -> error $ "symbolicChecks convert, unhandled:\n" <> prettyPrint (runIdentity $ sequence x)
  convertIS :: UnsizedExpr -> InputSizingExpr
  convertIS = runIdentity . cata (convertBasic (convertStuck (convertAbort (convertIndexed convertU))))
  unexpectedI x = error $ "symbolicChecks eval, unexpected:\n" <> prettyPrint x
  evalStep = basicStepM (stuckStepM (abortStepM (indexedInputStepM Set.empty (indexedInputIgnoreSwitchStepM (checkResultStepM report unexpectedI)))))

capMain :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> g -> g
capMain i c = appB c i

newtype UnexpectedGrammarException = UGException String

instance Show UnexpectedGrammarException where
  show (UGException e) = "UnexpectedGrammarException: " <> e

instance Exception UnexpectedGrammarException

initialInput :: (Base a ~ f, BasicBase f, IndexedInputBase f, Recursive a, Corecursive a) => InputRestrictions -> a
initialInput irs = f 0 where
  f n = if any (`decendant` n) $ pairs irs
    then PairB (f $ n * 2 + 1) (f $ n * 2 + 2)
    else indexedEE $ IVarF n

-- |Size every recursion site, returning the iteration counts alongside the
-- compiled term. The counts are the numbers the compiler already relies on to
-- claim the program is total; handing them back costs nothing, and re-running
-- this pass to recover them would cost minutes.
--
-- The failure carries no location — `UnsizedExpr` has none. Callers holding
-- the `Term3` fill it in (see `Telomare.Eval.locateSizingFailure`).
sizeTermM :: SizingSettings -> UnsizedExpr -> Either SizingFailure (SizedRecursion, CompiledExpr)
sizeTermM sizingSettings x = tidyUp . transformNoDeferM evalStep $ mx where
  unlocated tok kind = SizingFailure
    { sizingFailureToken = tok
    , sizingFailureKind = kind
    , sizingFailureLoc = Nothing
    }
  failConvert unhandled = (>>= Left) $ ("sizeTermM convert, unhandled:\n" <>) .  prettyPrint <$> sequence unhandled
  inputRestrictions = (\ir -> debugTrace ("sizeTermM zeros are\n" <> show ir) ir) $ getInputLimits cm'
  zeros = zeroes inputRestrictions
  convertNakedEnvs = \case
    StuckFW EnvSF -> ZeroB
    other -> embed other
  dtt :: UnsizedExpr -> UnsizedExpr
  dtt t = debugTrace ("sizeTermM initial term is\n" <> prettyPrint t) t
  cm' = dtt $ if doCap sizingSettings
    then capMain (indexedEE $ IVarF 0) x
    else x
  cm = removeRefinementWrappers cm'
  mx = removeRefinementWrappers $ if doCap sizingSettings
    then capMain (initialInput inputRestrictions) x
    else transformNoDefer convertNakedEnvs x
  tidyUp (StrictAccum sr@(SizedRecursion sm) r) = debugTrace ("sizes are: " <> show sm <> "\nand result is:\n" <> prettyPrint r) $ case foldAborted r of
    Just (UnsizableSR i) -> debugTrace "sizeTermM hit unsizable" Left $ unlocated i UnboundedInput
    Just (OverfueledSR i) -> debugTrace "sizeTermM ran out of budget" Left
      . unlocated i . FuelExhausted . succ $ maxSizingSize sizingSettings
    _ -> let sized = setSizes sm cm
         in debugTrace "sizeTermM found all sizes" pure . (,) sr . clean $ if doCap sizingSettings
            then uncap sized
            else sized
      where uncap = \case
              AppEE c _ -> c
              z -> error ("sizeTermM tidyUp trying to uncap something that isn't a main function:\n" <> prettyPrint z)
  clean :: UnsizedExpr -> CompiledExpr
  clean = verify . cata (convertBasic (convertStuck (convertAbort failConvert)))
  verify = \case
    Left e -> error e
    Right converted -> converted
  -- only the sizing analysis's own aborts say anything about sizing; the
  -- program's aborts are just one of the outcomes some inputs have
  foldAborted = para f where
    f = \case
      AbortFW (AbortF o (m, _)) | abortKind o == SizingAbort -> case messageData m of
        AbortRecursion i -> case b2i i of
          Just i' -> Just . OverfueledSR $ toEnum i'
          _ -> error $ "sizeTermM foldAborted unexpected AbortRecursion value:\n" <> prettyPrint i
        AbortAny -> error "sizeTermM AbortAny hit"
        -- a path that does not exist, or ends there: no verdict
        AbortStuck -> Nothing
        AbortUnsizeable t -> case b2i t of
          Just i' -> Just . UnsizableSR $ toEnum i'
          _ -> error $ "sizeTermM foldAborted unexpected AbortUnsizeable value:\n" <> prettyPrint t
        other -> error $ "sizeTermM foldAborted unexpected sizing abort:\n" <> prettyPrint other
      other -> Data.Foldable.fold (snd <$> other)
  unhandledGate g = error ("sizeTermM unhandled gate input: " <> show g)
  gateResult = gateBasicResult (gateAbortResult (gateIndexedResult (gateSuperResult gateResult unhandledGate)))
  unsizedTest :: UnsizedRecursionToken -> UnsizedExpr -> UnsizedExpr
  unsizedTest ri = unsizedTestIndexed zeros (unsizedTestSuper (unsizedTest ri) (const id)) ri
  unsizedTest' ri = (\v -> debugTrace ("unsizedTest evaluated to value of\n" <> prettyPrint v) v) . unsizedTest ri
  unhandledError err = throw $ UGException ("sizeTermM unhandled case\n" <> prettyPrint err)
  evalStep = basicStepM (stuckStepM (abortStepM (indexedInputStepM zeros (indexedSuperStepM (superStepM gateResult evalStep (unsizedStepM''' (maxSizingSize sizingSettings) zeros (\ri -> pure . unsizedTest' ri) (`StrictAccum` ()) (stuckSizingStepM unhandledError)))))))

removeRefinementWrappers :: (Base g ~ f, BasicBase f, StuckBase f, AbortBase f, UnsizedBase f, Recursive g, Corecursive g) => g -> g
removeRefinementWrappers = cata f where
  f = \case
    UnsizedFW (RefinementWrapperF o tc c) -> refinementCheckB o tc c
    x -> embed x

-- |One run of a refinement check that may fail, as the exact analysis
-- ('analyzeChecks') saw it.
data CheckFire = CheckFire
  { firePath   :: InputPath
    -- ^ What the run knew of the input when the check ran.
  , fireResult :: UnsizedExpr
    -- ^ The check's abort message there: Zero where it passes, a decision over
    -- input positions where that depends on the input.
  }

-- |What one exact run of a sized main over a symbolic input says about its
-- refinement checks.
data CheckAnalysis = CheckAnalysis
  { checkFires  :: Map AbortOrigin [CheckFire]
    -- ^ Every run of each check that may fail. A check missing here can
    -- never fail.
  , checkResult :: UnsizedExpr
    -- ^ main's result over the symbolic input, with every fired abort's
    -- place in it holding the same aborted value.
  }

-- |Run a sized main once over a symbolic input, through exact
-- superpositions that keep each path apart ('exactSuperStepM'; sized chains
-- make it finite), recording every run of a refinement check that may
-- fail. Nothing when that would take more than the budget of evaluation
-- steps.
--
-- Running every check with every value that can reach it, the run sees
-- where each check fails: a check's abort carries a message that is Zero
-- where it passes and the failing value under a pair where it fails
-- ('refinementCheckB'), so an abort that fires with something other than
-- Zero on some path ('mayBeNonZero') is a check that may fail there.
--
-- The input covers only what the zeros admit. For an answer to hold of
-- every run, an input they rule out must never reach main, or there must
-- be none. What the abstract run cannot follow (data applied as a
-- function, a stuck projection) becomes an unknown value, and a check
-- reaching one may fail. A fired abort is recorded and then forgotten:
-- every aborted value is the same one, so that runs differing only in
-- which check stopped them merge.
analyzeChecks :: Int -> UnsizedExpr -> Set Integer -> CompiledExpr -> Maybe CheckAnalysis
analyzeChecks budget input zeros prog =
  case State.runState (runExceptT (runReaderT run (zeroPath zeros))) (0, Map.empty) of
    (Left (), _)            -> Nothing
    (Right result, (_, fs)) -> Just (CheckAnalysis (reverse <$> fs) result)
  where
  run = transformNoDeferM evalStep . capMain input $ toUnsized prog
  toUnsized :: CompiledExpr -> UnsizedExpr
  toUnsized = runIdentity . cata (convertBasic (convertStuck (convertAbort (error "analyzeChecks: unexpected node"))))
  evalStep :: UnsizedExprF UnsizedExpr
    -> ReaderT InputPath (ExceptT () (State.State (Int, Map AbortOrigin [CheckFire]))) UnsizedExpr
  evalStep = basicStepM (stuckStepM (record (abortStepM (indexedInputStepM zeros
    (exactSuperStepM evalStep unknown)))))
  -- every step that is not plain data or code movement is counted
  record handleOther x = do
    (n, fs) <- State.get
    when (n >= budget) $ throwError ()
    path <- ask
    let fs' = case x of
          AbortFW (AbortF o m) | mayBeNonZero path m -> Map.insertWith (<>) o [CheckFire path m] fs
          _                                          -> fs
    let n' = n + 1
    n' `seq` fs' `seq` State.put (n', fs')
    case x of
      -- once recorded, which check fired no longer matters: an aborted value
      -- only propagates, and one of them for all lets outcomes merge
      AbortFW _ -> pure firedAbort'
      _         -> handleOther x
  unknown _ = pure (indexedEE AnyF)
  firedAbort' = AbortB unknownOrigin ZeroB

-- |The refinement checks of a sized main that may fail on some run
-- ('analyzeChecks').
mayFailChecks :: Int -> UnsizedExpr -> Set Integer -> CompiledExpr -> Maybe (Set AbortOrigin)
mayFailChecks budget input zeros prog = Map.keysSet . checkFires <$> analyzeChecks budget input zeros prog

-- |Whether a check's result is something other than Zero on some path
-- consistent with the given one: its superpositions are walked under what
-- each branch knows, without building anything.
mayBeNonZero :: InputPath -> UnsizedExpr -> Bool
mayBeNonZero path = \case
  ZeroB -> False
  -- an abort in the message is the one that counts ('abortStepM'): the run
  -- was stopped by an earlier abort, recorded where it fired, not this one
  AbortEE _ -> False
  IndexedEE (IVarF v) -> pathDecides path v /= Just True
  SuperEE (EitherPF n l r) -> case n >>= pathDecides path of
    Just True  -> mayBeNonZero path l
    Just False -> mayBeNonZero path r
    Nothing    -> mayBeNonZero (maybe path (\v -> withLiteral True v path) n) l
                  || mayBeNonZero (maybe path (\v -> withLiteral False v path) n) r
  _ -> True

-- |What a value says, on the paths consistent with a given one, of whether
-- a run aborts: an aborted value outside code on every one of them, on
-- none, or on some, with the first undecided superposition in a part that
-- may abort, to tell them apart by.
data AbortStatus = SurelyAborted | AbortFree | MayAbort (Maybe Integer)

-- |One walk of a value for its 'AbortStatus'. Sound but not complete: a
-- pair aborting on every path only because its two sides abort on
-- complementary ones is a 'MayAbort'.
abortStatus :: InputPath -> UnsizedExpr -> AbortStatus
abortStatus path = \case
  AbortEE _ -> SurelyAborted
  PairB a b -> case abortStatus path a of
    SurelyAborted -> SurelyAborted
    sa -> case (sa, abortStatus path b) of
      (_, SurelyAborted)     -> SurelyAborted
      (AbortFree, AbortFree) -> AbortFree
      (MayAbort n, _)        -> MayAbort n
      (_, sb)                -> sb
  SuperEE (EitherPF n a b) -> case n >>= pathDecides path of
    Just True  -> abortStatus path a
    Just False -> abortStatus path b
    Nothing    ->
      case (abortStatus (maybe path (\v -> withLiteral True v path) n) a,
            abortStatus (maybe path (\v -> withLiteral False v path) n) b) of
        (SurelyAborted, SurelyAborted) -> SurelyAborted
        (AbortFree, AbortFree)         -> AbortFree
        (sa, sb)                       -> MayAbort (n <|> tagOf sa <|> tagOf sb)
  _ -> AbortFree
  where
    tagOf = \case
      MayAbort t -> t
      _          -> Nothing

-- |How many times 'runTree' may split a path on main's result before
-- leaving the rest undecided.
demandSplits :: Int
demandSplits = 12

-- |The input positions a run of a check depends on, through the path that
-- reached it or through its result; Nothing when it depends on something
-- the analysis could not follow, or its result is not a decision over the
-- input (an aborted value, code).
fireReads :: CheckFire -> Maybe (Set Integer)
fireReads (CheckFire path r) = ((knownZero path <> knownPair path) <>) <$> reads r where
  reads = \case
    ZeroB                          -> Just mempty
    PairB a b                      -> (<>) <$> reads a <*> reads b
    IndexedEE (IVarF m)            -> Just (Set.singleton m)
    SuperEE (EitherPF (Just n) a b) -> Set.insert n <$> ((<>) <$> reads a <*> reads b)
    _                              -> Nothing

-- |What one run of a check comes to, as a decision over input positions.
data CheckTree
  = Passes
    -- ^ It passes, or its failing is never seen.
  | Fails UnsizedExpr
    -- ^ It fails and the run surely aborts, with this result as the
    -- message, and that is decided before main.
  | Undecided
    -- ^ Main must make it here.
  | Split Integer CheckTree CheckTree
    -- ^ As input position n is Zero or a pair.
  deriving Eq

-- |A 'Split' that does not merely repeat one tree.
split :: Integer -> CheckTree -> CheckTree -> CheckTree
split n a b
  | a == b    = a
  | otherwise = Split n a b

-- |Whether main must make a check somewhere in a tree.
undecidedIn :: CheckTree -> Bool
undecidedIn = \case
  Undecided   -> True
  Split _ a b -> undecidedIn a || undecidedIn b
  _           -> False

-- |One run of a check that depends on the input alone, as a decision: its
-- result's own decisions over the input, down to where it fails, and
-- there what main's result does. A user @if@ or @case@ computes both its
-- branches, so a check in one runs whichever is taken, and the condition
-- under which its abort matters is in main's result: the path is split on
-- the result's own superpositions until it is decided, or the splits run
-- out ('demandSplits').
--
-- Where the run surely aborts, the failure is decided before main, unless
-- it can happen on the input-less first call, which runs without the
-- prologue (the path does not say the input is a pair), or the path has
-- come to depend on the state (main's input is (input, state): the input
-- is under position 1; position 0 says whether there is any). Failing
-- before main then aborts exactly the runs main would have aborted. Where
-- the run aborts in no case, the failure is never seen.
runTree :: UnsizedExpr -> CheckFire -> CheckTree
runTree result (CheckFire path0 r0) = fails path0 r0 where
  fails path = \case
    ZeroB -> Passes
    IndexedEE (IVarF v) -> case pathDecides path v of
      Just True  -> Passes
      Just False -> demand demandSplits path (indexedEE (IVarF v))
      Nothing    -> split v Passes (demand demandSplits (withLiteral False v path) (indexedEE (IVarF v)))
    SuperEE (EitherPF (Just n) a b) -> case pathDecides path n of
      Just True  -> fails path a
      Just False -> fails path b
      Nothing    -> split n (fails (withLiteral True n path) a) (fails (withLiteral False n path) b)
    SuperEE (EitherPF Nothing _ _) -> Undecided
    other -> demand demandSplits path other
  demand :: Int -> InputPath -> UnsizedExpr -> CheckTree
  demand k path msg = case abortStatus path result of
    SurelyAborted
      | all onInput (knownZero path <> knownPair path) && not (Set.null (knownPair path)) -> Fails msg
      | otherwise -> Undecided
    AbortFree -> Passes
    MayAbort (Just n) | k > 0 ->
      split n (demand (k - 1) (withLiteral True n path) msg) (demand (k - 1) (withLiteral False n path) msg)
    MayAbort _ -> Undecided

-- |Whether an input position is in the input, not the state: main's input
-- is (input, state), so under 1, or 0 itself, whether there is any.
onInput :: Integer -> Bool
onInput m = m == 0 || decendant m 1

-- |Where a check that may fail goes.
data CheckVerdict = CheckVerdict
  { hoistedRuns :: [(InputPath, CheckTree)]
    -- ^ How it is decided before main ('inputPrologue'): each run, the
    -- path that reached it and what it comes to there. Empty when main
    -- keeps it.
  , keptInMain  :: Bool
    -- ^ Whether main must still make it, because some failure of it
    -- matters that is not decided before main.
  }

-- |Where each check that may fail goes. A check whose every run depends
-- on the input alone ('fireReads', 'onInput') is decided run by run
-- ('runTree'). It stays in main if any part of any run is undecided, and
-- then entirely: deciding its other failures before main as well would
-- only make them twice. Any other check stays in main.
checkVerdicts :: CheckAnalysis -> Map AbortOrigin CheckVerdict
checkVerdicts (CheckAnalysis fires result) = verdict <$> fires where
  verdict fs
    | all (maybe False (all onInput) . fireReads) fs
    , let runs = [ (firePath f, runTree result f) | f <- fs ]
    , not (any (undecidedIn . snd) runs) = CheckVerdict runs False
    | otherwise = CheckVerdict [] True

-- |main's input prologue: a function run on main's input before main,
-- giving Zero when every hoisted check passes and, when one does not, the
-- abort of the first in the order they were written. Nothing when no check
-- is hoisted. The first call of main, made before there is any input, runs
-- without it ('Telomare.Driver.funWrapWith').
--
-- Each run of a check decided before main becomes its tree ('runTree') as
-- gates on input positions, under gates testing the path that reached it:
-- Zero where it passes, its abort where it fails. Of what the path knows,
-- only the deepest of its pairs and the shallowest of its Zeros are
-- tested, since the rest follows. The verdicts are chained through gates,
-- which an aborted verdict ends.
inputPrologue :: Map AbortOrigin CheckVerdict -> Maybe CompiledExpr
inputPrologue verdicts = case runs of
  [] -> Nothing
  vs -> Just $ PairB (deferB inputPrologueInd (foldr chain ZeroB vs)) ZeroB
  where
    runs = [ onPath (knownZero p) (knownPair p) (treeCode o t)
           | (o, v) <- Map.toAscList verdicts, (p, t) <- hoistedRuns v, t /= Passes ]
    chain v rest = GateSwitchEE rest ZeroB v
    onPath zs ps code =
      foldr (\n c -> GateSwitchEE c ZeroB (inputPath n))
        (foldr (\n c -> GateSwitchEE ZeroB c (inputPath n)) code (deepest ps)) (shallowest zs)
    deepest ps = [ n | n <- Set.toList ps, not (any (\m -> m /= n && decendant m n) (Set.toList ps)) ]
    shallowest zs = [ n | n <- Set.toList zs, not (any (\m -> m /= n && decendant n m) (Set.toList zs)) ]
    treeCode o = \case
      Passes      -> ZeroB
      Fails msg   -> AbortB o (resultCode msg)
      Undecided   -> error "inputPrologue: a check main keeps was hoisted"
      Split n a b -> GateSwitchEE (treeCode o a) (treeCode o b) (inputPath n)
    resultCode :: UnsizedExpr -> CompiledExpr
    resultCode = \case
      ZeroB -> ZeroB
      PairB a b -> PairB (resultCode a) (resultCode b)
      IndexedEE (IVarF m) -> inputPath m
      SuperEE (EitherPF (Just n) a b) -> GateSwitchEE (resultCode a) (resultCode b) (inputPath n)
      other -> error $ "inputPrologue: a hoisted check's result is not a decision over the input:\n"
        <> prettyPrint other

-- |An input position as code whose env is (input, _): position 0 is the
-- input, and 2n + 1 and 2n + 2 are n's left and right.
inputPath :: Integer -> CompiledExpr
inputPath = \case
  0 -> LeftB EnvB
  n | odd n     -> LeftB (inputPath ((n - 1) `div` 2))
    | otherwise -> RightB (inputPath ((n - 2) `div` 2))

-- |How many abstract evaluation steps deciding a program's checks may take
-- before the compiler gives up and keeps them all where they are.
checkDecisionBudget :: Int
checkDecisionBudget = 100000000

-- |Where a sized main's refinement checks go ('checkVerdicts'): those
-- erased from main, because they can never fail, or every failure of
-- them that matters is decided before main, and main's input prologue.
-- When analyzing the checks is over budget, every check stays in main.
checkPlan :: CompiledExpr -> (AbortOrigin -> Bool, Maybe CompiledExpr)
checkPlan sized = case analyzeChecks checkDecisionBudget (indexedEE $ IVarF 0) Set.empty sized of
  Nothing -> (const False, Nothing)
  Just analysis ->
    let verdicts = checkVerdicts analysis
        erased o = maybe True (not . keptInMain) (Map.lookup o verdicts)
    in (erased, inputPrologue verdicts)

-- |Substitute sized chains for a term's recursion holes.
setSizes :: Map UnsizedRecursionToken (Maybe Int) -> UnsizedExpr -> UnsizedExpr
setSizes sizeMap = cata $ \case
  UnsizedFW _us@(UnsizedStubF tok _) ->
    let n = chainLinks (SizedRecursion sizeMap) tok
    in debugTrace ("sizeTermM setting size: " <> show (tok, n)) sizedRecursionChain n
  UnsizedFW (TraceF _ inner) -> inner
  other -> embed other

evalStaticCheck :: Bool -> StaticCheckExpr -> Maybe (AbortOrigin, BasicExpr)
evalStaticCheck shouldCap t =
  let unhandledError x = error ("evalA unhandled case " <> prettyPrint x)
      runResult = let aStep :: StaticCheckExprF StaticCheckExpr -> StaticCheckExpr
                      aStep = basicStep (stuckStep (abortStep (deferredEvalStep' unhandledError)))
                      eval' :: StaticCheckExpr -> StaticCheckExpr
                      eval' = transformNoDefer aStep
                      inp = deferredEE $ BarrierF EnvB
                      x = (\x' -> debugTrace ("evalA starting expr:\n" <> prettyPrint x') x') $ if shouldCap then capMain inp t else t
                  in eval' x
      -- a fired abort: not under a defer (code that has not run) or a
      -- barrier (code waiting on input)
      getAborted = \case
        AbortFW (AbortF o (m, im)) -> im <|> Just (o, messageData m)
        DeferredFW (BarrierF _)    -> Nothing
        StuckFW (DeferSF _ _)      -> Nothing
        x                          -> foldr ((<|>) . snd) Nothing x
  in para getAborted runResult

-- |What the sizing pass learned, kept rather than discarded. These iteration
-- counts are the numbers the compiler already relies on to claim a program is
-- total; reporting them asserts nothing new.
data SizingReport = SizingReport
  { sizingReportCounts :: SizedRecursion
  -- ^Per recursion site, the iteration count inferred over every input.
  , sizingReportLocs   :: Map UnsizedRecursionToken LocTag
  -- ^Where each site is in the source.
  , sizingReportBudget :: Int
  -- ^The unrolling budget the search was allowed.
  }

-- |Every recursion site's source location, recovered from the `Term3`
-- annotations that `term3ToUnsizedExpr` drops on its way to `UnsizedExpr`.
buildUnsizedLocMap :: Term3 -> Map UnsizedRecursionToken LocTag
buildUnsizedLocMap = cata f where
  f (anno CofreeT.:< g) = case g of
    Term3Unsized tok -> Map.singleton tok anno
    x                -> Data.Foldable.fold x

-- |`sizeTermM` names the recursion that failed but cannot say where it is.
locateSizingFailure :: Map UnsizedRecursionToken LocTag -> SizingFailure -> SizingFailure
locateSizingFailure locs failure =
  failure { sizingFailureLoc = Map.lookup (sizingFailureToken failure) locs }

-- |Every recursion site in the program, where it is, and how many times it can
-- iterate. The counts hold for every input: the sizing pass finds them by
-- running the program over a symbolic input, and takes the worst case across
-- the paths it explores.
--
-- Nothing here is a new claim. These are the very numbers the compiler bakes
-- into the program to make it total; a program that does not size does not
-- compile at all.
renderSizingCertificate :: SizingReport -> String
renderSizingCertificate report = unlines $
  "recursion sites (iterations, over every input):"
    : (if null sites then ["  none - this program has no unsized recursion"] else sites)
    <> ["", "sizing budget in force: " <> show (sizingReportBudget report) <> " unrollings"]
  where
    counts = Map.toAscList . unSizedRecursion $ sizingReportCounts report
    sites = fmap site counts
    site (tok, size) = "  " <> pad (place tok) <> "  <= " <> maybe "?" show size
    place tok =
      let named = "#" <> show (unUnsizedRecursionToken tok)
      in case Map.lookup tok (sizingReportLocs report) >>= renderLocTagCompact of
           Just spot -> spot <> " (" <> named <> ")"
           Nothing   -> named
    width = maximum (0 : fmap (length . place . fst) counts)
    pad s = s <> replicate (width - length s) ' '

