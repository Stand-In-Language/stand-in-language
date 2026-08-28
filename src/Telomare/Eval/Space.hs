{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase   #-}

-- |The memory figure `Telomare.Eval.Meter` deliberately leaves undone: the
-- live-heap peak of a concrete run, measured over /distinct/ nodes.
--
-- The evaluator binds one environment that every `EnvSF` in a body refers to,
-- so what a run holds is a graph with heavy sharing, and counting it as a tree
-- overcounts by orders of magnitude (see the Meter module header for the
-- numbers). This module measures instead of counting: it is the same
-- interpreter as `Telomare.Eval.Meter.runMeter`, defunctionalized into a
-- CEK-style machine whose values live in an explicit store keyed by node id.
-- Sharing is id-sharing — an `EnvSF` resolves to the id the environment was
-- allocated under, never to a copy — so "live heap" is reachability from the
-- machine's roots (the environment, the continuation frames, and the value
-- being returned) over distinct ids, and the peak is the maximum live figure
-- along the run. Retention needs no special handling: a value held by a frame
-- while a sibling evaluates is reachable from that frame, so it is counted for
-- exactly as long as something can still use it.
--
-- The unit is the /cell/: one value node — `ZeroN`, `PairN`, `GateN`,
-- `AbortN`, a `DeferN` (a reference to static code, which itself weighs
-- nothing), or an `AbortedN` at one cell plus its data payload.
--
-- Being a third interpreter, this can drift. What keeps it honest is that
-- `spSteps` and `spBuilt` tick in exactly the places `runMeter`'s counters do,
-- and `test/ConformanceTests.hs` asserts both the computed value and those two
-- counts agree with the Meter on every corpus program. The lazy gate branches
-- are load-bearing here as they are there: a `KGate` frame holds its branches
-- as syntax and only the chosen one is ever evaluated.
--
-- Sweeping the store at every allocation makes the peak exact but costs a
-- reachability walk per allocation; `SweepAdaptive` amortizes that away
-- (sweep when the cells allocated since the last sweep exceed half the last
-- live figure) at the price of bracketing the true peak between
-- `spPeakLower` and `spPeakUpper`. Unreachable nodes are dropped at each
-- sweep, which is what makes the upper end of the bracket valid: between
-- sweeps the store only grows, so no intermediate live set can exceed the
-- last live figure plus the cells allocated since.
module Telomare.Eval.Space where

import Data.Foldable (asum)
import Data.Functor.Foldable (cata, project)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import Numeric.Natural (Natural)

import Telomare.Eval.Meter (identityFunction)
import Telomare.IR.Base
import Telomare.IR.Core
import Telomare.Machine (doLeft, doRight)

-- |A key into the store. Distinctness of ids is what makes the live figure a
-- graph measure rather than a tree measure.
type NodeId = Int

-- |A value in the store. Only values live here; code stays syntax, so a
-- `DeferN` is one cell however large its body is.
data Node
  = ZeroN
  | PairN !NodeId !NodeId
  | DeferN !FunctionIndex CompiledExpr
  | GateN
  | AbortN
  | AbortedN BasicExpr
  deriving (Eq, Show)

-- |What a node holds live, in cells.
cellCost :: Node -> Natural
cellCost = \case
  AbortedN payload -> 1 + basicSize payload
  _                -> 1
  where
    basicSize :: BasicExpr -> Natural
    basicSize = cata $ \case
      ZeroSF     -> 1
      PairSF a b -> 1 + a + b

-- |The store children a node keeps reachable.
nodeChildren :: Node -> [NodeId]
nodeChildren = \case
  PairN a b -> [a, b]
  _         -> []

-- |When to measure. Exact costs a reachability walk per allocation; adaptive
-- amortizes it and brackets the peak instead of pinning it.
data SweepPolicy = SweepEveryAlloc | SweepAdaptive
  deriving (Eq, Show)

-- |What a run cost, now with a memory figure.
data SpaceMeter = SpaceMeter
  { spSteps     :: !Natural
  -- ^Evaluation steps taken; ticks where `Telomare.Eval.Meter.meterSteps` does.
  , spBuilt     :: !Natural
  -- ^Term nodes constructed; ticks where `Telomare.Eval.Meter.meterBuilt` does.
  , spPeakLower :: !Natural
  -- ^A live figure the run actually reached.
  , spPeakUpper :: !Natural
  -- ^A figure the run never exceeded. Equal to `spPeakLower` under
  -- `SweepEveryAlloc`.
  }
  deriving (Eq, Show)

-- |Across a session the totals accumulate and the peaks are the worst
-- iteration's, since each iteration starts from a fresh store.
instance Semigroup SpaceMeter where
  a <> b = SpaceMeter
    { spSteps = spSteps a + spSteps b
    , spBuilt = spBuilt a + spBuilt b
    , spPeakLower = max (spPeakLower a) (spPeakLower b)
    , spPeakUpper = max (spPeakUpper a) (spPeakUpper b)
    }

instance Monoid SpaceMeter where
  mempty = SpaceMeter 0 0 0 0

-- |What to print for a measured run.
renderSpaceMeter :: SpaceMeter -> String
renderSpaceMeter m = "steps (measured): " <> show (spSteps m)
  <> "\nnodes built (measured): " <> show (spBuilt m)
  <> "\nlive heap peak (measured): " <> peak <> " cells"
  where
    peak = if spPeakLower m == spPeakUpper m
      then show (spPeakLower m)
      else show (spPeakLower m) <> ".." <> show (spPeakUpper m)

-- |What the machine still has to do with the value it is returning.
data Frame
  = KPairRight CompiledExpr
  -- ^The first pair component is coming back; evaluate the second next.
  | KPairLeft !NodeId
  -- ^The first component, held live while the second evaluates.
  | KGate CompiledExpr CompiledExpr
  -- ^The scrutinee is coming back. The branches stay syntax so the
  -- unchosen one is never evaluated — load-bearing, see the Meter header.
  | KLeft
  | KRight
  | KSetEnv
  | KRestoreEnv !(Maybe NodeId)
  -- ^A function body is coming back; restore the caller's environment. The
  -- saved environment is a root: the caller can still use it.

frameRoots :: Frame -> [NodeId]
frameRoots = \case
  KPairLeft a           -> [a]
  KRestoreEnv (Just e)  -> [e]
  _                     -> []

data MachSt = MachSt
  { mStore    :: !(IntMap Node)
  , mNext     :: !NodeId
  , mEnv      :: !(Maybe NodeId)
  , mFrames   :: ![Frame]
  , mSteps    :: !Natural
  , mBuilt    :: !Natural
  , mPeakLow  :: !Natural
  , mPeakHigh :: !Natural
  , mLastLive :: !Natural
  -- ^Live cells at the last sweep; the store holds exactly the live nodes
  -- then, since sweeps drop the unreachable ones.
  , mDebt     :: !Natural
  -- ^Cells allocated since the last sweep.
  }

emptySt :: MachSt
emptySt = MachSt IntMap.empty 0 Nothing [] 0 0 0 0 0 0

step :: MachSt -> MachSt
step st = st { mSteps = mSteps st + 1 }

builtTick :: MachSt -> MachSt
builtTick st = st { mBuilt = mBuilt st + 1 }

-- |Mark from the roots and take the measure; drop what was not reached.
sweep :: Bool -- ^Exact: the store is measured at every allocation, so the
              -- live figure /is/ the bound.
      -> [NodeId] -> MachSt -> MachSt
sweep exact extraRoots st =
  let roots = extraRoots
        <> foldMap pure (mEnv st)
        <> concatMap frameRoots (mFrames st)
      reachable = mark (mStore st) IntSet.empty roots
      live = IntSet.foldr (\i acc -> acc + cellCost (mStore st IntMap.! i)) 0 reachable
      upperCandidate = if exact then live else mLastLive st + mDebt st
  in st { mStore = IntMap.restrictKeys (mStore st) reachable
        , mPeakLow = max (mPeakLow st) live
        , mPeakHigh = max (mPeakHigh st) upperCandidate
        , mLastLive = live
        , mDebt = 0
        }
  where
    mark _ visited [] = visited
    mark store visited (i : rest)
      | IntSet.member i visited = mark store visited rest
      | otherwise = mark store (IntSet.insert i visited)
          (nodeChildren (store IntMap.! i) <> rest)

-- |Put a node in the store; sweep if the policy says it is time. The fresh id
-- is a root — nothing else holds it yet.
alloc :: SweepPolicy -> Node -> MachSt -> (NodeId, MachSt)
alloc policy node st =
  let i = mNext st
      st1 = st { mStore = IntMap.insert i node (mStore st)
               , mNext = i + 1
               , mDebt = mDebt st + cellCost node
               }
      due = case policy of
        SweepEveryAlloc -> True
        SweepAdaptive   -> mDebt st1 > max 1024 (mLastLive st1 `div` 2)
  in (i, if due then sweep (policy == SweepEveryAlloc) [i] st1 else st1)

-- |Evaluate, measuring. The machine is `Telomare.Eval.Meter.runMeter` with
-- its continuations made explicit, which is what lets a sweep see its roots.
evalSpace :: SweepPolicy -> CompiledExpr -> (SpaceMeter, Either RunTimeError CompiledExpr)
evalSpace policy expr =
  let (finalSt, root) = evalC emptySt expr
      -- Fold the remaining debt into the peak before reading the result back.
      settledSt = sweep (policy == SweepEveryAlloc) [root] finalSt
      result = readback (mStore settledSt) root
      measured = SpaceMeter
        { spSteps = mSteps settledSt
        , spBuilt = mBuilt settledSt
        , spPeakLower = mPeakLow settledSt
        , spPeakUpper = mPeakHigh settledSt
        }
  in (measured, case findAborted result of
       Just e  -> Left $ AbortRunTime e
       Nothing -> Right result)
  where
    look st i = mStore st IntMap.! i

    settle st n = let (i, st') = alloc policy n (step st) in retC st' i

    allocRet st n = let (i, st') = alloc policy n st in retC st' i

    push f st = st { mFrames = f : mFrames st }

    -- The `GateSwitch` case must come before the generic `SetEnvSF` one: a
    -- gate switch is a `SetEnv` shape, and taking it apart generically would
    -- evaluate both branches.
    evalC !st whole = case project whole of
      GateSwitch l r s     -> evalC (push (KGate l r) st) s
      BasicFW ZeroSF       -> settle st ZeroN
      BasicFW (PairSF a b) -> evalC (push (KPairRight b) st) a
      StuckFW (DeferSF fi body) -> settle st (DeferN fi body)
      StuckFW GateSF       -> settle st GateN
      StuckFW (LeftSF x)   -> evalC (push KLeft st) x
      StuckFW (RightSF x)  -> evalC (push KRight st) x
      StuckFW (SetEnvSF x) -> evalC (push KSetEnv st) x
      StuckFW EnvSF -> case mEnv st of
        Just i  -> retC (step st) i
        Nothing -> unhandled "unapplied environment reference"
      AbortFW AbortF       -> settle st AbortN
      AbortFW (AbortedF e) -> settle st (AbortedN e)
      _ -> error "Telomare.Eval.Space.evalSpace: unexpected expression"

    retC !st v = case mFrames st of
      [] -> (st, v)
      KPairRight b : k -> evalC (st { mFrames = KPairLeft v : k }) b
      KPairLeft a : k ->
        allocRet (step (builtTick (st { mFrames = k }))) (PairN a v)
      KGate l r : k ->
        let st1 = step (st { mFrames = k })
        in case look st1 v of
          AbortedN _ -> retC st1 v
          ZeroN      -> evalC (step st1) l
          PairN _ _  -> evalC (step st1) r
          _          -> unhandled "gate on a non-data scrutinee"
      KLeft : k -> projRet (st { mFrames = k }) v $ \case
        PairN l _ -> Just l
        _         -> Nothing
      KRight : k -> projRet (st { mFrames = k }) v $ \case
        PairN _ r -> Just r
        _         -> Nothing
      KSetEnv : k ->
        let st1 = st { mFrames = k }
        in case look st1 v of
          AbortedN _ -> retC (step st1) v
          PairN f e  -> applyC st1 f e
          _          -> unhandled "SetEnv of something that is not a pair"
      KRestoreEnv saved : k ->
        retC (st { mEnv = saved, mFrames = k }) v

    projRet st v pick =
      let st1 = step st
      in case look st1 v of
        AbortedN _ -> retC st1 v
        ZeroN      -> retC st1 v
        n -> case pick n of
          Just i  -> retC st1 i
          Nothing -> unhandled "projection of something that is not a pair"

    applyC st f e = case (look st f, look st e) of
      (AbortedN _, _) -> retC (step st) f
      (_, AbortedN _) -> retC (step st) e
      -- `assert` on a passing value yields the identity function.
      (AbortN, ZeroN) -> allocRet (step st) (deferNode identityFunction)
      (AbortN, _)     ->
        allocRet (builtTick (step st)) (AbortedN (truncateData (mStore st) e))
      (GateN, ZeroN)     -> allocRet (step st) (deferNode doLeft)
      (GateN, PairN _ _) -> allocRet (step st) (deferNode doRight)
      -- The body's environment is now `e`; nothing is copied, so every
      -- `EnvSF` in the body resolves to this same id.
      (DeferN _ body, _) ->
        evalC ((step st) { mFrames = KRestoreEnv (mEnv st) : mFrames st
                         , mEnv = Just e }) body
      _ -> unhandled "application of something that is not a function"

    unhandled why = error $ "Telomare.Eval.Space: " <> why

    findAborted = cata $ \case
      AbortFW (AbortedF e) -> Just e
      x                    -> asum x

-- |The store view of a known function value.
deferNode :: CompiledExpr -> Node
deferNode x = case project x of
  StuckFW (DeferSF fi body) -> DeferN fi body
  _ -> error "Telomare.Eval.Space.deferNode: not a function"

-- |What an abort keeps of its argument: the data, with anything else read as
-- zero. Mirrors the Meter's @truncateToData@.
truncateData :: IntMap Node -> NodeId -> BasicExpr
truncateData store = go where
  go :: NodeId -> BasicExpr
  go i = case store IntMap.! i of
    PairN a b -> PairB (go a) (go b)
    _anything -> ZeroB

-- |The result as a term again, so the callers of the plain evaluator work
-- unchanged. Shared substructure is materialized per reference, exactly as
-- the tree evaluators would have built it.
readback :: IntMap Node -> NodeId -> CompiledExpr
readback store = go where
  go i = case store IntMap.! i of
    ZeroN          -> ZeroB
    PairN a b      -> PairB (go a) (go b)
    DeferN fi body -> StuckEE (DeferSF fi body)
    GateN          -> StuckEE GateSF
    AbortN         -> AbortEE AbortF
    AbortedN e     -> AbortEE (AbortedF e)
