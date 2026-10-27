{-# LANGUAGE LambdaCase #-}

-- |Measured cost of a concrete run: how many evaluation steps it took, and how
-- many term nodes it built along the way.
--
-- Both numbers are /measured/, not analysed. Nothing here predicts the cost of
-- a run that has not happened; for an a-priori claim see the per-recursion-site
-- iteration counts that the sizing pass already infers
-- (`Telomare.Eval.renderSizingCertificate`).
--
-- == Why there is no memory figure
--
-- There was one, and it was wrong, in a way worth recording so it is not
-- reintroduced. Telomare evaluates by rewriting a term, so it is tempting to
-- call the residual term's node count its memory. But the evaluator binds one
-- environment that every `EnvSF` in a body refers to, and chains each
-- environment onto the last, so the structure it holds is a graph with heavy
-- sharing. Counting it as a tree counts shared structure once per reference:
-- for `tictactoe.tel` that reads 50 billion nodes, about 1.2TB, for a run that
-- takes 5.7GB — and most of that 5.7GB is the sizing pass, not the run.
--
-- This is the same shape as the dead end recorded in the sibling project's
-- @design/SPACE.md@, one level further down. There, a cost algebra could not
-- see /retention/; here, a tree metric cannot see /sharing/. A real figure
-- needs reachability over distinct nodes — hash-consing, not arithmetic — and
-- is deliberately left undone rather than approximated. For actual memory, run
-- the binary under @+RTS -s@.
--
-- `meterBuilt` is what survives of the idea: a count of the nodes the run
-- constructs. It is well defined without any sharing analysis, and it still
-- shows how much term-building a program does.
--
-- == Substitution
--
-- Applying a function binds the body's `EnvSF` to the argument as evaluation
-- reaches it, rather than substituting through the body first. That mirrors
-- the evaluator, which fuses the two. Substituting first is both slower and
-- wrong: it walks into the substituted value at every `EnvSF`, which the
-- evaluator does not do, and inflated the step count for `simpleplus.tel` from
-- 46 thousand to 17 million.
--
-- == Refinement checks
--
-- A check compiles to a defer with the reserved index
-- 'Telomare.Machine.removeRefinementWrappersTC', so the meter recognises
-- one when it applies it and charges the steps spent inside to the check's
-- origin, less those of the checks nested in it. The per-origin costs
-- therefore add up to the checks' share of 'meterSteps'.
--
-- `evalMeter` mirrors `Telomare.Eval.Reference`'s
-- @instance AbstractRunTime CompiledExpr@. Being a second interpreter, it can
-- drift; `test/SizingTests.hs` asserts it still computes the same value, which
-- is what keeps the mirror honest. One difference is deliberate and easy to
-- "fix" by mistake: the evaluator gets lazy gate branches from Haskell rather
-- than from its own structure, so the unselected branch is never forced. See
-- the `GateSwitch` case.
module Telomare.Eval.Meter where

import Control.Applicative ((<|>))
import Control.Monad.State.Strict (State, get, modify', put, runState)
import Data.Functor.Foldable (cata, project)
import Data.List (sortOn)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ord (Down (..))
import Numeric.Natural (Natural)

import Telomare.IR.Base
import Telomare.IR.Core
import Telomare.Machine (doLeft, doRight, removeRefinementWrappersTC)

-- |What a run cost.
data Meter = Meter
  { meterSteps  :: !Natural
  -- ^Evaluation steps taken.
  , meterBuilt  :: !Natural
  -- ^Term nodes constructed. Not a memory figure — see the module header.
  , meterChecks :: !(Map AbortOrigin CheckCost)
  -- ^What the refinement checks cost, by where each was written.
  }
  deriving (Eq, Show)

-- |What one refinement check (one origin) cost over a run.
data CheckCost = CheckCost
  { checkRuns  :: !Natural
  -- ^How many times it ran.
  , checkSteps :: !Natural
  -- ^Steps spent running it, less those of the checks nested in it, so the
  -- costs of all checks add up to their share of 'meterSteps'.
  }
  deriving (Eq, Show)

instance Semigroup CheckCost where
  a <> b = CheckCost (checkRuns a + checkRuns b) (checkSteps a + checkSteps b)

instance Monoid CheckCost where
  mempty = CheckCost 0 0

-- |Across a session all the totals accumulate.
instance Semigroup Meter where
  a <> b = Meter (meterSteps a + meterSteps b) (meterBuilt a + meterBuilt b)
    (Map.unionWith (<>) (meterChecks a) (meterChecks b))

instance Monoid Meter where
  mempty = Meter 0 0 Map.empty

-- |What to print for a measured run.
renderMeter :: Meter -> String
renderMeter m = "steps (measured): " <> show (meterSteps m)
  <> "\nnodes built (measured): " <> show (meterBuilt m)
  <> checks
  where
    costs = sortOn (Down . checkSteps . snd) . Map.toList $ meterChecks m
    total = foldMap snd costs
    checks
      | null costs = ""
      | otherwise = "\nrefinement checks (measured): " <> show (checkRuns total)
          <> " runs, " <> show (checkSteps total) <> " steps ("
          <> percent (checkSteps total) <> " of all steps)"
          <> concatMap line costs
    line (o, c) = "\n  " <> renderAbortOrigin o <> ": " <> show (checkRuns c)
      <> " runs, " <> show (checkSteps c) <> " steps"
    percent n
      | meterSteps m == 0 = "-"
      | otherwise = show (n * 100 `div` meterSteps m) <> "%"

-- |The meter, and the steps of the checks finished inside the check
-- currently running (for charging each check only its own steps).
data MeterState = MeterState !Meter !Natural

type M = State MeterState

step :: M ()
step = modify' $ \(MeterState m n) -> MeterState m { meterSteps = meterSteps m + 1 } n

built :: M ()
built = modify' $ \(MeterState m n) -> MeterState m { meterBuilt = meterBuilt m + 1 } n

-- |Run a refinement check, charging its origin the steps it takes less
-- those of the checks nested in it.
checking :: AbortOrigin -> M a -> M a
checking o act = do
  MeterState m0 outer <- get
  put (MeterState m0 0)
  r <- act
  MeterState m1 nested <- get
  let inclusive = meterSteps m1 - meterSteps m0
      cost = CheckCost 1 (inclusive - nested)
  put $ MeterState m1 { meterChecks = Map.insertWith (<>) o cost (meterChecks m1) }
    (outer + inclusive)
  pure r

-- |The origin of a refinement check's outer body ('Telomare.Machine.refinementCheckB'):
-- the one abort in it.
checkOrigin :: CompiledExpr -> Maybe AbortOrigin
checkOrigin = cata $ \case
  AbortFW (AbortF o _) -> Just o
  x                    -> foldr (<|>) Nothing x
-- |The value `EnvSF` stands for while a function body is being evaluated.
-- Nothing at the top level, where an `EnvSF` would be a bug.
type Env = Maybe CompiledExpr

-- |Evaluate, metering.
runMeter :: Env -> CompiledExpr -> M CompiledExpr
runMeter env whole = case project whole of
  -- Already values.
  BasicFW ZeroSF       -> settled
  StuckFW DeferSF {}   -> settled
  StuckFW GateSF       -> settled

  -- An abort evaluates its message and becomes an aborted value; an abort
  -- in the message is the one that counts.
  AbortFW (AbortF o m) -> do
    m' <- runMeter env m
    step
    case m' of
      AbortEE AbortF {} -> pure m'
      _                 -> built >> pure (AbortB o m')

  -- A gate switch. The branches sit in the application's argument pair and
  -- stay unevaluated until the scrutinee picks one. The evaluator gets this
  -- from Haskell's laziness: it discards the unselected thunk without ever
  -- forcing it. That is load-bearing, not incidental — a bounded recursion's
  -- "recurse" branch is still present at the base case, and evaluating it
  -- would run off the end of the repeater's inferred size.
  --
  -- Only the chosen branch is evaluated, and in the current environment: a
  -- gate is built and applied at the same node (`iteB_`), so its branches
  -- belong to this environment.
  GateSwitch l r s -> do
    s' <- runMeter env s
    step
    case s' of
      AbortEE AbortF {} -> pure s'
      BasicEE ZeroSF    -> chose l
      BasicEE PairSF {} -> chose r
      _                 -> unhandled "gate on a non-data scrutinee" s'

  BasicFW (PairSF a b) -> do
    a' <- runMeter env a
    b' <- runMeter env b
    built
    step
    pure $ PairB a' b'

  StuckFW (LeftSF x)  -> project' x $ \case
    BasicEE (PairSF l _) -> Just l
    z@(BasicEE ZeroSF)   -> Just z
    _                    -> Nothing
  StuckFW (RightSF x) -> project' x $ \case
    BasicEE (PairSF _ r) -> Just r
    z@(BasicEE ZeroSF)   -> Just z
    _                    -> Nothing

  StuckFW (SetEnvSF x) -> do
    x' <- runMeter env x
    case x' of
      AbortEE AbortF {}    -> step >> pure x'
      BasicEE (PairSF f e) -> apply f e
      _ -> unhandled "SetEnv of something that is not a pair" x'

  -- The environment is a value, already evaluated by whoever bound it.
  StuckFW EnvSF -> case env of
    Just bound -> step >> pure bound
    Nothing    -> unhandled "unapplied environment reference" whole

  _ -> error "Telomare.Eval.Meter.runMeter: unexpected expression"
  where
    settled = step >> pure whole

    chose branch = step >> runMeter env branch

    project' x pick = do
      x' <- runMeter env x
      step
      case x' of
        AbortEE AbortF {} -> pure x'
        _ -> case pick x' of
          Just v  -> pure v
          Nothing -> unhandled "projection of something that is not a pair" x'

    apply f e = case (f, e) of
      (AbortEE AbortF {}, _) -> step >> pure f
      (_, AbortEE AbortF {}) -> step >> pure e
      -- A gate applied to its scrutinee alone yields the branch-selector
      -- function the evaluator would produce; the `GateSwitch` case above is
      -- the one that keeps the usual full shape lazy.
      (StuckEE GateSF, BasicEE ZeroSF) -> step >> pure doLeft
      (StuckEE GateSF, BasicEE PairSF {}) -> step >> pure doRight
      -- The body's environment is now `e`; nothing is substituted or built.
      -- A refinement check charges its steps to where it was written.
      (StuckEE (DeferSF fi body), _)
        | fi == toEnum removeRefinementWrappersTC, Just o <- checkOrigin body ->
            step >> checking o (runMeter (Just e) body)
      (StuckEE (DeferSF _ body), _) -> step >> runMeter (Just e) body
      _ -> unhandled "application of something that is not a function" f

    unhandled why what = error $ "Telomare.Meter: " <> why <> ":\n" <> show what

-- |Run a compiled program on an input, reporting what it cost. The result
-- mirrors @eval@: an abort surfaces as a `RunTimeError`.
evalMeter :: CompiledExpr -> (Meter, Either RunTimeError CompiledExpr)
evalMeter expr =
  let (result, MeterState measured _) = runState (runMeter Nothing expr) (MeterState mempty 0)
  in (measured, case firedAbort result of
       Just (o, e) -> Left $ AbortRunTime o e
       Nothing     -> pure result)
