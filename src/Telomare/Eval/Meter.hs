{-# LANGUAGE LambdaCase #-}

-- |Measured cost of a concrete run: how many evaluation steps it took, and how
-- many term nodes it built along the way.
--
-- Both numbers are /measured/, not analysed. Nothing here predicts the cost of
-- a run that has not happened; for an a-priori claim see the per-recursion-site
-- iteration counts that the sizing pass already infers
-- (`Telomare.Eval.renderSizingCertificate`).
--
-- == Why there is no memory figure here
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
-- needs reachability over distinct nodes, and that is what
-- `Telomare.Eval.Space` now measures: this same interpreter defunctionalized
-- over an explicit store, where sharing is id-sharing and the live heap is
-- what the machine's roots reach. @--meter@ reports its peak. This module
-- stays as it is — the fast mirror whose step and build counts the space
-- machine must match tick for tick, which is what keeps both honest.
--
-- `meterBuilt` is a count of the nodes the run constructs. It is well defined
-- without any sharing analysis, and it still shows how much term-building a
-- program does.
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
-- `evalMeter` mirrors `Telomare.Eval.Reference`'s
-- @instance AbstractRunTime CompiledExpr@. Being a second interpreter, it can
-- drift; `test/SizingTests.hs` asserts it still computes the same value, which
-- is what keeps the mirror honest. One difference is deliberate and easy to
-- "fix" by mistake: the evaluator gets lazy gate branches from Haskell rather
-- than from its own structure, so the unselected branch is never forced. See
-- the `GateSwitch` case.
module Telomare.Eval.Meter where

import Control.Monad.State.Strict (State, modify', runState)
import Data.Foldable (asum)
import Data.Functor.Foldable (cata, project)
import Numeric.Natural (Natural)

import Telomare.IR.Base
import Telomare.IR.Core
import Telomare.Machine (abortInd, deferB, doLeft, doRight)

-- |What a run cost.
data Meter = Meter
  { meterSteps :: !Natural
  -- ^Evaluation steps taken.
  , meterBuilt :: !Natural
  -- ^Term nodes constructed. Not a memory figure — see the module header.
  }
  deriving (Eq, Show)

-- |Across a session both totals accumulate.
instance Semigroup Meter where
  a <> b = Meter (meterSteps a + meterSteps b) (meterBuilt a + meterBuilt b)

instance Monoid Meter where
  mempty = Meter 0 0

-- |What to print for a measured run.
renderMeter :: Meter -> String
renderMeter m = "steps (measured): " <> show (meterSteps m)
  <> "\nnodes built (measured): " <> show (meterBuilt m)

type M = State Meter

step :: M ()
step = modify' $ \m -> m { meterSteps = meterSteps m + 1 }

built :: M ()
built = modify' $ \m -> m { meterBuilt = meterBuilt m + 1 }

-- |The value `EnvSF` stands for while a function body is being evaluated.
-- Nothing at the top level, where an `EnvSF` would be a bug.
type Env = Maybe CompiledExpr

-- |Evaluate, metering.
runMeter :: Env -> CompiledExpr -> M CompiledExpr
runMeter env whole = case project whole of
  -- Already values.
  BasicFW ZeroSF       -> settled
  StuckFW DeferSF {}   -> settled
  AbortFW AbortF       -> settled
  AbortFW (AbortedF _) -> settled
  StuckFW GateSF       -> settled

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
      AbortEE (AbortedF _) -> pure s'
      BasicEE ZeroSF       -> chose l
      BasicEE PairSF {}    -> chose r
      _                    -> unhandled "gate on a non-data scrutinee" s'

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
      AbortEE (AbortedF _) -> step >> pure x'
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
        AbortEE (AbortedF _) -> pure x'
        _ -> case pick x' of
          Just v  -> pure v
          Nothing -> unhandled "projection of something that is not a pair" x'

    apply f e = case (f, e) of
      (AbortEE (AbortedF _), _) -> step >> pure f
      (_, AbortEE (AbortedF _)) -> step >> pure e
      -- `assert` on a passing value yields the identity function.
      (AbortEE AbortF, BasicEE ZeroSF) -> step >> pure identityFunction
      (AbortEE AbortF, _) -> do
        step
        built
        pure . AbortEE . AbortedF $ cata truncateToData e
      -- A gate applied to its scrutinee alone yields the branch-selector
      -- function the evaluator would produce; the `GateSwitch` case above is
      -- the one that keeps the usual full shape lazy.
      (StuckEE GateSF, BasicEE ZeroSF) -> step >> pure doLeft
      (StuckEE GateSF, BasicEE PairSF {}) -> step >> pure doRight
      -- The body's environment is now `e`; nothing is substituted or built.
      (StuckEE (DeferSF _ body), _) -> step >> runMeter (Just e) body
      _ -> unhandled "application of something that is not a function" f

    truncateToData = \case
      BasicFW ZeroSF       -> BasicEE ZeroSF
      BasicFW (PairSF a b) -> PairB a b
      _                    -> BasicEE ZeroSF

    unhandled why what = error $ "Telomare.Meter: " <> why <> ":\n" <> show what

-- |The identity function a passed assertion becomes, carrying the index the
-- evaluator gives it.
identityFunction :: CompiledExpr
identityFunction = deferB abortInd $ StuckEE EnvSF

-- |Run a compiled program on an input, reporting what it cost. The result
-- mirrors @eval@: an abort surfaces as a `RunTimeError`.
evalMeter :: CompiledExpr -> (Meter, Either RunTimeError CompiledExpr)
evalMeter expr =
  let (result, measured) = runState (runMeter Nothing expr) mempty
  in (measured, case findAborted result of
       Just e  -> Left $ AbortRunTime e
       Nothing -> pure result)
  where
    findAborted = cata $ \case
      AbortFW (AbortedF e) -> Just e
      x                    -> asum x
