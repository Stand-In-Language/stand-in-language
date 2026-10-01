{-# LANGUAGE LambdaCase #-}

-- | Driver glue for the interaction-combinator runtime ('Telomare.IC'):
-- the admission gate and the guided evaluator, in the shape the eval loop
-- ('Telomare.Driver.evalLoopCore') consumes.
--
-- The net's correctness rests on EAL typability ('Telomare.EAL'), so a
-- driver must not hand it a program without the certificate — that is
-- 'admitIC', run once per compiled program. Iterations only ever apply the
-- program to data input, which the certificate's virtual application of
-- main already covers, so one admission holds for a whole session; the
-- capture layouts riding on the granted plan feed the runtime's guided
-- closure-duplication strategy ('Telomare.EAL.ealCaptureLayouts').
module Telomare.Eval.IC where

import Crypto.Hash (Digest, SHA256)
import Data.List (sortOn)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ord (Down (..))

import Telomare.EAL (CapShape, EALLiftedResult (..), ealCaptureLayouts,
                     inferEALCompiled, renderEALVerdict)
import Telomare.Error (EALError (..), renderEALError)
import Telomare.IC (defaultFuel, icRunReport)
import Telomare.IR.Core (CompiledExpr, RunTimeError)

-- | What admission grants a session: the right to run on the net at all,
-- plus the per-hash capture layouts that guide it. A record rather than a
-- bare map so further guidance a driver threads through (scheduling
-- hints, erasure plans) has somewhere to land.
newtype ICPlan = ICPlan
  { icPlanLayouts :: Map (Digest SHA256) CapShape }

-- | The admission gate, from scratch: certify the compiled program on
-- its own account and grant a plan only on success. The refusal is
-- rendered for a user — the whole-program verdict first, then the bodies
-- that failed on their own account (dependency-failure cascades are
-- elided when a root cause is present). A driver that compiled through
-- 'Telomare.Driver.compileMainReporting' already holds this inference's
-- product and reads the same admission off it with
-- 'Telomare.Driver.programPlan' instead of paying for it again here.
admitIC :: CompiledExpr -> Either String ICPlan
admitIC expr =
  let lr = inferEALCompiled expr
  in case ealLiftedMain lr of
       Right _ -> Right . ICPlan $ ealCaptureLayouts lr
       Left _  -> Left $ renderRefusal lr

renderRefusal :: EALLiftedResult -> String
renderRefusal lr = unlines $ verdict : bodies
  where
    verdict =
      "the IC runtime requires an EAL certificate; this program "
        <> renderEALVerdict lr
    failures = [ (h, e) | (h, Left e) <- Map.toList (ealGuidance lr) ]
    rootCauses = case filter (not . isCascade . snd) failures of
      []    -> failures
      roots -> roots
    isCascade = \case
      EALDependencyFailed _ -> True
      _rootCause            -> False
    bodies =
      [ "  body " <> take 12 (show h) <> ": " <> renderEALError e
      | (h, e) <- rootCauses ]

-- | What a session on the net cost: interactions spent against fuel, and
-- every counter the runtime keeps (interaction rules and compile-time
-- notes alike, told apart by name).
data ICMeter = ICMeter
  { icMeterInteractions :: !Int
  , icMeterEvents       :: Map String Int
  } deriving (Eq, Show)

-- | Across a session both the total and the per-event counts accumulate.
instance Semigroup ICMeter where
  a <> b = ICMeter
    (icMeterInteractions a + icMeterInteractions b)
    (Map.unionWith (+) (icMeterEvents a) (icMeterEvents b))

instance Monoid ICMeter where
  mempty = ICMeter 0 Map.empty

-- | What to print for a measured session, busiest counters first.
renderICMeter :: ICMeter -> String
renderICMeter m = unlines $
  ("interactions (measured): " <> show (icMeterInteractions m))
    : [ "  " <> name <> ": " <> show n
      | (name, n) <- sortOn (Down . snd) (Map.toList (icMeterEvents m)) ]

-- | One iteration on the net under an admission's plan, measured. The
-- outcome follows the reference evaluator's contract
-- ('Telomare.IC.icOutcome'), so the loop treats both evaluators alike.
evalIC :: ICPlan -> CompiledExpr -> (ICMeter, Either RunTimeError CompiledExpr)
evalIC plan term =
  let (outcome, spent, events) =
        icRunReport (icPlanLayouts plan) defaultFuel term
  in (ICMeter spent events, outcome)
