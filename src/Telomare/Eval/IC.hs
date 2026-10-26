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
import Telomare.IC (ICCost (..), Resources (..), defaultFuel, icRunReport,
                    maxResources, noResources)
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

-- | What a session on the net cost: interactions spent against fuel,
-- every counter the runtime keeps (interaction rules and compile-time
-- notes alike, told apart by name), and storage: the largest net any one
-- iteration built and the largest template table. Storage is counted in
-- the net's own units ('Telomare.IC.Resources'), not bytes.
data ICMeter = ICMeter
  { icMeterInteractions :: !Int
  , icMeterEvents       :: Map String Int
  , icMeterPeak         :: !Resources
  , icMeterTemplates    :: !Resources
  } deriving (Eq, Show)

-- | Across a session the total and the per-event counts accumulate;
-- storage peaks combine by maximum, since each iteration builds its net
-- afresh.
instance Semigroup ICMeter where
  a <> b = ICMeter
    (icMeterInteractions a + icMeterInteractions b)
    (Map.unionWith (+) (icMeterEvents a) (icMeterEvents b))
    (maxResources (icMeterPeak a) (icMeterPeak b))
    (maxResources (icMeterTemplates a) (icMeterTemplates b))

instance Monoid ICMeter where
  mempty = ICMeter 0 Map.empty noResources noResources

-- | What to print for a measured session, busiest counters first.
renderICMeter :: ICMeter -> String
renderICMeter m = unlines $
  ("interactions (measured): " <> show (icMeterInteractions m))
    : [ "  " <> name <> ": " <> show n
      | (name, n) <- sortOn (Down . snd) (Map.toList (icMeterEvents m)) ]
  <> [ "peak net, largest iteration (measured): "
         <> show (resAgents peak) <> " agents, "
         <> show (resPorts peak) <> " port entries, "
         <> show (resWork peak) <> " pending pairs"
     , "template table (measured): "
         <> show (resAgents tpl) <> " agents, "
         <> show (resPorts tpl) <> " port entries" ]
  where
    peak = icMeterPeak m
    tpl = icMeterTemplates m

-- | One iteration on the net under an admission's plan, measured. The
-- outcome follows the reference evaluator's contract
-- ('Telomare.IC.icOutcome'), so the loop treats both evaluators alike.
evalIC :: ICPlan -> CompiledExpr -> (ICMeter, Either RunTimeError CompiledExpr)
evalIC plan term =
  let (outcome, cost) = icRunReport (icPlanLayouts plan) defaultFuel term
  in ( ICMeter (costInteractions cost) (costEvents cost)
         (costPeak cost) (costTemplates cost)
     , outcome )
