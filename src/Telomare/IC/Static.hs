{-# LANGUAGE LambdaCase #-}

-- |A compositional storage estimate over a prepared IC program: no abstract
-- execution, no exploration of worlds. Where 'Telomare.IC.Space' walks the
-- net under the runtime's own scheduler and can answer @Unknown@,
-- this module only reads the template table and always answers.
--
-- The argument. Each of the three counters (agents, stored port entries,
-- pending pairs) only ever increments at an explicit 'account' site in
-- 'Telomare.IC' — 'newNode', 'setHalf' on an empty slot, 'connect' pushing a
-- pair — so the lifetime total of increments bounds the peak, whatever order
-- the redexes fire in. That order-independence is the whole point: it makes
-- the estimate immune to the LIFO scheduling and to the speculative firing of
-- both gate arms that defeat trace-based analyses.
--
-- Lifetime increments decompose into
--
--   1. the entry net ('icResident' of the prepared program) and the compiled
--      input, one agent and at most three port entries per input constructor
--      — the affine part, with the whole input as path 0;
--   2. template instantiations: the reference graph over the template table
--      is acyclic (a template's id is minted after everything its body
--      references), so a walk in descending id order bounds how many times
--      each template is spliced in ('staticInstBounds'). A gate or abort
--      node counts as a reference to the selector templates it can deliver
--      — both arms, since which one fires is data the analysis does not see;
--   3. copies: the copy multiplier below is @(1 + 3F)^L@ for @F@
--      duplication fans and @L@ one more than the deepest EAL box level.
--      This step is a heuristic, not a proof, and it can fail: @F@ is
--      counted from copy-free instantiation counts, although copying
--      creates further instantiations and fans; when the program-level EAL
--      solve gives up, the deepest per-body level stands in for the
--      program's depth, although nesting across bodies can stack levels;
--      and the multiplier grows single-exponentially in @L@, where
--      elementary affine logic allows a tower of exponentials of height
--      @L@. A hand-built Church-numeral tower of height five is estimated
--      at about 9×10^11 agents; its result has 2^65536 cells;
--   4. rule overhead: every rule in the table allocates at most a small
--      constant beyond what it consumes, folded into one factor of 4.
--
-- The constants — 3 allocations per copied node, the +1 level margin, the
-- overhead factor 4, ports and pending pairs from the templates' stored port
-- counts — are prose, not derived in code, and are checked only against the
-- measured peaks of small hand-written fixtures. The result is loose by
-- construction, often absurdly so; its virtues are that it exists for every
-- program that prepares and that it does not depend on firing order. It is
-- an estimate, and the rendered certificate says so.
module Telomare.IC.Static where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map as Map
import Numeric.Natural (Natural)

import Telomare.EAL (CodeGuidance (..), EALLiftedResult (..), EALResult (..))
import Telomare.IC
import Telomare.IC.Space (AnalysisOutcome (..), Claim (..), analyzeIC,
                          defaultAnalysisBudget, renderICSpace,
                          renderICSpaceCertificate)
import Telomare.SpaceBound

-- |How many times each template can be instantiated, at a given per-node
-- copy multiplier: entry-net references seed the walk, and every reference
-- inside an instantiated template multiplies through. Descending template
-- ids is topological order, since a template only references ids minted
-- before its own.
staticInstBounds :: Natural -> ICProgram -> IntMap Natural
staticInstBounds copies prog = foldl place seeds (IntMap.toDescList tpls)
  where
    tpls = icTemplates (programInitial prog)
    seeds = IntMap.map (copies *) (refTargets (icNodes (programInitial prog)))
    place inst (tid, tpl) = case IntMap.findWithDefault 0 tid inst of
      0 -> inst
      n -> IntMap.unionWith (+) inst
        (IntMap.map (\r -> copies * r * n) (refTargets (tplNodes tpl)))

-- |References a net's nodes can instantiate, template id by template id. A
-- gate can deliver either selector and an abort the identity selector, so
-- they count as references to those reserved templates.
refTargets :: IntMap Node -> IntMap Natural
refTargets nodes = IntMap.fromListWith (+)
  [ t | nd <- IntMap.elems nodes, t <- targets (nodeKind nd) ]
  where
    targets = \case
      ICRef tid _ -> [(tid, 1)]
      ICGate      -> [(leftSelTpl, 1), (rightSelTpl, 1)]
      ICAbort     -> [(idSelTpl, 1)]
      _           -> []

-- |The copy multiplier: @F@ duplication fans, nested @L@ levels deep by the
-- EAL analysis. When the program-level EAL solve gave up, the deepest
-- per-body level stands in for the program's depth — an approximation, since
-- nesting across bodies can stack levels (step 3 of the module argument).
copyMultiplier :: EALLiftedResult -> ICProgram -> IntMap Natural -> Natural
copyMultiplier eal prog inst = (1 + 3 * fans) ^ levels
  where
    tpls = icTemplates (programInitial prog)
    dupCount nodes = fromIntegral $ length
      [ () | nd <- IntMap.elems nodes, ICDup _ <- [nodeKind nd] ]
    fans = dupCount (icNodes (programInitial prog))
      + sum [ IntMap.findWithDefault 0 tid inst * dupCount (tplNodes tpl)
            | (tid, tpl) <- IntMap.toList tpls ]
    levels = 1 + maximum
      (0 : either (const []) (pure . ealMaxLevel) (ealLiftedMain eal)
         <> [ cgMaxLevel g | Right g <- Map.elems (ealGuidance eal) ])

-- |The estimate. Total, order-independent, and never @Unknown@: every
-- program 'prepareIC' accepts gets one. Not a proven bound (step 3 of the
-- module argument).
staticBound :: EALLiftedResult -> ICProgram -> Resources SpaceBound
staticBound eal prog =
  Resources (bound entryAgents instAgents 1) (ports 3) (ports 3)
  where
    entry = icResident (programInitial prog)
    entryAgents = resourceAgents entry
    entryPorts = resourcePorts entry
    tpls = icTemplates (programInitial prog)
    inst0 = staticInstBounds 1 prog
    copies = copyMultiplier eal prog inst0
    inst = staticInstBounds copies prog
    weigh perTpl = sum [ IntMap.findWithDefault 0 tid inst * perTpl tpl
                       | (tid, tpl) <- IntMap.toList tpls ]
    instAgents = weigh (fromIntegral . IntMap.size . tplNodes)
    instPorts = weigh (\t -> sum
      [ fromIntegral (IntMap.size (nodePorts nd)) | nd <- IntMap.elems (tplNodes t) ])
    bound e i perInput = sbScale (4 * copies)
      (sbConst (e + i) <> sbScale perInput (sbInput 0))
    ports = bound entryPorts instPorts

-- |Render the compositional estimate, naming the method and, when known, why
-- the walk gave nothing: the reader must know these figures are an estimate,
-- not a walked bound.
renderStaticIC :: Maybe String -> Resources SpaceBound -> String
renderStaticIC why = renderICSpaceCertificate Estimates
  [ "How it was computed: compositionally. The walk of the runtime's own"
  , "rules did not finish here" <> reason <> "."
  , "These figures instead charge every allocation the program's templates"
  , "allow, in any order of firing, times an estimated multiplier for"
  , "copying. Figures like these exist for every program, but they are"
  , "loose — often by many orders of magnitude — and not a proven bound:"
  , "the copy multiplier can undercount programs that copy code heavily,"
  , "such as towers of Church numerals. Read them as an order-of-growth"
  , "estimate, not as a guarantee or a prediction of the actual peak."
  ]
  where reason = maybe "" (\r -> " (" <> r <> ")") why

-- |Which analysis produced a stored certificate. The analyzer walks the net
-- and is close to the real peak where it finishes; the compositional
-- estimate always exists.
data ICMethod = ICAnalyzer | ICCompositional
  deriving (Eq, Show)

-- |A bound or estimate and its provenance, as `--ic --compile` stores it.
data ICCertificate = ICCertificate
  { certMethod :: ICMethod
  , certBounds :: Resources SpaceBound
  } deriving (Eq, Show)

-- |The best certificate available: the analyzer's bound when its walk
-- finishes, else the compositional estimate, which always exists. The string
-- says what happened, including why the walk gave nothing when it did.
icCertify :: EALLiftedResult -> ICProgram -> (ICCertificate, String)
icCertify eal prog = case analyzeIC defaultAnalysisBudget prog of
  outcome@(Established c) -> (ICCertificate ICAnalyzer c, renderICSpace outcome)
  Unknown why -> (ICCertificate ICCompositional bounds, renderStaticIC (Just why) bounds)
    where bounds = staticBound eal prog

-- |Render a certificate the way the analysis that made it would. A stored
-- certificate does not remember why the walk gave nothing, only that it did.
renderICCertificate :: ICCertificate -> String
renderICCertificate (ICCertificate ICAnalyzer c) = renderICSpace (Established c)
renderICCertificate (ICCertificate ICCompositional c) = renderStaticIC Nothing c
