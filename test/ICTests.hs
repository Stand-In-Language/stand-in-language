{-# LANGUAGE PatternSynonyms #-}
module Main where

import Control.Monad (forM_, replicateM)
import Control.Monad.Except (runExceptT)
import qualified Control.Monad.State.Strict as State
import Data.Bifunctor (first)
import qualified Data.IntMap.Strict as IntMap
import Data.List (isInfixOf, isPrefixOf, tails)
import qualified Data.Map as Map
import qualified System.IO.Strict as Strict
import Telomare.Driver (compileUnitTest)
import Telomare.EAL (CapShape (..), CodeGuidance (..), EALLiftedResult (..),
                     Step (..), ealCaptureLayouts, envUsageL, inferEALCompiled,
                     inferEALWithLifting)
import Telomare.Expand (expandModule, renderExpansionError)
import Telomare.IC
import Telomare.IC.Draw (DrawSummary (..), drawNet, drawProgram, netStats)
import Telomare.IC.Space
import Telomare.IR.Base (AbortableF (..), BasicExpr, pattern AbortB,
                         pattern AbortEE, pattern EnvB, pattern GateB,
                         pattern GateSwitchEE, pattern LeftB, pattern PairB,
                         pattern RightB, pattern SetEnvB, pattern ZeroB, varB)
import Telomare.IR.Core (AbstractRunTime (..), CompiledExpr, RunTimeError (..),
                         Term3, compiled2Term3)
import Telomare.Machine (abortInd, appB, deferB, iteB)
import Telomare.Parse (runParseModule)
import Telomare.Resolve (DeferMap (..), deferLift, main2Term3let)
import Test.Tasty
import Test.Tasty.HUnit

-- * Term construction helpers

z :: CompiledExpr
z = ZeroB

p :: CompiledExpr -> CompiledExpr -> CompiledExpr
p = PairB

se :: CompiledExpr -> CompiledExpr
se = SetEnvB

d :: Int -> CompiledExpr -> CompiledExpr
d = deferB

-- | Apply a closure pair (code, env) to an argument, through twiddle,
-- exactly as compiled applications do.
app :: CompiledExpr -> CompiledExpr -> CompiledExpr
app = appB

-- | @\\f x -> f (f x)@ as a closed closure: the church numeral two.
churchTwo :: CompiledExpr
churchTwo = p (d 20 (p (d 21 body) EnvB)) z where
  body = app (varB 1) (app (varB 1) (varB 0))

-- | A successor-shaped closure: @\\x -> (Zero, x)@.
succC :: CompiledExpr
succC = p (d 22 (p z (varB 0))) z

-- | Telomare-style numerals: n = (Zero, (Zero, ... Zero)).
num :: Int -> CompiledExpr
num 0 = z
num n = p z (num (n - 1))

-- | The abort message @(Zero, Zero)@ at the message type.
msgPair :: BasicExpr
msgPair = PairB ZeroB ZeroB

-- | Unapplied self-application is a value; applied to itself its level
-- equations demand an unbounded tower — EAL rejects it, and this runtime
-- runs out of fuel on it.
omegaApplied :: CompiledExpr
omegaApplied = se (p omega (p omega z)) where
  omega = d 1 (se (p (LeftB EnvB) EnvB))

-- * Assertion helpers

-- | The IC runtime and the reference evaluator must both produce exactly
-- this outcome.
expectTest :: String -> CompiledExpr -> Either RunTimeError CompiledExpr
           -> TestTree
expectTest name t v = testCase name $ do
  icEval t @?= v
  eval t @?= v

-- | The IC runtime must agree with the reference evaluator, whatever the
-- outcome.
diffTest :: String -> CompiledExpr -> TestTree
diffTest name t = icDiff name t (const (pure ()))

-- | 'diffTest' plus an extra check on the term.
icDiff :: String -> CompiledExpr -> (CompiledExpr -> Assertion) -> TestTree
icDiff name t extra = testCase name $ do
  icEval t @?= eval t
  extra t

-- | Occurrences of a marker in the rendered figure, overlapping ones included.
count :: String -> String -> Int
count needle = length . filter (needle `isPrefixOf`) . tails

main :: IO ()
main = do
  preludeFile <- Strict.readFile "Prelude.tel"
  let
    expandNamed name content =
      case runParseModule name content
             >>= first renderExpansionError . expandModule of
        Right m -> m
        Left e  -> error e
    prelude = [("Prelude", expandNamed "Prelude" preludeFile)]
    parseAuxModule str =
      ("AuxModule", expandNamed "AuxModule" ("import Prelude\n" <> str))
    parse :: String -> Either String Term3
    parse str =
      first show $ main2Term3let (parseAuxModule str : prelude) "AuxModule"
    -- compile a source program and evaluate it the way the unit-test
    -- corpus does: the compiled expression applied to a Zero env
    compiled :: String -> Either String CompiledExpr
    compiled src = do
      t3 <- parse src
      c <- first show (compileUnitTest t3)
      pure $ se (p (d 0 c) z)
    -- both evaluators must agree on the compiled program
    corpus :: String -> TestTree
    corpus src = testCase src $ case compiled src of
      Left e  -> assertFailure $ "compilation failed: " <> e
      Right t -> do
        icEval t @?= eval t
        prog <- either (\e -> assertFailure (show e) >> error "unreachable") pure
          (prepareIC mempty t)
        let outcome = analyzeIC defaultAnalysisBudget prog
            (_, measured) = runICProgram defaultFuel prog ZeroB
        case outcome of
          Unknown reason -> assertFailure ("closed corpus analysis: " <> reason)
          Established _ -> assertBool "whole-run resource bound" (certificateCovers ZeroB measured outcome)
  defaultMain $ testGroup "IC runtime"
    [ testGroup "net drawing"
        [ testCase "every agent and every wire is drawn exactly once" $ do
            let term = se (p (d 80 (p (LeftB EnvB) (RightB EnvB))) (p z z))
            prog <- either (\err -> assertFailure (show err) >> error "unreachable")
              pure (prepareIC mempty term)
            let nodes = icNodes (programInitial prog)
                (agents, wires) = netStats nodes
                svg = drawNet nodes
            assertBool "figure is an svg document" $
              "<svg" `isPrefixOf` svg && "</svg>" `isInfixOf` svg
            count "<g class=\"agent\">" svg @?= agents
            count "<line class=\"wire" svg + count "<circle class=\"wire\"" svg
              @?= wires
            forM_ (IntMap.keys nodes) $ \n ->
              assertBool ("agent #" <> show n <> " is labeled")
                (("#" <> show n <> "<") `isInfixOf` svg)
        , testCase "programs that differ only inside a template draw differently" $ do
            let withBody b = either (\err -> assertFailure (show err) >> error "unreachable")
                  pure (prepareIC mempty (se (p (d 80 b) (p z z))))
            split <- withBody (p (LeftB EnvB) (RightB EnvB))
            dup <- withBody (p EnvB EnvB)
            let entry = drawNet . icNodes . programInitial
            entry split @?= entry dup
            assertBool "template panels tell them apart"
              (fst (drawProgram "t" 400 split) /= fst (drawProgram "t" 400 dup))
        , testCase "every drawn template is drawn once, within the budget" $ do
            let body = se (p (d 80 (p (d 81 (LeftB EnvB)) (d 82 (p EnvB z)))) (p z z))
            prog <- either (\err -> assertFailure (show err) >> error "unreachable")
              pure (prepareIC mempty body)
            let st = programInitial prog
                tplAgents = sum [ IntMap.size (tplNodes t) | t <- IntMap.elems (icTemplates st) ]
                (svg, summary) = drawProgram "t" 400 prog
                (entryAgents, entryWires) = netStats (icNodes st)
                drawnWires = entryWires + sum
                  [ snd (netStats (tplNodes t))
                  | (tid, t) <- IntMap.toList (icTemplates st), tid > 2 ]
            drawnTemplates summary @?= reachableTemplates summary
            count "<g class=\"panel\"" svg @?= 1 + drawnTemplates summary
            count "<g class=\"agent\">" svg @?= entryAgents + drawnAgents summary
            count "<line class=\"wire" svg + count "<circle class=\"wire\"" svg
              @?= drawnWires
            assertBool "only reachable templates are counted"
              (totalAgents summary <= tplAgents)
            let (none, noneSummary) = drawProgram "t" 0 prog
            drawnTemplates noneSummary @?= 0
            count "<g class=\"panel\"" none @?= 1
            count "<g class=\"collapsed\"" none @?= min 12 (reachableTemplates noneSummary)
        , testCase "selector templates are left out of program drawings" $ do
            prog <- either (\err -> assertFailure (show err) >> error "unreachable")
              pure (prepareIC mempty (GateSwitchEE ZeroB (PairB ZeroB ZeroB) EnvB))
            let (svg, summary) = drawProgram "t" 400 prog
            reachableTemplates summary @?= 0
            assertBool "no selector panel" (not ("template #" `isInfixOf` svg))
        ]
    , testGroup "logical storage accounting"
        [ testCase "half wires, replacement, deletion and stale entries" $ do
            let action = do
                  a <- newNode ICEra
                  b <- newNode ICZero
                  setHalf (Port a 0) (Port b 0)
                  half <- State.gets icResident
                  connect (Port a 0) (Port b 0)
                  connect (Port a 0) (Port b 0)
                  deleteNode a
                  deleteNode a
                  before <- State.get
                  reduce
                  after <- State.get
                  pure (half, before, after)
                (result, _) = State.runState (runExceptT action) (emptyState mempty 10)
            case result of
              Left err -> assertFailure (show err)
              Right (half, before, after) -> do
                half @?= Resources 2 1 0
                icPeak before @?= Resources 2 2 2
                icResident before @?= Resources 1 1 2
                residentResources before @?= icResident before
                icResident after @?= Resources 1 1 0
                residentResources after @?= icResident after
        , testCase "template scratch is excluded and transient allocations count" $ do
            let action = do
                  _ <- newNode ICRoot
                  _ <- isolatedNet (replicateM 20 (newNode ICZero))
                  a <- newNode ICZero
                  b <- newNode ICZero
                  deleteNode a
                  deleteNode b
                (result, st) = State.runState (runExceptT action) (emptyState mempty 10)
            result @?= Right ()
            icPeak st @?= Resources 3 0 0
            icResident st @?= Resources 1 0 0
        , testCase "initialization and failed runs retain their peaks" $ do
            let (result, stats) = icEvalSpaceWith mempty 0 (se (p (d 90 EnvB) z))
            result @?= Left (ICFuelExhausted 0)
            resourceAgents (spacePeak stats) @?= 5
            resourcePorts (spacePeak stats) @?= 8
            resourceWork (spacePeak stats) @?= 1
        , testCase "runs and analyses exclude the preparation peak" $ do
            let body = se (p (d 2 (p EnvB EnvB)) EnvB)
            prog <- either (\e -> assertFailure (show e) >> error "unreachable") pure
              (prepareIC mempty body)
            let poisoned = prog { programInitial =
                  (programInitial prog) { icPeak = pure 999999 } }
                (result, measured) = runICProgram defaultFuel poisoned ZeroB
            result @?= fst (runICProgram defaultFuel prog ZeroB)
            spacePeak measured @?= spacePeak (snd (runICProgram defaultFuel prog ZeroB))
            assertBool "peak reset at run start"
              (resourceAgents (spacePeak measured) < 999999)
            analyzeIC defaultAnalysisBudget poisoned
              @?= analyzeIC defaultAnalysisBudget prog
        ]
    , testGroup "template namespace"
        [ testCase "prepared entry and templates are reusable across inputs" $ do
            let body = se (p (d 2 (p EnvB EnvB)) EnvB)
            prog <- either (\e -> assertFailure (show e) >> error "unreachable") pure
              (prepareIC mempty body)
            forM_ [ZeroB, PairB ZeroB ZeroB, PairB (PairB ZeroB ZeroB) ZeroB] $ \input -> do
              let (result, measured) = runICProgram defaultFuel prog input
                  expected = eval (se (p (d 3 body) (basicCompiled input)))
              icRuntimeResult result @?= expected
              assertBool "prepared templates retained" (resourceAgents (staticStorage prog) > 0)
              assertBool "execution measured" (resourceAgents (spacePeak measured) > 0)
        , testCase "deferHash agrees with the DeferMap key" $ do
            let dv = d 2 (p (LeftB EnvB) z)
                (DeferMap dm, _) = deferLift (compiled2Term3 dv)
            case (deferHash dv, Map.keys dm) of
              (Right h, [h']) -> h @?= h'
              other -> assertFailure $ "expected one shared hash, got "
                <> show other
        , testCase "equal bodies share one template (selectors included)" $ do
            -- both bodies equal doLeft's, so all three refs reuse the
            -- selector template and only the three reserved templates are
            -- ever compiled
            let term = p (se (p (d 2 (LeftB EnvB)) (p z z)))
                         (se (p (d 3 (LeftB EnvB)) (p z z)))
                (r, stats) = icEvalDetailed defaultFuel term
            r @?= Right (p z z)
            Map.lookup "template-compiled" stats @?= Just 3
            Map.lookup "template-reused" stats @?= Just 2
        , testCase "nested hashes retain the deferLift encoding" $ do
            let bodies = [z, EnvB, p EnvB z, AbortB,
                          AbortEE (AbortedF msgPair),
                          d 81 (LeftB EnvB),
                          p (d 82 (d 83 EnvB)) (d 84 (p EnvB EnvB))]
            forM_ bodies $ \body -> do
              let dv = d 80 body
                  (DeferMap dm, _) = deferLift (compiled2Term3 dv)
                  keys = [h | (h, (fi, _)) <- Map.toList dm, fi == toEnum 80]
              case keys of
                [h] -> deferHash dv @?= Right h
                _   -> assertFailure "outer body's hash missing"
        , testCase "deduped defers read back with their own index" $ do
            -- the result contains both defer values; sharing a template
            -- must not collapse their indexes (defer equality is by index)
            let body = p EnvB z
                term = p (d 2 body) (d 3 body)
            icEval term @?= eval term
            icEval term @?= Right term
        , testCase "bodies equal only modulo nested indexes stay separate" $ do
            -- outer bodies hash alike (the hash names nested defers by
            -- content) but differ by Eq, so each keeps its own template
            -- and readback stays exact
            let outer i j = d i (se (p (d j (LeftB EnvB)) EnvB))
                term = p (outer 2 10) (outer 3 11)
                (r, stats) = icEvalDetailed defaultFuel term
            r @?= Right term
            icEval term @?= eval term
            -- 3 selectors + 2 distinct outers; the nested bodies reuse
            -- the doLeft selector template
            Map.lookup "template-compiled" stats @?= Just 5
            Map.lookup "template-reused" stats @?= Just 2
        ]
    , testGroup "env splitting"
        [ testCase "disjoint projections split with no duplication" $ do
            let term = se (p (d 2 (p (LeftB EnvB) (RightB EnvB)))
                          (p z (p z z)))
                (r, stats) = icEvalDetailed defaultFuel term
            r @?= Right (p z (p z z))
            Map.lookup "split-pair" stats @?= Just 1
            Map.lookup "dup-pair" stats @?= Nothing
            Map.lookup "left-pair" stats @?= Nothing
            Map.lookup "right-pair" stats @?= Nothing
            Map.lookup "era-pair" stats @?= Nothing
        , testCase "whole-and-part use duplicates exactly once" $ do
            -- the whole env is copied (the analyzer's contraction), then
            -- one copy is split for the component
            let term = se (p (d 2 (p EnvB (LeftB EnvB))) (p z z))
                (r, stats) = icEvalDetailed defaultFuel term
            r @?= Right (p (p z z) z)
            Map.lookup "dup-pair" stats @?= Just 1
            Map.lookup "split-pair" stats @?= Just 1
        , expectTest "unused env component is erased, not projected"
            (se (p (d 2 (LeftB EnvB)) (p z (p z z)))) (Right z)
        , expectTest "deep disjoint paths route directly"
            (se (p (d 2 (p (LeftB (RightB EnvB))
                          (p (LeftB EnvB) (RightB (RightB EnvB)))))
                 (p z (p (p z z) z))))
            (Right (p (p z z) (p z z)))
        , diffTest "projections of a zero env"
            (se (p (d 2 (p (LeftB EnvB) (RightB EnvB))) z))
        , testCase "projections of a bare defer env are stuck" $
            -- (asserted on the net only: the reference evaluator is
            -- partial on a demanded projection of bare code)
            case icEval (se (p (d 2 (p (LeftB EnvB) (RightB EnvB)))
                             (d 9 z))) of
              Left (GenericRunTimeError msg _) -> assertBool
                ("stuck on shape, got: " <> msg)
                ("not a pair" `isInfixOf` msg)
              other -> assertFailure $
                "expected a stuck report, got " <> show other
        , diffTest "projections of an aborted env"
            (se (p (d 2 (p (LeftB EnvB) (RightB EnvB)))
                 (AbortEE (AbortedF msgPair))))
        , testCase "wiring consumes exactly the guidance-published usage" $ do
            let body = p (LeftB EnvB) (p (RightB (RightB EnvB)) (LeftB EnvB))
                lr = inferEALWithLifting (compiled2Term3 (d 2 body))
            case Map.elems (ealGuidance lr) of
              [Right cg] -> cgUsage cg @?= envUsage body
              other -> assertFailure $
                "expected one certified body, got " <> show other
        , testCase "usage adapters agree across projection and frame boundaries" $ do
            let leaves = [z, EnvB, LeftB EnvB, RightB (LeftB EnvB),
                          d 30 (p EnvB EnvB)]
                bodies = leaves <> [p a b | a <- leaves, b <- leaves]
                  <> [LeftB (p a b) | a <- leaves, b <- leaves]
                  <> [se (p (d 31 EnvB) a) | a <- leaves]
            forM_ bodies $ \body -> do
              envUsage body @?= (fmap fst . envUsageL . snd . deferLift $
                compiled2Term3 body)
              -- Compilation must consume exactly those occurrence wires.
              icEval (se (p (d 32 body) (p z (p z z))))
                @?= eval (se (p (d 32 body) (p z (p z z))))
            envPathOf (LeftB (RightB EnvB)) @?= Just [SR, SL]
            envPathOf (LeftB (p EnvB z)) @?= Nothing
        ]
    , testGroup "closure dup plans"
        [ testCase "inaccurate capture layouts preserve results" $ do
            let code = d 5 (LeftB EnvB)
                captures = [p z z, p (d 7 EnvB) z,
                            p (p (d 8 (p EnvB z)) z) (p z z)]
                shapes = [CapData, CapCode, CapPair CapCode CapData,
                          CapPair (CapPair CapData CapCode) CapCode, CapOther]
            h <- either assertFailure pure (deferHash code)
            forM_ captures $ \capture -> do
              let clo = p code capture
                  term = se (p (d 1 (p EnvB EnvB)) clo)
                  expected = Right (p clo clo)
              icEval term @?= expected
              eval term @?= expected
              forM_ shapes $ \shape -> do
                let (r, stats) = icEvalDetailedWith (Map.singleton h shape)
                      defaultFuel term
                r @?= expected
                assertBool "supplied layout was exercised"
                  (Map.findWithDefault 0 "dup-closure" stats > 0)
        , testCase "guided duplication copies the closure skeleton" $ do
            -- a data-captured closure applied twice: its dup meets the
            -- closure pair, and with a layout the whole skeleton (ref,
            -- capture pair, zeros) copies in one interaction
            let clo = p (d 5 (LeftB EnvB)) (p z z)
                body = p (app EnvB (p z z)) (app EnvB (p z z))
                term = se (p (d 1 body) clo)
                layouts = ealCaptureLayouts
                  (inferEALWithLifting (compiled2Term3 term))
                (r, stats) = icEvalDetailedWith layouts defaultFuel term
                (r0, stats0) = icEvalDetailed defaultFuel term
            assertBool "has layouts" (not (Map.null layouts))
            -- guided and generic runs agree, and match the reference
            r @?= r0
            r @?= Right (p (p z z) (p z z))
            icEval term @?= eval term
            -- the guided run replaced the fan cascade
            assertBool "plan fired"
              (Map.findWithDefault 0 "dup-closure" stats > 0)
            assertBool "skeleton copied"
              (Map.findWithDefault 0 "dup-plan-copy" stats > 0)
            Map.lookup "dup-pair" stats @?= Nothing
            Map.lookup "dup-leaf" stats @?= Nothing
            -- the generic run paid the cascade the plan avoided
            assertBool "generic cascade present"
              (Map.findWithDefault 0 "dup-pair" stats0 > 0)
        , testCase "guided run agrees on a real program" $
            case parse "main = take $5 [1,2,3]" of
              Left e -> assertFailure $ "parse failed: " <> e
              Right t3 -> case compileUnitTest t3 of
                Left e -> assertFailure $ "compile failed: " <> show e
                Right c -> do
                  let t = se (p (d 0 c) z)
                      layouts = ealCaptureLayouts (inferEALCompiled c)
                      (r, stats) = icEvalDetailedWith layouts defaultFuel t
                      (r0, _) = icEvalDetailed defaultFuel t
                  assertBool "has layouts" (not (Map.null layouts))
                  r @?= r0
                  assertBool "plan fired on real closures"
                    (Map.findWithDefault 0 "dup-closure" stats > 0)
        -- the CLI's route: prepare once under the EAL layouts, run inputs
        , testCase "guided preparation agrees with generic across inputs" $
            case parse "main = take $5 [1,2,3]" of
              Left e -> assertFailure $ "parse failed: " <> e
              Right t3 -> case compileUnitTest t3 of
                Left e -> assertFailure $ "compile failed: " <> show e
                Right c -> do
                  let layouts = ealCaptureLayouts (inferEALCompiled c)
                      body = appB c EnvB
                      prep = either (\e -> assertFailure (show e)
                                       >> error "unreachable") pure
                  assertBool "has layouts" (not (Map.null layouts))
                  guided <- prep (prepareIC layouts body)
                  generic <- prep (prepareIC mempty body)
                  forM_ [ZeroB, PairB ZeroB ZeroB,
                         PairB (PairB ZeroB ZeroB) ZeroB] $ \input ->
                    fst (runICProgram defaultFuel guided input)
                      @?= fst (runICProgram defaultFuel generic input)
        ]
    , testGroup "application"
        [ expectTest "identity defer" (se (p (d 100 EnvB) z)) (Right z)
        , expectTest "constant body erases its env"
            (se (p (d 107 z) (p z z))) (Right z)
        , expectTest "application through twiddle"
            (app (p (d 106 (LeftB EnvB)) z) (p z z)) (Right (p z z))
        , expectTest "closure returning a closure"
            (se (p (d 108 (p (d 109 (LeftB EnvB)) EnvB)) z))
            (Right (p (d 109 (LeftB EnvB)) z))
        ]
    , testGroup "projection"
        [ expectTest "left of pair" (LeftB (p (p z z) z)) (Right (p z z))
        , expectTest "right of pair" (RightB (p (p z z) z)) (Right z)
        , expectTest "left of zero" (LeftB z) (Right z)
        , expectTest "projection of computed pair"
            (LeftB (se (p (d 112 EnvB) (p z (p z z))))) (Right z)
        ]
    , testGroup "duplication"
        [ expectTest "env used twice duplicates data"
            (se (p (d 101 (p EnvB EnvB)) (p z z)))
            (Right (p (p z z) (p z z)))
        , expectTest "env used twice duplicates a defer by reference"
            (se (p (d 102 (p EnvB EnvB)) (d 103 EnvB)))
            (Right (p (d 103 EnvB) (d 103 EnvB)))
        , expectTest "shared defer applied to two different arguments"
            (se (p (d 110 (p (se (p EnvB z)) (se (p EnvB (p z z)))))
                   (d 111 EnvB)))
            (Right (p z (p z z)))
        ]
    , testGroup "gates"
        [ expectTest "zero selects the left branch"
            (GateSwitchEE (p z z) z z) (Right (p z z))
        , expectTest "pair selects the right branch"
            (GateSwitchEE (p z z) z (p z z)) (Right z)
        , expectTest "discarded branch may be a closure"
            (GateSwitchEE (d 105 EnvB) z (p z z)) (Right z)
        , diffTest "scrutinee is computed"
            (GateSwitchEE z (p z z) (se (p (d 113 EnvB) (p z z))))
        ]
    , testGroup "abort"
        [ expectTest "abort of zero is the identity continuation"
            (se (p AbortB z)) (Right (d abortInd EnvB))
        , expectTest "the abort continuation passes its env through"
            (se (p (se (p AbortB z)) (p z z))) (Right (p z z))
        , expectTest "abort of a pair aborts with that message"
            (se (p AbortB (p z z))) (Left (AbortRunTime msgPair))
        , expectTest "aborted values poison projections"
            (LeftB (se (p AbortB (p z z)))) (Left (AbortRunTime msgPair))
        , expectTest "a discarded aborted value is no abort"
            (GateSwitchEE z (LeftB (se (p AbortB (p z z)))) z) (Right z)
        ]
    , testGroup "church numerals"
        [ expectTest "two applications of successor"
            (app (app churchTwo succC) z) (Right (num 2))
        , expectTest "iterated composition: two of (two of successor)"
            (app (app churchTwo (app churchTwo succC)) z) (Right (num 4))
        , diffTest "three levels of composition"
            (app (app churchTwo (app churchTwo (app churchTwo succC))) z)
        ]
    , testGroup "runtime machinery"
        [ testCase "interaction counts are reported" $ do
            let (r, stats) =
                  icEvalDetailed defaultFuel (app (app churchTwo succC) z)
            either (assertFailure . show) (const (pure ())) r
            assertBool "apply-ref fired"
              (maybe False (> 0) (Map.lookup "apply-ref" stats))
        , testCase "fuel exhaustion is reported" $
            case fst (icEvalDetailed 3 (app (app churchTwo succC) z)) of
              Left (ICFuelExhausted _) -> pure ()
              r -> assertFailure $ "expected fuel exhaustion, got " <> show r
        ]
    , testGroup "compiled program corpus (IC vs reference evaluator)"
        [ corpus "main = 0"
        , corpus "main = succ 0"
        , corpus "main = (\\f x -> f (f (f x))) ((\\f x -> f (f x)) succ) 0"
        , corpus "main = plus $3 $2 succ 0"
        , corpus "main = times $3 $2 succ 0"
        , corpus "main = dEqual 2 1"
        , corpus "main = dEqual 2 2"
        , corpus "main = listLength [1,2,3]"
        , corpus "main = listPlus [1,2] [3,4]"
        , corpus "main = listEqual \"ab\" \"ab\""
        , corpus "main = map left [1,2]"
        , corpus "main = foldr (\\a b -> plus (d2c a) (d2c b) succ 0) 1 [2,4,6]"
        , corpus "main = take $5 [1,2,3]"
        , corpus "main = c2d (minus $4 $3)"
        , corpus ("main = let f = \\a b -> (a,b)\n"
               <> "           g = if 1 then f 1 else left\n"
               <> "       in g 1")
        , corpus ("main = let layer = \\recur x -> recur (x, 0)\n"
               <> "       in $3 layer (\\x -> x) 0")
        ]
    , testGroup "branch laziness (iteB vs iteB_)"
        [ expectTest "lazy ite never instantiates a diverging dead branch"
            -- iteB defers each branch, so the unselected else-branch (which
            -- would diverge) is an erased ref the net never fires
            (se (p (d 200 (iteB (p z z) (LeftB EnvB) omegaApplied))
                   (p z z)))
            (Right z)
        , testCase "strict ite speculates: a diverging dead branch is fuel death" $ do
            -- iteB_-style raw branches are fired eagerly by the net (the
            -- price of speculation); the lazy reference evaluator skips
            -- them, so this is a deliberate, documented divergence
            let strict = se (p (d 201 (se (p (se (p GateB (p z z)))
                                            (p omegaApplied (LeftB EnvB)))))
                             (p z z))
            eval strict @?= Right z
            case fst (icEvalDetailed 50000 strict) of
              Left (ICFuelExhausted _) -> pure ()
              r -> assertFailure $ "expected fuel exhaustion, got " <> show r
        , expectTest "strict ite with a stuck dead branch still agrees"
            -- bounded dead code is fine under speculation: the stuck value
            -- is erased with the unselected branch
            (se (p (d 202 (se (p (se (p GateB (p z z)))
                                (p (se (p (p z z) z)) (LeftB EnvB)))))
                  (p z z)))
            (Right z)
        ]
    , testGroup "EAL boundary experiments"
        [ testCase "EAL-certified numeral composition: runtime agrees" $
            -- numeral-of-numeral composition ($3 applied to $2) needs a
            -- level per composition rung; per-apply-site dispatch
            -- expresses that, so the certificate now covers the program
            -- the abstract algorithm was already computing correctly
            case parse "main = $3 $2 succ 0" of
              Left e -> assertFailure $ "parse failed: " <> e
              Right t3 -> do
                case ealLiftedMain (inferEALWithLifting t3) of
                  Right _ -> pure ()
                  Left e -> assertFailure $
                    "expected EAL acceptance, got " <> show e
                case compiled "main = $3 $2 succ 0" of
                  Left e  -> assertFailure $ "compilation failed: " <> e
                  Right t -> icEval t @?= eval t
        , testCase "EAL-rejected and diverging: runtime runs out of fuel" $
            -- omega omega: the reference evaluator would hang, EAL rejects
            -- at the level cap, and the net reduction never quiesces
            case fst (icEvalDetailed 100000 omegaApplied) of
              Left (ICFuelExhausted _) -> pure ()
              r -> assertFailure $ "expected divergence, got " <> show r
        ]
    ]

basicCompiled :: BasicExpr -> CompiledExpr
basicCompiled ZeroB       = ZeroB
basicCompiled (PairB a b) = PairB (basicCompiled a) (basicCompiled b)
basicCompiled _           = error "non-data BasicExpr"
