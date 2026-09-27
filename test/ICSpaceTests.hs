{- HLINT ignore "Monoid law, left identity" -}
module Main where

import Control.Applicative (liftA2)
import Control.Monad (forM_)
import Control.Monad.Except (runExceptT)
import qualified Control.Monad.State.Strict as State
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Numeric.Natural (Natural)
import Telomare.EAL (CapShape (..), inferEALCompiled)
import Telomare.IC
import Telomare.IC.Space
import Telomare.IC.Static
import Telomare.IR.Base
import Telomare.IR.Core (CompiledExpr)
import Telomare.Machine (appB, deferB)
import Telomare.SpaceBound
import Test.Tasty
import Test.Tasty.HUnit

main :: IO ()
main = defaultMain $ testGroup "IC space"
  [ testGroup "bound laws"
      [ testCase "addition, maximum and widening are pointwise sound" .
          forM_ bounds $ \a -> forM_ bounds $ \b -> forM_ [0..12] $ \size -> do
            let at = sbEvaluate (const size)
            at (a <> b) @?= at a + at b
            at (sbMax a b) @?= max (at a) (at b)
            at (sbWiden 1 (sbMax a b)) >= at (sbMax a b) @? "widening bounds both"
      , testCase "normalization does not widen implicitly" $ do
          let SpaceBound xs = norm [Affine (Map.singleton 0 n) (30-n) | n <- [0..30]]
          length xs @?= 31
      , testCase "unknown cannot validate a measurement" $
          certificateCovers ZeroB mempty (Unknown "test") @?= False
      , testCase "coefficients use arbitrary precision" $ do
          let huge = 10 ^ (100 :: Int)
          sbEvaluate (const 0) (sbConst huge <> sbConst huge) @?= 2*huge
      ]
  , testGroup "rendering"
      [ testCase "figures of at most six digits are exact, larger ones round up" $ do
          renderNatUp 999999 @?= "999999"
          renderNatUp 1000000 @?= "1.00×10^6"
          renderNatUp 9999999 @?= "1.00×10^7"
          renderNatUp 477544804096 @?= "4.78×10^11"
          forM_ [0, 7, 999999, 1000000, 1000001, 123456789, 477544804096,
                 10 ^ (100 :: Int), 10 ^ (100 :: Int) + 1] $ \n ->
            assertBool (show n <> " rendered below itself")
              (renderedValue (renderNatUp n) >= n)
      , testCase "deep paths fold, short paths stay in words" $ do
          renderPath 0 @?= "input"
          renderPath (pathTo "lll") @?= "input.left.left.left"
          renderPath (pathTo (replicate 60 'l')) @?= "input.left×60"
          renderPath (pathTo ("lrr" <> replicate 60 'l')) @?= "input.left.right.right.left×60"
      , testCase "the whole-input headline dominates every case" .
          forM_ (bounds <> shapedBounds) $ \b -> forM_ [0..12] $ \size ->
            forM_ [const size, \p -> if p == 0 then size else min size 3] $ \val ->
              assertBool (renderSpaceBound b) $
                sbEvaluate val (SpaceBound [sbHeadline b]) >= sbEvaluate val b
      ]
  , testGroup "all finite data contracts" $ fmap fixture dataFixtures
  , testGroup "generated projection and duplication combinations" $
      fmap fixture generatedFixtures
  , testCase "budget exhaustion is explicit, never a partial bound" $ do
      prog <- prepared (SetEnvB (PairB (deferB 80 EnvB) EnvB))
      case analyzeIC (AnalysisBudget 0 1) prog of
        Unknown _     -> pure ()
        Established _ -> assertFailure "budget exhaustion certified"
  , testCase "session statistics obey identity and associate" $ do
      prog <- prepared EnvB
      let a = snd (runICProgram defaultFuel prog ZeroB)
          b = snd (runICProgram defaultFuel prog (PairB ZeroB ZeroB))
      a <> mempty @?= a
      mempty <> a @?= a
      (a <> b) <> a @?= a <> (b <> a)
  , testCase "hand-traced splitting, copying and erasure peaks include temporary fans" .
      forM_ [(ICSplit, Resources 6 12 1), (ICDup 0, Resources 8 18 2),
             (ICEra, Resources 4 6 2)] $ \(consumer, expected) -> do
        let build = do
              c <- newNode consumer
              case consumer of
                ICEra -> pure ()
                _ -> do
                  root <- newNode ICRoot
                  pair <- newNode ICPair
                  connect (Port root 0) (Port pair 0)
                  connect (Port pair 1) (Port c 1)
                  connect (Port pair 2) (Port c 2)
              value <- compileData (PairB ZeroB ZeroB)
              connect (Port c 0) value
              reduce
            (result, st) = State.runState (runExceptT build) (emptyState mempty 100)
        result @?= Right ()
        icPeak st @?= expected
        icResident st @?= residentResources st
  , testCase "repeated tests of one input part fork once and stay covered" $ do
      let test = GateSwitchEE ZeroB (PairB ZeroB ZeroB) EnvB
      prog <- prepared (GateSwitchEE test test EnvB)
      let (outcome, stats) = analyzeICDetailed defaultAnalysisBudget prog
      case outcome of
        Unknown reason -> assertFailure reason
        Established _  -> statForks stats @?= 1
      forM_ finiteInputs $ \input -> do
        let (_, measured) = runICProgram defaultFuel prog input
        assertBool (show input <> " " <> show measured <> " " <> renderICSpace outcome)
          (certificateCovers input measured outcome)
  , testCase "projections, copies and erasures of regions never fork" $ do
      prog <- prepared (SetEnvB (PairB (deferB 80 (PairB (LeftB EnvB) (PairB (RightB EnvB) EnvB))) EnvB))
      let (outcome, stats) = analyzeICDetailed defaultAnalysisBudget prog
      case outcome of
        Unknown reason -> assertFailure reason
        Established _  -> statForks stats @?= 0
  , testCase "guided copying of concrete regions, including inaccurate guidance, has finite bounds" $ do
      let code = deferB 20 (LeftB EnvB)
          closure = PairB code (PairB ZeroB (PairB ZeroB ZeroB))
          body = SetEnvB (PairB (deferB 21 (PairB EnvB EnvB)) closure)
      h <- either (\e -> assertFailure (show e) >> error "unreachable") pure (deferHash code)
      forM_ [CapData, CapCode, CapPair CapCode CapData, CapOther] $ \shape -> do
        prog <- either (\e -> assertFailure (show e) >> error "unreachable") pure
          (prepareIC (Map.singleton h shape) body)
        let outcome = analyzeIC defaultAnalysisBudget prog
            (result, measured) = runICProgram defaultFuel prog ZeroB
        result @?= Right (PairB closure closure)
        assertBool "guided copying was executed" (Map.findWithDefault 0 "dup-plan-copy" (spaceRules measured) > 0)
        assertBool (renderICSpace outcome) (certificateCovers ZeroB measured outcome)
  , testGroup "compositional estimate"
      [ testCase "covers the measured peak of every fixture on every finite input" .
          forM_ allFixtures $ \(name, body) -> do
            prog <- prepared body
            let bounds = staticBound (inferEALCompiled body) prog
            forM_ finiteInputs $ \input -> do
              let (_, measured) = runICProgram defaultFuel prog input
                  at = sbEvaluate
                    (\p -> Map.findWithDefault 0 p (inputSizes input))
              assertBool (name <> " input " <> show input
                <> " peaks " <> show (spacePeak measured))
                (and (liftA2 (\actual b -> at b >= actual) (spacePeak measured) bounds))
      , testCase "instantiation counts bound the measured apply-ref firings" .
          forM_ allFixtures $ \(name, body) -> do
            prog <- prepared body
            let eal = inferEALCompiled body
                copies = copyMultiplier eal prog (staticInstBounds 1 prog)
                predicted = staticInstBounds copies prog
            forM_ finiteInputs $ \input -> do
              let (_, measured) = runICProgram defaultFuel prog input
              forM_ (IntMap.toList (spaceInsts measured)) $ \(tid, count) ->
                assertBool (name <> " template " <> show tid <> " fired " <> show count)
                  (fromIntegral count <= IntMap.findWithDefault 0 tid predicted)
      , testCase "a straight-line instantiation is predicted exactly" $ do
          let body = SetEnvB (PairB (deferB 80 (PairB EnvB EnvB)) EnvB)
          prog <- prepared body
          -- no fans anywhere, so the copy-free walk is the truth
          let predicted = staticInstBounds 1 prog
              (_, measured) = runICProgram defaultFuel prog ZeroB
          assertBool "an instantiation fired" (not (IntMap.null (spaceInsts measured)))
          forM_ (IntMap.toList (spaceInsts measured)) $ \(tid, count) ->
            IntMap.findWithDefault 0 tid predicted @?= fromIntegral count
      , testCase "the walk's established bound is never above the compositional estimate" .
          forM_ allFixtures $ \(name, body) -> do
            prog <- prepared body
            let compositional = staticBound (inferEALCompiled body) prog
            case analyzeIC defaultAnalysisBudget prog of
              Unknown _ -> pure ()
              Established walked -> forM_ finiteInputs $ \input -> do
                let at = sbEvaluate
                      (\p -> Map.findWithDefault 0 p (inputSizes input))
                assertBool (name <> " at " <> show input)
                  (and (liftA2 (\w c -> at w <= at c) walked compositional))
      ]
  , testCase "guided copying at opaque frontiers is covered by the generic copy" $ do
      let code = deferB 20 (LeftB EnvB)
          call = appB EnvB ZeroB
          body = SetEnvB (PairB (deferB 21 (PairB call call)) (PairB code EnvB))
      h <- either (\e -> assertFailure (show e) >> error "unreachable") pure (deferHash code)
      prog <- either (\e -> assertFailure (show e) >> error "unreachable") pure
        (prepareIC (Map.singleton h CapData) body)
      let outcome = analyzeIC defaultAnalysisBudget prog
      case outcome of
        Unknown reason -> assertFailure reason
        Established _  -> forM_ finiteInputs $ \input -> do
          let (_, measured) = runICProgram defaultFuel prog input
          assertBool (show input <> " " <> show measured <> " " <> renderICSpace outcome)
            (certificateCovers input measured outcome)
  ]
  where
    bounds = [sbConst 0, sbConst 7, sbInput 0, sbScale 3 (sbInput 0) <> sbConst 2,
              sbMax (sbConst 8) (sbScale 2 (sbInput 0))]
    shapedBounds = [sbInput 1 <> sbInput 2 <> sbConst 5,
                    sbMax (sbScale 4 (sbInput 3)) (sbInput 0 <> sbConst 9)]
    pathTo = foldl (\p c -> if c == 'l' then 2*p+1 else 2*p+2) (0 :: Integer)
    dataFixtures =
      [ ("identity", EnvB)
      , ("erasure", ZeroB)
      , ("duplication", PairB EnvB EnvB)
      , ("split", PairB (LeftB EnvB) (RightB EnvB))
      , ("deep projection", LeftB (RightB EnvB))
      , ("template instantiation", SetEnvB (PairB (deferB 80 (PairB EnvB EnvB)) EnvB))
      , ("discarded stuck", GateSwitchEE ZeroB (SetEnvB (PairB ZeroB EnvB)) ZeroB)
      , ("discarded abort", GateSwitchEE ZeroB (SetEnvB (PairB AbortB EnvB)) ZeroB)
      , ("speculative branch", GateSwitchEE (PairB EnvB EnvB) (PairB EnvB ZeroB) (LeftB EnvB))
      ]
    generatedFixtures =
      [ (show (i,j), SetEnvB (PairB (deferB 90 (PairB EnvB EnvB)) (PairB a b)))
      | (i,a) <- zip [0 :: Int ..] [EnvB, LeftB EnvB, RightB EnvB, ZeroB]
      , (j,b) <- zip [0 :: Int ..] [EnvB, LeftB EnvB, RightB EnvB, ZeroB]]
    allFixtures = dataFixtures <> generatedFixtures

prepared :: CompiledExpr -> IO ICProgram
prepared body = either (\e -> assertFailure (show e) >> error "unreachable") pure
  (prepareIC mempty body)

fixture :: (String, CompiledExpr) -> TestTree
fixture (name, body) = testCase name $ do
  prog <- prepared body
  let outcome = analyzeIC defaultAnalysisBudget prog
  case outcome of
    Unknown reason -> assertFailure (name <> ": " <> reason)
    Established _ -> forM_ finiteInputs $ \input -> do
      let (_, measured) = runICProgram defaultFuel prog input
      assertBool (name <> " input " <> show input <> " peaks " <> show measured
        <> " bound " <> renderICSpace outcome)
        (certificateCovers input measured outcome)

-- |The figure a rendered figure stands for: @4.78×10^11@ is 478000000000.
renderedValue :: String -> Natural
renderedValue s = case break (== '×') s of
  (m, "") -> read m
  (m, _times : power) ->
    let (whole, frac) = fmap (drop 1) (break (== '.') m)
        expn = read (drop (length "10^") power) - length frac :: Int
    in read (whole <> frac) * 10 ^ expn

finiteInputs :: [BasicExpr]
finiteInputs = trees 4 <> [chain 60, PairB (chain 25) (chain 25)]
  where
    trees :: Int -> [BasicExpr]
    trees 0 = [ZeroB]
    trees n = ZeroB : [PairB a b | i <- [0..n-1], a <- trees i, b <- trees (n-1-i)]
    chain :: Int -> BasicExpr
    chain 0 = ZeroB
    chain n = PairB ZeroB (chain (n-1))
