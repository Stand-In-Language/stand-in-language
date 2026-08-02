
-- |The two ways to run a program that are not "size it, then run it": from an
-- artifact that was sized earlier, and without sizing at all.
--
-- Both are only worth having if they compute what the sized run computes, so
-- that is what most of this checks.
module RunModeTests where

import qualified Data.ByteString.Lazy.Char8 as BL
import Data.List (isInfixOf)
import qualified Data.Map as Map
import qualified System.IO.Strict as Strict
import Test.Hspec

import Telomare.Artifact (Artifact (..), decodeArtifact, encodeArtifact,
                          nodeCount, sourcesHash)
import Telomare.Certificate (renderStaticReport)
import Telomare.Error
import Telomare.Driver (compileModules, runMainWithInput)
import Telomare.Fast (FastError (..), FastMeter (..), compileFast,
                      runFastWithInput)
import Telomare.IR.Base
import Telomare.IR.Builder
import Telomare.IR.Core
import Telomare.IR.Loc
import Telomare.IR.Surface
import Telomare.IR.Types
import Telomare.Levels (LevelsInfo (..), levelsInfo)
import Telomare.Machine (appB)
import Telomare.Size (SizingReport (..))
import Telomare.Size.IR (SizedRecursion (..))

limitsDir :: FilePath
limitsDir = "test/programs/limits/"

-- |A program plus the prelude, as the CLI would load them.
loadWith :: FilePath -> String -> IO [(String, String)]
loadWith path moduleName = do
  prelude <- Strict.readFile "Prelude.tel"
  source <- Strict.readFile path
  pure [("Prelude", prelude), (moduleName, source)]

runModeSpec :: Spec
runModeSpec = do
  describe "a compiled artifact" $ do
    it "round-trips through its encoding" $ do
      modules <- loadWith "simpleplus.tel" "simpleplus"
      case compileModules modules "simpleplus" of
        Left err -> expectationFailure $ "failed to compile simpleplus.tel:\n" <> err
        Right (report, sized) -> do
          let artifact = Artifact
                { artifactEntry = "simpleplus"
                , artifactSourceHash = sourcesHash modules
                , artifactReport = report
                , artifactCertificate = "the certificate text"
                , artifactExpr = sized
                }
          case decodeArtifact (encodeArtifact artifact) of
            Left err -> expectationFailure $ "failed to decode:\n" <> err
            Right back -> do
              -- The program itself must survive exactly: this is what will run.
              artifactExpr back `shouldBe` sized
              artifactEntry back `shouldBe` "simpleplus"
              artifactSourceHash back `shouldBe` sourcesHash modules
              artifactCertificate back `shouldBe` "the certificate text"
              -- And the sizing results, which is the point of storing it at
              -- all: reporting them again must not need a second sizing run.
              unSizedRecursion (sizingReportCounts (artifactReport back))
                `shouldBe` unSizedRecursion (sizingReportCounts report)
              sizingReportLocs (artifactReport back) `shouldBe` sizingReportLocs report
              sizingReportBudget (artifactReport back) `shouldBe` sizingReportBudget report

    it "evaluates to what the program it came from evaluates to" $ do
      modules <- loadWith "tc_ultra_minimal.tel" "tc_ultra_minimal"
      case compileModules modules "tc_ultra_minimal" of
        Left err -> expectationFailure $ "failed to compile:\n" <> err
        Right (report, sized) -> do
          let artifact = Artifact "tc_ultra_minimal" (sourcesHash modules) report "" sized
          case decodeArtifact (encodeArtifact artifact) of
            Left err -> expectationFailure $ "failed to decode:\n" <> err
            Right back ->
              fmap show (eval (appB (artifactExpr back) ZeroB))
                `shouldBe` fmap show (eval (appB sized ZeroB))

    it "refuses a file that is not one, rather than misreading it" $ do
      isLeftContaining "magic" (decodeArtifact (BL.pack "not a telomare artifact at all"))
        `shouldBe` True

    it "notices when the sources it was compiled from change" $ do
      modules <- loadWith "simpleplus.tel" "simpleplus"
      let changed = ("simpleplus", "main = \\input -> (\"different\", 0)")
            : filter ((/= "simpleplus") . fst) modules
      sourcesHash changed `shouldNotBe` sourcesHash modules
      -- Order must not matter: modules are discovered in import order.
      sourcesHash (reverse modules) `shouldBe` sourcesHash modules

  describe "running without sizing" $ do
    it "produces the same transcript as the sized run" $ do
      modules <- loadWith "simpleplus.tel" "simpleplus"
      expected <- runMainWithInput ["3 4"] modules "simpleplus"
      case compileFast modules "simpleplus" of
        Left err -> expectationFailure $ "failed to compile without sizing:\n" <> err
        Right prog -> case snd (runFastWithInput Nothing ["3 4"] prog) of
          Left e       -> expectationFailure $ "fast run failed: " <> show e
          Right actual -> actual `shouldBe` expected

    it "produces the same transcript on a program with no input" $ do
      modules <- loadWith "tc_ultra_minimal.tel" "tc_ultra_minimal"
      expected <- runMainWithInput [] modules "tc_ultra_minimal"
      case compileFast modules "tc_ultra_minimal" of
        Left err -> expectationFailure $ "failed to compile without sizing:\n" <> err
        Right prog -> case snd (runFastWithInput Nothing [] prog) of
          Left e       -> expectationFailure $ "fast run failed: " <> show e
          Right actual -> actual `shouldBe` expected

    it "counts the unrolls of each recursion site separately" $ do
      modules <- loadWith "simpleplus.tel" "simpleplus"
      case compileFast modules "simpleplus" of
        Left err -> expectationFailure $ "failed to compile without sizing:\n" <> err
        Right prog -> do
          let (measured, _) = runFastWithInput Nothing ["3 4"] prog
          -- simpleplus recurses in the prelude and in its own doAdd.
          Map.size (fmUnrolls measured) `shouldSatisfy` (> 1)
          fmApplies measured `shouldSatisfy` (> 0)
          sum (Map.elems (fmUnrolls measured)) `shouldSatisfy` (> 0)

    it "runs a program the sizing pass rejects" $ do
      modules <- loadWith (limitsDir <> "unbounded-input-recursion.tel")
        "unbounded-input-recursion"
      -- Still rejected the usual way: this is the program's whole point.
      isLeft (compileModules modules "unbounded-input-recursion") `shouldBe` True
      case compileFast modules "unbounded-input-recursion" of
        Left err -> expectationFailure $ "failed to compile without sizing:\n" <> err
        Right prog -> case snd (runFastWithInput Nothing ["a"] prog) of
          Left e           -> expectationFailure $ "fast run failed: " <> show e
          Right transcript -> transcript `shouldSatisfy` isInfixOf "done"

    it "stops on the fuel cap instead of running forever" $ do
      modules <- loadWith "simpleplus.tel" "simpleplus"
      case compileFast modules "simpleplus" of
        Left err -> expectationFailure $ "failed to compile without sizing:\n" <> err
        Right prog -> do
          -- Far less fuel than the program needs, so the cap must be what stops it.
          snd (runFastWithInput (Just 20) ["3 4"] prog)
            `shouldSatisfy` isOutOfFuel
          -- And with no cap it finishes, so the cap is the only difference.
          snd (runFastWithInput Nothing ["3 4"] prog) `shouldSatisfy` isRight

  describe "the static report" $ do
    it "reports the structural analysis with no sizing at all" $ do
      modules <- loadWith "simpleplus.tel" "simpleplus"
      let levels = levelsInfo modules "simpleplus"
          report = renderStaticReport Nothing Nothing levels
      case levels of
        Left err -> expectationFailure $ "structural analysis failed:\n" <> err
        Right info -> do
          levelsSites info `shouldSatisfy` not . null
          -- d2c's recursion is reached from under foldr's, so the nesting is
          -- deeper than one level; a flat answer would mean the walk is not
          -- following calls.
          levelsMaxDepth info `shouldSatisfy` (> 1)
      report `shouldSatisfy` isInfixOf "recursion nesting"
      report `shouldSatisfy` isInfixOf "was not sized"

    it "reports both analyses, and that they do not line up" $ do
      modules <- loadWith "simpleplus.tel" "simpleplus"
      case compileModules modules "simpleplus" of
        Left err -> expectationFailure $ "failed to compile simpleplus.tel:\n" <> err
        Right (sizing, _) -> do
          let report = renderStaticReport (Just "somehash") (Just sizing)
                (levelsInfo modules "simpleplus")
          report `shouldSatisfy` isInfixOf "somehash"
          report `shouldSatisfy` isInfixOf "recursion sites (iterations, over every input)"
          report `shouldSatisfy` isInfixOf "recursion nesting"
          report `shouldSatisfy` isInfixOf "65536"
          -- Sizing counts instantiations and the structural pass counts written
          -- triples, so the report must not invite reading them as one table.
          report `shouldSatisfy` isInfixOf "do not line up row by row"

    it "gives a sized program's nodes a count worth reporting" $ do
      modules <- loadWith "simpleplus.tel" "simpleplus"
      case compileModules modules "simpleplus" of
        Left err -> expectationFailure $ "failed to compile simpleplus.tel:\n" <> err
        -- Sizing bakes iteration counts in as towers, so the compiled program
        -- is far bigger than its source.
        Right (_, sized) -> nodeCount sized `shouldSatisfy` (> 1000)

isLeft :: Either a b -> Bool
isLeft = either (const True) (const False)

isRight :: Either a b -> Bool
isRight = either (const False) (const True)

isLeftContaining :: String -> Either String a -> Bool
isLeftContaining needle = either (isInfixOf needle) (const False)

isOutOfFuel :: Either FastError a -> Bool
isOutOfFuel (Left (FastOutOfFuel _)) = True
isOutOfFuel _                        = False
