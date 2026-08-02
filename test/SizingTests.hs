module SizingTests where

import Data.List (isInfixOf)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import qualified System.IO.Strict as Strict
import Test.Hspec

import Telomare.Error
import Telomare.IR.Base
import Telomare.IR.Builder
import Telomare.IR.Core
import Telomare.IR.Loc
import Telomare.IR.Surface
import Telomare.IR.Types
import Telomare.Eval (SizingOption (DebugSizing), SizingReport (..),
                      compileModules, compileModulesWith,
                      renderSizingCertificate)
import Telomare.Meter (Meter (..), evalMeter)
import Telomare.Possible (SizingSettings (SizingSettings), appB)
import Telomare.PossibleData (SizedRecursion (..))

-- Common datatypes for generating Telomare AST.
import Common

limitsDir :: FilePath
limitsDir = "test/programs/limits/"

-- |Compile a program alongside the prelude, at a chosen sizing budget.
compileProgram :: SizingOption -> FilePath -> String -> IO (Either String SizingReport)
compileProgram sizingOption path moduleName = do
  prelude <- Strict.readFile "Prelude.tel"
  source <- Strict.readFile path
  pure . fmap fst $
    compileModulesWith sizingOption [("Prelude", prelude), (moduleName, source)] moduleName

-- |Compile at the budget the CLI uses.
compileAtFullBudget :: FilePath -> String -> IO (Either String SizingReport)
compileAtFullBudget = compileProgram (DebugSizing (SizingSettings 65536 True))

sizingSpec :: Spec
sizingSpec = do
  describe "sizing failures name the recursion and say why" $ do
    -- The distinction these two tests draw is the whole point: one is fixable
    -- by a bigger budget and the other is not, and before this they were
    -- reported identically.
    it "reports unbounded input as unfixable by budget" $ do
      result <- compileAtFullBudget
        (limitsDir <> "unbounded-input-recursion.tel") "unbounded-input-recursion"
      case result of
        Right _ -> expectationFailure "expected this program to fail sizing"
        Left err -> do
          err `shouldSatisfy` isInfixOf "depends on input that nothing bounds"
          err `shouldSatisfy` isInfixOf "unbounded-input-recursion:"

    it "reports an exhausted budget as an exhausted budget" $ do
      result <- compileProgram (DebugSizing (SizingSettings 5 True))
        (limitsDir <> "over-budget-recursion.tel") "over-budget-recursion"
      case result of
        Right _ -> expectationFailure "expected this program to exhaust the budget"
        Left err -> do
          err `shouldSatisfy` isInfixOf "had still not stopped after 6 unrollings"
          err `shouldSatisfy` isInfixOf "over-budget-recursion:"

    it "sizes the same program once the budget is big enough" $ do
      result <- compileAtFullBudget
        (limitsDir <> "over-budget-recursion.tel") "over-budget-recursion"
      case result of
        Left err -> expectationFailure $ "expected this program to size:\n" <> err
        Right _  -> pure ()

  describe "sizing results are reported" $ do
    it "gives every recursion site a count and a source location" $ do
      result <- compileAtFullBudget "simpleplus.tel" "simpleplus"
      case result of
        Left err -> expectationFailure $ "failed to compile simpleplus.tel:\n" <> err
        Right report -> do
          let counts = Map.toList . unSizedRecursion $ sizingReportCounts report
          counts `shouldSatisfy` not . null
          -- A site with no count would mean the compiler baked in a loop bound
          -- it could not justify.
          counts `shouldSatisfy` all (isJust . snd)
          -- Every site is locatable, which is what makes the report actionable.
          counts `shouldSatisfy` all
            (\(tok, _) -> case Map.lookup tok (sizingReportLocs report) of
               Just loc -> isJust (locStartLineColumn loc)
               Nothing  -> False)

    it "keeps simpleplus.tel's inferred counts stable" $ do
      result <- compileAtFullBudget "simpleplus.tel" "simpleplus"
      case result of
        Left err -> expectationFailure $ "failed to compile simpleplus.tel:\n" <> err
        Right report ->
          -- Two `d2c` calls converting a decimal digit, and the prelude's own
          -- recursions. If these move, sizing precision moved with them.
          (snd <$> Map.toAscList (unSizedRecursion (sizingReportCounts report)))
            `shouldBe` [Just 11, Just 7, Just 10, Just 10]

    it "names the budget it searched under" $ do
      result <- compileAtFullBudget "simpleplus.tel" "simpleplus"
      case result of
        Left err -> expectationFailure $ "failed to compile simpleplus.tel:\n" <> err
        Right report -> do
          sizingReportBudget report `shouldBe` 65536
          renderSizingCertificate report `shouldSatisfy` isInfixOf "65536"

  -- The meter is a second interpreter, so the thing worth testing is that it is
  -- still the same interpreter. It is easy to get a plausible cost out of an
  -- evaluator that quietly computes the wrong answer.
  describe "the meter mirrors the evaluator"
    . it "computes the same value as the real evaluator" $ do
      result <- compileAtFullBudget "tc_ultra_minimal.tel" "tc_ultra_minimal"
      case result of
        Left err -> expectationFailure $ "failed to compile:\n" <> err
        Right _  -> pure ()
      prelude <- Strict.readFile "Prelude.tel"
      source <- Strict.readFile "tc_ultra_minimal.tel"
      case compileModules [("Prelude", prelude), ("tc_ultra_minimal", source)] "tc_ultra_minimal" of
        Left err -> expectationFailure $ "failed to compile:\n" <> err
        Right (_, sized) -> do
          let applied = appB sized ZeroB
              (measured, metered) = evalMeter applied
          fmap show metered `shouldBe` fmap show (eval applied)
          meterSteps measured `shouldSatisfy` (> 0)
          -- A run of any length constructs at least one node.
          meterBuilt measured `shouldSatisfy` (> 0)

-- |Kept for the historical name; the suite entry point calls this.
twoFailedApproaches :: Spec
twoFailedApproaches = sizingSpec
