{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables   #-}

-- | Tests of refinement annotations and list assignments, evaluated in the
-- scope of @Prelude.tel@. Also home of the eval harness shared with the
-- Prelude suite.
module RefinementTests
  ( refinementTests
  , loadBindings
  , evalWithBindings
  , assertExprWith
  , assertErrorWith
  ) where

import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Monad (unless)
import Data.Bifunctor (Bifunctor (first))
import Data.List (isInfixOf)
import qualified System.IO.Strict as Strict
import Telomare.Desugar (desugarTerm)
import Telomare.Driver (SizingOption (..), compile, runStaticChecks)
import Telomare.Error
import Telomare.Expand (expandDefs, expandTerm, renderExpansionError)
import Telomare.IR.Core
import Telomare.IR.Loc
import Telomare.IR.Surface
import Telomare.Parse (parseLongExpr, runParseDefinitions)
import Telomare.PrettyPrint
import Telomare.Resolve (process, pruneBindings)
import Telomare.Size (SizingSettings (SizingSettings))
import Test.Tasty
import Test.Tasty.HUnit
import Text.Megaparsec (eof, errorBundlePretty, runParser)

parseBindings :: String -> String -> IO [(String, ExpandedSurfaceTerm)]
parseBindings name raw =
  case runParseDefinitions "" raw
         >>= first renderExpansionError . expandDefs of
    Left err -> error $ "parseBindings: " <> name <> ": " <> err
    Right bs -> pure $ first locatedNameText <$> bs

loadBindings :: FilePath -> IO [(String, ExpandedSurfaceTerm)]
loadBindings path = do
  raw <- Strict.readFile path
  parseBindings path raw

-- |Evaluate @expr@ in the scope of the given bindings.
evalWithBindings :: [(String, ExpandedSurfaceTerm)] -> String -> IO (Either String String)
evalWithBindings bindings input =
  case first errorBundlePretty (runParser (parseLongExpr <* eof) "" input)
         >>= first renderExpansionError . expandTerm of
    Left err -> pure $ Left err
    Right aupt -> do
      let term = UnknownLoc :< LetUPF (first (locatedName UnknownLoc) <$> pruneBindings aupt bindings) aupt
          compile' :: Term3 -> Either EvalError CompiledExpr
          compile' = compile (DebugSizing (SizingSettings 255 False)) runStaticChecks
      case first RE (process $ desugarTerm term) >>= compile' of
        Left err -> pure $ Left (show err)
        Right iexpr -> case eval iexpr of
          Left e       -> pure . Left . show $ e
          Right result -> case toTelomare result of
            Just r  -> pure . Right . show $ PrettyBasic r
            Nothing -> pure . Left $ "conversion error from result:\n" <> prettyPrint result

-- |Evaluate @expr@ in the scope of @Prelude.tel@.
evalPreludeExpr :: String -> IO (Either String String)
evalPreludeExpr input = do
  preludeBindings <- loadBindings "Prelude.tel"
  evalWithBindings preludeBindings input

-- |Assert that @input@ evaluates to @expected@ under the given evaluator.
-- An evaluation error always fails: a test that expects one uses
-- 'assertErrorWith'.
assertExprWith :: (String -> IO (Either String String)) -> String -> String -> Assertion
assertExprWith evalStr input expected = do
  res <- evalStr input
  case res of
    Left err  -> assertFailure $ "Evaluation failed: " <> err
    Right val -> val @?= expected

-- |Assert that evaluating @input@ fails with an error containing
-- @msgFragment@.
assertErrorWith :: (String -> IO (Either String String)) -> String -> String -> Assertion
assertErrorWith evalStr input msgFragment = do
  res <- evalStr input
  case res of
    Left err ->
      unless (msgFragment `isInfixOf` err)
        . assertFailure
        $ "Expected an error containing '" <> msgFragment <> "', got: " <> err
    Right val ->
      assertFailure
        $ "Expected an error containing '" <> msgFragment
        <> "' but evaluation succeeded with: " <> val

assertEvalEquals :: String -> String -> Assertion
assertEvalEquals = assertExprWith evalPreludeExpr

assertStaticCheckError :: String -> String -> Assertion
assertStaticCheckError input msgFragment = do
  res <- evalPreludeExpr input
  case res of
    Left err ->
      unless ("StaticCheckError" `isInfixOf` err && msgFragment `isInfixOf` err)
        . assertFailure
        $ "Expected static check error containing '" <> msgFragment <> "', got: " <> err
    Right val ->
      assertFailure
        $ "Expected static check error containing '" <> msgFragment
        <> "' but evaluation succeeded with: " <> val

refinementTests :: TestTree
refinementTests = testGroup "Refinement annotations, guards and list assignments"
  [ testCase "plain list assignment works inside let" $
      assertEvalEquals
        "let [a, b, c] = [1, 2, 3] in b"
        "2"
  -- An annotation @(p : P)@ is a predicate on what @p@ matches: anything
  -- but Zero passes. In a definition or at the top of a lambda parameter
  -- it is a refinement, a match with no alternative to fall to, which the
  -- static checks reject when they can prove it fails.
  , testCase "a definition refinement that fails is rejected statically" $
      assertStaticCheckError
        "let x : (\\v -> not v) = 1 in x"
        "check failed on 1"
  , testCase "a lambda parameter refinement that fails is rejected statically" $
      assertStaticCheckError
        "(\\(x : \\v -> not v) -> x) 1"
        "check failed on 1"
  , testCase "lambda parameter refinements bind the checked value" $
      assertEvalEquals
        "(\\(x : Bool) y (z : Bool) -> if x then y else z) 1 7 0"
        "7"
  , testCase "lambda refinements reject values statically" $
      assertStaticCheckError
        "(\\(x : Bool) -> x) 2"
        "check failed on 2"
  , testCase "refined lambda parameters can still be destructured" $
      assertEvalEquals
        "(\\((a, b) : \\v -> 1) -> b) (1, 2)"
        "2"
  -- In a case alternative the same annotation is a guard: where it fails,
  -- matching goes on to the next alternative.
  , testCase "a case guard that holds selects its alternative" $
      assertEvalEquals
        "case 3 of\n  (x : \\v -> dEqual v 3) -> 30\n  _ -> 40"
        "30"
  , testCase "a case guard that fails falls through" $
      assertEvalEquals
        "case 4 of\n  (x : \\v -> dEqual v 3) -> 30\n  _ -> 40"
        "40"
  , testCase "a guard nested in a pair pattern runs on its part" $
      assertEvalEquals
        "case (1, 5) of\n  (a, (b : \\v -> dEqual v 4)) -> b\n  (a, b) -> a"
        "1"
  , testCase "a guard bound variable gets the matched value" $
      assertEvalEquals
        "case (1, 4) of\n  (a, (b : \\v -> dEqual v 4)) -> b\n  (a, b) -> a"
        "4"
  , testCase "a case whose guards all fail aborts" $
      assertStaticCheckError
        "case 4 of\n  (x : \\v -> dEqual v 3) -> \"three\""
        "Non-exhaustive patterns in case"
  , testCase "a guard nested in a lambda parameter aborts as a mismatch" $
      assertStaticCheckError
        "(\\((a : Bool), b) -> b) (2, 3)"
        "lambda argument does not match its pattern"
  ]
