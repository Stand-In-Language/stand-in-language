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
assertExprWith :: (String -> IO (Either String String)) -> String -> String -> Assertion
assertExprWith evalStr input expected = do
  res <- evalStr input
  case res of
    Left err  -> unless (expected `isInfixOf` err) . assertFailure
                  $ "Evaluation failed: " <> err
    Right val -> val @?= expected

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
refinementTests = testGroup "Refinement annotations and list assignments"
  [ testCase "plain list assignment works inside let" $
      assertEvalEquals
        "let [a, b, c] = [1, 2, 3] in b"
        "2"
  -- Refinement annotations, both @x : validator = value@ and lambda
  -- parameters @\(x : validator) -> ...@, lower to @CheckUPF@. The
  -- compiler's static refinement pass runs that validator symbolically
  -- and rejects values that can be proven to abort.
  , testCase "plain refinement annotations use static CheckUPF" $
      assertStaticCheckError
        ( "let x : (\\v -> assert (not v) "
          <> "\"plain refinement uses CheckUPF\") = 1 in x" )
        "plain refinement uses CheckUPF"
  , testCase "lambda parameter refinements use static CheckUPF" $
      assertStaticCheckError
        ( "(\\(x : \\v -> assert (not v) "
          <> "\"lambda refinement uses CheckUPF\") -> x) 1" )
        "lambda refinement uses CheckUPF"
  , testCase "lambda parameter refinements bind the checked value" $
      assertEvalEquals
        "(\\(x : Bool) y (z : Bool) -> if x then y else z) 1 7 0"
        "7"
  , testCase "lambda refinements reject values statically" $
      assertStaticCheckError
        "(\\(x : Bool) -> x) 2"
        "user abort: Bool cannot have non-zero val in left of pair"
  , testCase "refined lambda parameters can still be destructured" $
      assertEvalEquals
        "(\\((a, b) : \\v -> 0) -> b) (1, 2)"
        "2"
  ]
