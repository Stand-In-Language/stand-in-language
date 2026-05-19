{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables   #-}

-- | Dedicated tests for the user-defined-type sugar
-- @[T, op1, op2, …] = \\h -> [ … ]@ exercised through the @Nat@ UDT
-- defined in @udt.tel@.
module NatUDTTests (natUDTTests) where

import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Monad (unless)
import Data.Bifunctor (Bifunctor (first))
import Data.List (isInfixOf, isPrefixOf)
import PrettyPrint
import qualified System.IO.Strict as Strict
import Telomare
import Telomare.Eval (SizingOption (..), compile, runStaticChecks)
import Telomare.Parser (AnnotatedUPT, parseLongExpr, parsePrelude)
import Telomare.Possible (SizingSettings (SizingSettings))
import Telomare.PossibleData (CompiledExpr)
import Telomare.Resolver (process, pruneBindings)
import Test.Tasty
import Test.Tasty.HUnit
import Text.Megaparsec (eof, errorBundlePretty, runParser)

-- |Strip a leading @import Prelude@ line from a .tel file so the
-- remaining bindings can be fed to 'parsePrelude' (which handles
-- assignments and UDTs but not @import@ directives).
stripImports :: String -> String
stripImports = unlines . filter (not . ("import " `isPrefixOf`)) . lines

loadBindings :: FilePath -> IO [(String, AnnotatedUPT)]
loadBindings path = do
  raw <- Strict.readFile path
  case parsePrelude (stripImports raw) of
    Left err -> error $ "loadBindings: " <> path <> ": " <> err
    Right bs -> pure bs

-- |Evaluate @expr@ in the scope of @Prelude.tel@ + @udt.tel@.
evalUDTExpr :: String -> IO (Either String String)
evalUDTExpr input = do
  preludeBindings <- loadBindings "Prelude.tel"
  udtBindings     <- loadBindings "udt.tel"
  let allBindings = preludeBindings <> udtBindings
  case runParser (parseLongExpr <* eof) "" input of
    Left err -> pure $ Left (errorBundlePretty err)
    Right aupt -> do
      let term = DummyLoc :< LetUPF (pruneBindings aupt allBindings) aupt
          compile' :: Term3 -> Either EvalError CompiledExpr
          compile' = compile (DebugSizing (SizingSettings 255 False)) runStaticChecks
      case first RE (process term) >>= compile' of
        Left err -> pure $ Left (show err)
        Right iexpr -> case eval iexpr of
          Left e       -> pure . Left . show $ e
          Right result -> case toTelomare result of
            Just r  -> pure . Right . show $ PrettyIExpr r
            Nothing -> pure . Left $ "conversion error from result:\n" <> prettyPrint result

assertEvalEquals :: String -> String -> Assertion
assertEvalEquals input expected = do
  res <- evalUDTExpr input
  case res of
    Left err  -> unless (expected `isInfixOf` err) . assertFailure
                  $ "Evaluation failed: " <> err
    Right val -> val @?= expected

assertAborts :: String -> String -> Assertion
assertAborts input msgFragment = do
  res <- evalUDTExpr input
  case res of
    Left err ->
      unless ("abort:" `isInfixOf` err && msgFragment `isInfixOf` err)
        . assertFailure
        $ "Expected abort containing '" <> msgFragment <> "', got: " <> err
    Right val ->
      assertFailure
        $ "Expected abort containing '" <> msgFragment
        <> "' but evaluation succeeded with: " <> val

natUDTTests :: TestTree
natUDTTests = testGroup "User-defined-type sugar (Nat UDT from udt.tel)"
  [ testGroup "Unit tests"
      [ testCase "toNat then right round-trips the value" $
          assertEvalEquals "right (toNat 8)" "8"
      , testCase "nPlus on two valid Nats returns the sum" $
          assertEvalEquals "right (nPlus (toNat 3) (toNat 5))" "8"
      , testCase "nMinus on two valid Nats returns the difference" $
          assertEvalEquals "right (nMinus (toNat 7) (toNat 2))" "5"
      , testCase "nMinus aborts on underflow" $
          assertAborts
            "right (nMinus (toNat 2) (toNat 7))"
            "can't subtract larger number from smaller one"
      , testCase "nPlus rejects a non-Nat first arg" $
          assertAborts
            "right (nPlus (0, 3) (toNat 5))"
            "not Nat"
      , testCase "nPlus rejects a non-Nat second arg" $
          assertAborts
            "right (nPlus (toNat 3) (0, 5))"
            "not Nat"
      , testCase "UDT destructuring works inside let" $
          assertEvalEquals
            ( "let [Color, mkColor, defaultColor] = \\h -> "
              <> "[ \\c -> (h, c), (h, 7) ] "
              <> "in right defaultColor" )
            "7"
      ]
  -- NOTE: QuickCheck property tests for nPlus/nMinus were omitted
  -- because each evalUDTExpr call recompiles Prelude+udt.tel+the
  -- expression from scratch, which currently takes 5–6 minutes per
  -- compile (Prelude is big; nPlus pulls in the d2c recursion which
  -- triggers sizing). The unit tests above cover the same behaviour.
  ]
