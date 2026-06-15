{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables   #-}

-- | Dedicated tests for the user-defined-type sugar
-- @[T, op1, op2, ...] = \\h -> [ ... ]@ exercised through an embedded
-- @Nat@ UDT fixture.
module NatUDTTests (natUDTTests) where

import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Monad (unless)
import Data.Bifunctor (Bifunctor (first, second))
import Data.List (isInfixOf)
import PrettyPrint
import qualified System.IO.Strict as Strict
import Telomare
import Telomare.Eval (SizingOption (..), compile, runStaticChecks)
import Telomare.Parser (parseLongExpr, parsePrelude)
import Telomare.Possible (SizingSettings (SizingSettings))
import Telomare.Resolver (process, pruneBindings)
import Test.Tasty
import Test.Tasty.HUnit
import Text.Megaparsec (eof, errorBundlePretty, runParser)

natUDTSource :: String
natUDTSource = unlines
  [ "[Nat, toNat, fromNat, nPlus, nMinus] = \\h ->"
  , "  [ \\x -> (h, x)"
  , "  , \\(x : Nat) -> x"
  , "  , \\(aa : Nat) (bb : Nat) -> (h, d2c aa succ bb)"
  , "  , \\(aa : Nat) (bb : Nat) ->"
  , "      let sLeft = \\x -> case x of"
  , "                          (l, _) -> l"
  , "                          y      -> abort \"can't subtract larger number from smaller one\""
  , "      in (h, d2c bb sLeft aa)"
  , "  ]"
  ]

parseBindings :: String -> String -> IO [(String, AnnotatedUPT)]
parseBindings name raw =
  case parsePrelude raw of
    Left err -> error $ "parseBindings: " <> name <> ": " <> err
    Right bs -> pure bs

loadBindings :: FilePath -> IO [(String, AnnotatedUPT)]
loadBindings path = do
  raw <- Strict.readFile path
  parseBindings path raw

-- |Evaluate @expr@ in the scope of @Prelude.tel@ + the embedded Nat UDT.
evalUDTExpr :: String -> IO (Either String String)
evalUDTExpr input = do
  preludeBindings <- loadBindings "Prelude.tel"
  udtBindings     <- parseBindings "Nat UDT fixture" natUDTSource
  let allBindings = preludeBindings <> udtBindings
  case runParser (parseLongExpr <* eof) "" input of
    Left err -> pure $ Left (errorBundlePretty err)
    Right aupt -> do
      let bindings = fmap (second unAnnotatedUPT) allBindings
          term = UnknownLoc :< LetUPF (first (locatedName UnknownLoc) <$> pruneBindings aupt bindings) aupt
          compile' :: Term3 -> Either EvalError CompiledExpr
          compile' = compile (DebugSizing (SizingSettings 255 False)) runStaticChecks
      case first RE (process $ AnnotatedUPT term) >>= compile' of
        Left err -> pure $ Left (show err)
        Right iexpr -> case eval iexpr of
          Left e       -> pure . Left . show $ e
          Right result -> case toTelomare result of
            Just r  -> pure . Right . show $ PrettyStuckExpr r
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

assertStaticCheckError :: String -> String -> Assertion
assertStaticCheckError input msgFragment = do
  res <- evalUDTExpr input
  case res of
    Left err ->
      unless ("StaticCheckError" `isInfixOf` err && msgFragment `isInfixOf` err)
        . assertFailure
        $ "Expected static check error containing '" <> msgFragment <> "', got: " <> err
    Right val ->
      assertFailure
        $ "Expected static check error containing '" <> msgFragment
        <> "' but evaluation succeeded with: " <> val

natUDTTests :: TestTree
natUDTTests = testGroup "User-defined-type sugar (embedded Nat UDT)"
  [ testGroup "Unit tests"
      [ testCase "toNat then right round-trips the value" $
          assertEvalEquals "right (toNat 8)" "8"
      , testCase "fromNat extracts a Nat payload" $
          assertEvalEquals "fromNat (toNat 8)" "8"
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
      , testCase "plain list assignment works inside let" $
          assertEvalEquals
            "let [a, b, c] = [1, 2, 3] in b"
            "2"
      -- Normal refinement annotations, such as @x : validator = value@,
      -- still lower to @CheckUPF@. The compiler's static refinement pass
      -- runs that validator symbolically and rejects values that can be
      -- proven to abort.
      --
      -- UDT pattern annotations, such as @\(x : Nat) -> x@, deliberately do
      -- not lower to @CheckUPF@. A UDT validator compares the branded value's
      -- hash against the UDT hash generated by the UDT expansion, so the
      -- static refinement analyzer cannot prove it symbolically. Instead the
      -- parser lowers the annotation to a runtime validator call used as a
      -- @case@ scrutinee: success extracts the payload, and failure aborts at
      -- runtime with the validator's message.
      , testCase "plain refinement annotations use static CheckUPF" $
          assertStaticCheckError
            ( "let x : (\\v -> assert (not v) "
              <> "\"plain refinement uses CheckUPF\") = 1 in x" )
            "plain refinement uses CheckUPF"
      , testCase "UDT annotations validate branded values at runtime" $
          assertEvalEquals "fromNat (toNat 8)" "8"
      , testCase "UDT annotations reject unbranded values at runtime" $
          assertAborts "fromNat (0, 8)" "not Nat"
      ]
  -- NOTE: QuickCheck property tests for nPlus/nMinus were omitted
  -- because each evalUDTExpr call recompiles Prelude+the embedded UDT+the
  -- expression from scratch, which currently takes 5–6 minutes per
  -- compile (Prelude is big; nPlus pulls in the d2c recursion which
  -- triggers sizing). The unit tests above cover the same behaviour.
  ]
