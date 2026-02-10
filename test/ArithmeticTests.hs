{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Main where

import Common
import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Monad (unless)
import Data.Bifunctor (Bifunctor (first))
import Data.List (isInfixOf)
import Data.Ratio
import Debug.Trace
import PrettyPrint
import qualified System.IO.Strict as Strict
import Telomare
import Telomare.Eval (compileUnitTest, compileUnitTestNoAbort)
import Telomare.Parser (AnnotatedUPT, TelomareParser, parseLongExpr,
                        parsePrelude)
import Telomare.Resolver (process)
import Telomare.RunTime (simpleEval)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC
import Text.Megaparsec (eof, errorBundlePretty, runParser)


main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Arithmetic Tests" [ unitTestsNatArithmetic
                                     , unitTestsRatArithmetic
                                     , qcPropsNatArithmetic
                                     , qcPropsRatArithmetic
                                     ]

maybeToRight :: Maybe a -> Either EvalError a
maybeToRight (Just x) = Right x
maybeToRight Nothing  = Left CompileConversionError

rightToMaybe :: Either String a -> Maybe a
rightToMaybe (Right x) = Just x
rightToMaybe _         = Nothing

loadPreludeBindings :: IO [(String, AnnotatedUPT)]
loadPreludeBindings = do
  preludeResult <- Strict.readFile "Prelude.tel"
  case parsePrelude preludeResult of
    Left _   -> pure []
    Right bs -> pure bs

evalExprString :: String -> IO (Either String String)
evalExprString input = do
  preludeBindings <- loadPreludeBindings
  let parseResult = runParser (parseLongExpr <* eof) "" input
  case parseResult of
    Left err -> pure $ Left (errorBundlePretty err)
    Right aupt -> do
      let term = DummyLoc :< LetUPF preludeBindings aupt
          compile' :: Term3 -> Either EvalError IExpr
          compile' x = case compileUnitTestNoAbort x of
                         Left err -> Left  err
                         Right r  -> case toTelomare r of
                           Just te -> pure $ fromTelomare te
                           Nothing -> Left . RTE . ResultConversionError $ "conversion error from compiled expr:\n" <> prettyPrint r
      case first RE (process term) >>= compile' of
        Left err -> pure $ Left (show err)
        Right iexpr -> case eval iexpr of
                         Left e -> pure . Left . show $ e
                         Right result -> pure . Right . show . PrettyIExpr $ result

assertExpr :: String -> String -> Assertion
assertExpr input expected = do
  res <- evalExprString input
  case res of
    Left err  -> unless (expected `isInfixOf` err) . assertFailure $ "Evaluation failed: " <> err
    Right val -> val @?= expected

rationalToString :: Ratio Integer -> String
rationalToString r = "(" <> show (numerator r) <> "," <> show (denominator r) <> ")"

genInt :: Gen Int
genInt = choose (0, 100)

genInt2 :: Gen Int
genInt2 = choose (0, 85)

genInt3 :: Gen Int
genInt3 = choose (0, 16)

genInt4 :: Gen Int
genInt4 = choose (0, 6)

-----------------
------ Unit Tests
-----------------

unitTestsNatArithmetic :: TestTree
unitTestsNatArithmetic = testGroup "Unit tests on natural arithmetic expresions"
  [ testCase "test addition" $ assertExpr "dPlus 1 2" (show (1 + 2))
  , testCase "test subtraction" $ assertExpr "dMinus 5 3" (show (5 - 3))
  , testCase "test substraction lower limit" $ assertExpr "dMinus 0 1" "0"
  , testCase "test multiplication" $ assertExpr "dTimes 3 4" (show (3 * 4))
  , testCase "test division" $ assertExpr "dDiv 8 2" (show (8 `div` 2))
  , testCase "test division by zero" $ assertExpr "dDiv 1 0" "abort:"
  , testCase "test equality" $ assertExpr "dEqual 3 3" "1"
  , testCase "test inequality" $ assertExpr "dEqual 3 4" "0"
  , testCase "test modulo" $ assertExpr "dMod 10 3" (show (10 `mod` 3))
  , testCase "test gcd" $ assertExpr "gcd 48 18" (show (gcd 48 18))
  , testCase "test lcm" $ assertExpr "lcm 12 15" (show (lcm 12 15))
  , testCase "test exponentiation" $ assertExpr "dPow 2 3" (show (2 ^ 3))
  , testCase "test exponentiation with zero exponent" $ assertExpr "dPow 5 0" "1"
  , testCase "test raise zero to the zero power" $ assertExpr "dPow 0 0" "1"
  , testCase "test factorial" $ assertExpr "dFactorial 5" (show (product [1..5]))
  ]

unitTestsRatArithmetic :: TestTree
unitTestsRatArithmetic = testGroup "Unit tests on rational arithmetic expresions"
  [ testCase "test addition" $ do
      let exp = rationalToString (1 % 2 + 1 % 2)
      assertExpr "right (rPlus (fromRational 1 2) (fromRational 1 2))" exp
  , testCase "test subtraction" $ do
      let exp = rationalToString (1 % 2 - 1 % 2)
      assertExpr "right (rMinus (fromRational 1 2) (fromRational 1 2))" exp
  , testCase "test multiplication" $ do
      let exp = rationalToString ((1 % 2) * (1 % 2))
      assertExpr "right (rTimes (fromRational 1 2) (fromRational 1 2))" exp
  , testCase "test division" $ do
      let exp = rationalToString ((1 % 2) / (1 % 2))
      assertExpr "right (rDiv (fromRational 1 2) (fromRational 1 2))" exp
  , testCase "test division by zero" $ assertExpr "rDiv (fromRational 1 2) (fromRational 0 1)" "abort:"
  ]

---------------------
------ Property Tests
---------------------

qcPropsNatArithmetic = testGroup "Property tests on natural arithmetic expressions (QuickCheck)"
  [ QC.testProperty "Commutative Additive" $
      \() -> withMaxSuccess 16 . QC.idempotentIOProperty $ do
        x <- generate genInt
        y <- generate genInt
        res <- evalExprString
                 ( "dEqual (dPlus " <> show x <> " " <> show y <>
                   ") (dPlus " <> show y <> " " <> show x <> ")" )
        pure $ case res of
          Left err  -> err === "1"
          Right val -> val === "1"
  , QC.testProperty "Associative Additive" $
      \() -> withMaxSuccess 16 . QC.idempotentIOProperty $ do
        x <- generate genInt2
        y <- generate genInt2
        z <- generate genInt2
        res <- evalExprString
                 ( "dEqual (dPlus (dPlus " <> show x <> " " <> show y
                 <> ")" <> show z <> ") (dPlus " <> show x <> "(dPlus "
                 <> show y <> " " <> show z <>"))" )
        pure $ case res of
          Left err  -> err === "1"
          Right val -> val === "1"
  , QC.testProperty "Neutral Additive" $
      \() -> withMaxSuccess 16 . QC.idempotentIOProperty $ do
        x   <- generate genInt
        res <- evalExprString ("dPlus " <> show x <> " 0")
        pure $ case res of
          Left err  -> err === show x
          Right val -> val === show x
  , QC.testProperty "Commutative Multiplicative" $
      \() -> withMaxSuccess 16 . QC.idempotentIOProperty $ do
        x <- generate genInt3
        y <- generate genInt3
        res <- evalExprString
                 ( "dEqual (dTimes " <> show x <> " " <> show y <>
                   ") (dTimes " <> show y <> " " <> show x <> ")" )
        pure $ case res of
          Left err  -> err === "1"
          Right val -> val === "1"
  , QC.testProperty "Associative Multiplicative" $
      \() -> withMaxSuccess 16 . QC.idempotentIOProperty $ do
        x <- generate genInt4
        y <- generate genInt4
        z <- generate genInt4
        res <- evalExprString
                 ( "dEqual (dTimes (dTimes " <> show x <> " " <> show y
                 <> ")" <> show z <> ") (dTimes " <> show x <> "(dTimes "
                 <> show y <> " " <> show z <>"))" )
        pure $ case res of
          Left err  -> err === "1"
          Right val -> val === "1"
  , QC.testProperty "Neutral Multiplicative" $
      \() -> withMaxSuccess 16 . QC.idempotentIOProperty $ do
        x   <- generate genInt
        res <- evalExprString ("dTimes " <> show x <> " 1")
        pure $ case res of
          Left err  -> err === show x
          Right val -> val === show x
  ]

qcPropsRatArithmetic = testGroup "Property tests on rational arithmetic expressions (QuickCheck)" []
