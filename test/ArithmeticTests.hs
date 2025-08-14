{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Main where

import Common
import Control.Comonad.Cofree (Cofree ((:<)))
import Data.Bifunctor (second)
import PrettyPrint
import qualified System.IO.Strict as Strict
import Telomare
import Telomare.Eval (compileUnitTest, EvalError (CompileConversionError))
import Telomare.RunTime (simpleEval)
import Telomare.Resolver (process)
import Telomare.Parser (parseLongExpr, TelomareParser, parsePrelude, AnnotatedUPT)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC
import Text.Megaparsec (runParser, errorBundlePretty, eof)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Arithmetic Tests" [ unitTestsNatArithmetic
                                     , unitTestsRatArithmetic
                                     , qcPropsNatArithmetic
                                     , qcPropsRatArithmetic]

parseReplExpr :: TelomareParser [(String, UnprocessedParsedTerm)]
parseReplExpr = do
  expr <- parseLongExpr <* eof
  pure [("_tmp_", forget expr)]

maybeToRight :: Maybe a -> Either EvalError a
maybeToRight (Just x) = Right x
maybeToRight Nothing  = Left CompileConversionError

rightToMaybe :: Either String a -> Maybe a
rightToMaybe (Right x) = Just x
rightToMaybe _         = Nothing

loadPreludeBindings :: IO [(String, UnprocessedParsedTerm)]
loadPreludeBindings = do
  preludeResult <- Strict.readFile "Prelude.tel"
  case parsePrelude preludeResult of
    Left _ -> pure []
    Right bs -> pure $ fmap (second forget) bs

evalExprString :: String -> IO (Either String String)
evalExprString input = do
  preludeBindings <- loadPreludeBindings
  let parseResult = runParser (parseReplExpr <* eof) "" input
  case parseResult of
    Left err -> pure $ Left (errorBundlePretty err)
    Right exprBindings -> do
      let allBindingsUPT = preludeBindings ++ exprBindings
          allBindings :: [(String, Cofree UnprocessedParsedTermF LocTag)]
          allBindings = fmap (second (tag DummyLoc)) allBindingsUPT
          uptMaybe = lookup "_tmp_" allBindings
          termMaybe = fmap (DummyLoc :<) . fmap (LetUPF allBindings) $ uptMaybe
          compiled = compileUnitTest =<< maybeToRight (termMaybe >>= rightToMaybe . process)
      case compiled of
        Left err -> pure $ Left (show err)
        Right iexpr -> do
          result <- simpleEval (SetEnv (Pair (Defer iexpr) Zero))
          pure $ Right (show $ PrettyIExpr result)

assertExpr :: String -> String -> Assertion
assertExpr input expected = do
  res <- evalExprString input
  case res of
    Left err -> assertFailure $ "Evaluation failed: " <> err
    Right val -> val @?= expected

-----------------
------ Unit Tests
-----------------

unitTestsNatArithmetic :: TestTree
unitTestsNatArithmetic = testGroup "Unit tests on natural arithmetic expresions"
  [ testCase "test addition" $ assertExpr "dPlus 1 2" "3"
  ]

unitTestsRatArithmetic :: TestTree
unitTestsRatArithmetic = testGroup "Unit tests on natural arithmetic expresions"
  [ 
  ]

---------------------
------ Property Tests
---------------------

qcPropsNatArithmetic = testGroup "Property tests on natural arithmetic expressions (QuickCheck)"
  [ 
  ]

qcPropsRatArithmetic = testGroup "Property tests on rational arithmetic expressions (QuickCheck)"
  [ 
  ]
