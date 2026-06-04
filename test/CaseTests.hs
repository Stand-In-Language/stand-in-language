{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}

module CaseTests (unitTestsCase, qcPropsCase) where

import Common
import Control.Comonad.Cofree (Cofree ((:<)))
import qualified Control.Monad.State as State
import Data.Fix (Fix (..))
import PrettyPrint
import qualified System.IO.Strict as Strict
import Telomare
import Telomare.Eval (runMainWithInput)
import Telomare.Parser
import Telomare.Resolver (pattern2UPT)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC

caseTests :: IO ()
caseTests = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTestsCase, qcPropsCase]

---------------------
------ Property Tests
---------------------

caseExprStrWithPattern :: PatternA -> String
caseExprStrWithPattern p = unlines
  [ "import Prelude"
  , "main ="
  , "  let toCase = " <> showPatternTerm p
  , "      caseTest ="
  , "        case toCase of"
  , "          " <> prettyPrintPattern (const "") p <> " -> \"True\""
  , "          _ -> \"False\""
  , "  in \\input -> (caseTest, 0)"
  ]

caseExprStrWithPatternIgnore :: PatternA -> String
caseExprStrWithPatternIgnore p = unlines
  [ "import Prelude"
  , "main ="
  , "  let toCase = " <> showPatternTerm p
  , "      caseTest ="
  , "        case toCase of"
  , "          _ -> \"True\""
  , "          " <> prettyPrintPattern (const "") p <> " -> \"False\""
  , "  in \\input -> (caseTest, 0)"
  ]

showPatternTerm :: PatternA -> String
showPatternTerm = prettyAUPT . pattern2UPT UnknownLoc

prettyAUPT :: AUPT -> String
prettyAUPT (_ :< term) = case term of
  IntUPF i      -> show i
  VarUPF str    -> str
  StringUPF str -> show str
  PairUPF x y   -> "(" <> prettyAUPT x <> "," <> prettyAUPT y <> ")"
  AppUPF x y    -> prettyAUPT x <> " " <> prettyAUPT y
  _             -> error $ "unexpected generated case test term: " <> show term

runCaseExpWithPattern :: (PatternA -> String) -> PatternA -> IO String
runCaseExpWithPattern p2s p = runTelomareStr $ p2s p

qcPropsCase = testGroup "Property tests on case expressions (QuickCheck)"
  [ QC.testProperty "All case patterns are reachable" $
      \x -> withMaxSuccess 16 . QC.idempotentIOProperty $ (do
        res <- runCaseExpWithPattern caseExprStrWithPattern x
        case res of
          "True\ndone" -> pure True
          _            -> pure False)
  , QC.testProperty "Ignore pattern accpets any pattern" $
      \x -> withMaxSuccess 16 . QC.idempotentIOProperty $ (do
        res <- runCaseExpWithPattern caseExprStrWithPatternIgnore x
        case res of
          "True\ndone" -> pure True
          _            -> pure False)
  ]

unitTestsCase :: TestTree
unitTestsCase = testGroup "Unit tests on case expressions"
  [ testCase "test case with int leaves" $ do
      res <- runTelomareStr caseExprIntLeavesStr
      res @?= "True\ndone"
  , testCase "test case with string leaves" $ do
      res <- runTelomareStr caseExprStringLeavesStr
      res @?= "True\ndone"
  , testCase "test case with all leaves" $ do
      res <- runTelomareStr caseExprAllLeavesStr
      res @?= "Hi, sam!\ndone"
  ]

runTelomareStr :: String -> IO String
runTelomareStr str = do
  preludeStr <- Strict.readFile "Prelude.tel"
  runMainWithInput [] [("Prelude", preludeStr), ("dummyModule", str)] "dummyModule"

caseExprIntLeavesStr :: String
caseExprIntLeavesStr = unlines
  [ "import Prelude"
  , "main ="
  , "  let toCase = (0,(8,2))"
  , "      caseTest ="
  , "        case toCase of"
  , "          (0, (1,2)) -> \"False\""
  , "          (1, (8,2)) -> \"False\""
  , "          (0,(8,2)) -> \"True\""
  , "  in \\input -> (caseTest, 0)"
  ]

caseExprStringLeavesStr :: String
caseExprStringLeavesStr = unlines
  [ "import Prelude"
  , "main ="
  , "  let toCase = (\"a string\",(\"hi, sam\",\"str\"))"
  , "      caseTest ="
  , "        case toCase of"
  , "          (\"a string\", (\"hi, sam\",2)) -> \"False\""
  , "          (1, (8,2)) -> \"False\""
  , "          (\"a string\",(\"hi, sam\",\"str\")) -> \"True\""
  , "  in \\input -> (caseTest, 0)"
  ]

caseExprAllLeavesStr :: String
caseExprAllLeavesStr = unlines
  [ "import Prelude"
  , "main ="
  , "  let toCase = (\"a string\",(\"Hi, sam!\",\"str\"))"
  , "      caseTest ="
  , "        case toCase of"
  , "          (\"a string\", (\"Hi, sam!\",2)) -> \"False\""
  , "          (1, (8,2)) -> \"False\""
  , "          (\"a string\",(x,\"str\")) -> x"
  , "  in \\input -> (caseTest, 0)"
  ]

instance Arbitrary PatternA where
  arbitrary = sanitizePatternVars <$> sized genTree where
    sanitizePatternVars :: PatternA -> PatternA
    sanitizePatternVars p = State.evalState (go p) 0 where
      go :: PatternA -> State.State Int PatternA
      go (Fix patternF) = case patternF of
        PatternVarF _ -> do
          s <- State.get
          State.modify (+ 1)
          pure . Fix . PatternVarF $ "var" <> show s
        PatternPairF x y -> Fix <$> (PatternPairF <$> go x <*> go y)
        other -> pure $ Fix other
    leaves :: Gen PatternA
    leaves = oneof
      [ Fix . PatternStringF <$> elements (fmap (("s" <>) . show) [1..9])
      , Fix . PatternIntF <$> elements [0..9]
      , pure . Fix $ PatternVarF ""
      ]
    genTree :: Int -> Gen PatternA
    genTree = \case
      0 -> leaves
      x -> oneof
        [ leaves
        , Fix <$> (PatternPairF <$> genTree (div x 2) <*> genTree (div x 2))
        ]

  shrink (Fix patternF) = case patternF of
    PatternVarF str -> case str of
      "" -> []
      _  -> pure . Fix . PatternVarF $ tail str
    PatternStringF s -> case s of
      "" -> []
      _  -> pure . Fix . PatternStringF $ tail s
    PatternIntF i -> case i of
      0 -> []
      x -> pure . Fix . PatternIntF $ x - 1
    PatternPairF a b -> a : b : [Fix $ PatternPairF na nb | (na, nb) <- shrink (a,b)]
    _ -> []
