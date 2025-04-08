{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Common
import Control.Lens.Fold
import Control.Lens.Plated
import Control.Monad

import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Monad.Fix (fix)
import Control.Monad.IO.Class (liftIO)
import qualified Control.Monad.State as State
import Data.Bifunctor
import Data.Either (fromRight)
import Data.Functor.Foldable
import Data.List
import Data.Map (Map, fromList, toList)
import qualified Data.Map as Map
import Data.Ord
import qualified Data.Semigroup as Semigroup
import qualified Data.Set as Set
import Debug.Trace (trace, traceShowId)
import qualified System.IO.Strict as Strict
import System.Process hiding (createPipe)
import Telomare
import Telomare.Eval
import Telomare.Parser
import Telomare.Resolver
import Telomare.RunTime
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC
import Text.Megaparsec
import Text.Megaparsec.Debug
import Text.Megaparsec.Error

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Parser Tests" [unitTests]

unitTests :: TestTree
unitTests = testGroup "Unit tests"
  [ testCase "parse uniqueUP" $ do
      res <- parseSuccessful parseHash "# (\\x -> x)"
      res @?= True
  , testCase "test function applied to a string that has whitespaces in both sides inside a structure" $ do
      res1 <- parseSuccessful parseLongExpr "(foo \"woops\" , 0)"
      res2 <- parseSuccessful parseLongExpr "(foo \"woops\" )"
      res3 <- parseSuccessful parseLongExpr "if 0 then foo \"woops\" else 0"
      res4 <- parseSuccessful parseLongExpr "[ foo \"woops\" ]"
      (res1 && res2 && res3 && res4) `compare` True @?= EQ
  , testCase "test Pair 0" $ do
      res <- parseSuccessful (parsePair >> eof) testPair0
      res @?= True
  , testCase "test ITE 1" $ do
      res <- parseSuccessful parseITE testITE1
      res @?= True
  , testCase "test ITE 2" $ do
      res <- parseSuccessful parseITE testITE2
      res @?= True
  , testCase "test ITE 3" $ do
      res <- parseSuccessful parseITE testITE3
      res @?= True
  , testCase "test ITE 4" $ do
      res <- parseSuccessful parseITE testITE4
      res @?= True
  , testCase "test ITE with Pair" $ do
      res <- parseSuccessful parseITE testITEwPair
      res @?= True
  , testCase "test if Complete Lambda with ITE Pair parses successfuly" $ do
      res <- parseSuccessful (parseLambda <* eof) testCompleteLambdawITEwPair
      res @?= True
  , testCase "test if Lambda with ITE Pair parses successfuly" $ do
      res <- parseSuccessful (parseLambda <* eof) testLambdawITEwPair
      res @?= True
  , testCase "test parse assignment with Complete Lambda with ITE with Pair" $ do
      res <- parseSuccessful (parseTopLevel <* eof) testParseAssignmentwCLwITEwPair1
      res @?= True
  , testCase "test if testParseTopLevelwCLwITEwPair parses successfuly" $ do
      res <- parseSuccessful (parseTopLevel <* eof) testParseTopLevelwCLwITEwPair
      res @?= True
  , testCase "test main2Term3 with CL with ITE with Pair parses" $ do
      res <- runTestMainwCLwITEwPair
      res @?= True
  , testCase "testList0" $ do
      res <- parseSuccessful parseList testList0
      res @?= True
  , testCase "testList1" $ do
      res <- parseSuccessful parseList testList1
      res @?= True
  , testCase "testList2" $ do
      res <- parseSuccessful parseList testList2
      res @?= True
  , testCase "testList3" $ do
      res <- parseSuccessful parseList testList3
      res @?= True
  , testCase "testList4" $ do
      res <- parseSuccessful parseList testList4
      res @?= True
  , testCase "testList5" $ do
      res <- parseSuccessful parseList testList5
      res @?= True
  , testCase "test parse Prelude.tel" $ do
      res <- runTestParsePrelude
      res @?= True
  , testCase "test parse tictactoe.tel" $ do
      res <- testWtictactoe
      res @?= True
  , testCase "test Main with Type" $ do
      res <- runTestMainWType
      res @?= True
  , testCase "testShowBoard0" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard0
      res @?= True
  , testCase "testShowBoard1" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard1
      res @?= True
  , testCase "testShowBoard2" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard2
      res @?= True
  , testCase "testShowBoard3" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard3
      res @?= True
  , testCase "testShowBoard4" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard4
      res @?= True
  , testCase "testShowBoard5" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testShowBoard5
      res @?= True
  , testCase "testShowBoard6" $ do
      res <- parseSuccessful parseApplied testShowBoard6
      res @?= True
  , testCase "testLetShowBoard0" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetShowBoard0
      res @?= True
  , testCase "testLetShowBoard1" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetShowBoard1
      res @?= True
  , testCase "testLetShowBoard2" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetShowBoard2
      res @?= True
  , testCase "testLetShowBoard3" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) testLetShowBoard3
      res @?= True
  , testCase "testLetShowBoard4" $ do
      res <- parseSuccessful (parseTopLevel <* scn <* eof) testLetShowBoard4
      res @?= True
  , testCase "testLetShowBoard5" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetShowBoard5
      res @?= True
  , testCase "testLetShowBoard8" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) testLetShowBoard8
      res @?= True
  , testCase "testLetShowBoard9" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) testLetShowBoard9
      res @?= True
  , testCase "AST terms as functions" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "app left (pair zero zero)"
      res @?= True
  , testCase "left with a lot of arguments" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "left (\\x y z -> [x, y, z, 0], 0) 1 2 3"
      res @?= True
  , testCase "right with a lot of arguments" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "right (\\x y z -> [x, y, z, 0], 0) 1 2 3"
      res @?= True
  , testCase "trace with a lot of arguments" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "trace (\\x -> (\\y -> (x,y))) 0 0"
      res @?= True
  , testCase "app with a lot of arguments" $ do
      res <- parseSuccessful (parseApplied <* scn <* eof) "app (\\x y z -> x) 0 1 2"
      res @?= True
  , testCase "testLetIndentation" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetIndentation
      res @?= True
  , testCase "testLetIncorrectIndentation1" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetIncorrectIndentation1
      res `compare` False @?= EQ
  , testCase "testLetIncorrectIndentation2" $ do
      res <- parseSuccessful (parseLet <* scn <* eof) testLetIncorrectIndentation2
      res `compare` False @?= EQ
  , testCase "Case within top level definitions" $ do
      res' <- runTelomareParser parseTopLevel caseExpr0
      let res = forget res'
      res @?= caseExpr0UPT
  ]

caseExpr0UPT =
  LetUP [ ("foo", LamUP "a" (CaseUP (VarUP "a")
                               [ (PatternInt 0,VarUP "a")
                               , (PatternVar "x",AppUP (VarUP "succ") (VarUP "a"))
                               ]))
        , ("main", LamUP "i" (PairUP (StringUP "Success")
                                     (IntUP 0)))
        ]
        (LamUP "i" (PairUP (StringUP "Success") (IntUP 0)))
caseExpr0 = unlines
  [ "foo = \\a -> case a of"
  , "              0 -> a"
  , "              x -> succ a"
  , ""
  , "main = \\i -> (\"Success\", 0)"
  ]

test2IExpr str =  do
  preludeFile <- Strict.readFile "Prelude.tel"
  let
    prelude :: [Either AnnotatedUPT (String, AnnotatedUPT)]
    prelude = case parseModule preludeFile of
                Right p -> p
                Left pe -> error pe
  case traceShowId (eval2IExpr [("Prelude", prelude)] str) of
    Right _ -> return True
    Left _  -> return False

-- |Usefull to see if tictactoe.tel was correctly parsed and precessed to an IExpr
testWtictactoe = Strict.readFile "tictactoe.tel" >>= test2IExpr

runTestMainwCLwITEwPair = test2IExpr testMainwCLwITEwPair

runTestMainWType = test2IExpr "main : (\\x -> if x then \"fail\" else 0) = 0"

testLetIndentation = unlines
  [ "let x = 0"
  , "    y = 1"
  , "in (x,y)"
  ]

testLetIncorrectIndentation1 = unlines
  [ "let x = 0"
  , "  y = 1"
  , "in (x,y)"
  ]

testLetIncorrectIndentation2 = unlines
  [ "let x = 0"
  , "      y = 1"
  , "in (x,y)"
  ]

testPair0 = "(\"Hello World!\", \"0\")"

testITE1 = unlines
  [ "if"
  , "  1"
  , "then 1"
  , "else"
  , "  2"
  ]
testITE2 = unlines
  [ "if 1"
  , "  then"
  , "                1"
  , "              else 2"
  ]
testITE3 = unlines
  [ "if 1"
  , "   then"
  , "                1"
  , "              else 2"
  ]
testITE4 = unlines
  [ "if 1"
  , "    then"
  , "                1"
  , "              else 2"
  ]

testITEwPair = unlines
  [ "if"
  , "    1"
  , "  then (\"Hello, world!\", 0)"
  , "  else"
  , "    (\"Goodbye, world!\", 1)"
  ]

testCompleteLambdawITEwPair = unlines
  [ "\\input ->"
  , "  if"
  , "    1"
  , "   then (\"Hello, world!\", 0)"
  , "   else"
  , "    (\"Goodbye, world!\", 1)"
  ]

testLambdawITEwPair = unlines
  [ "\\input ->"
  , "  if"
  , "    1"
  , "   then (\"Hello, world!\", 0)"
  , "   else"
  , "    (\"Goodbye, world!\", 1)"
  ]

runTestParsePrelude = do
  preludeFile <- Strict.readFile "Prelude.tel"
  case parsePrelude preludeFile of
    Right _ -> return True
    Left _  -> return False

testParseAssignmentwCLwITEwPair1 = unlines
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "     then"
  , "       (\"Hello, world!\", 0)"
  , "     else (\"Goodbye, world!\", 0)"
  ]

testParseTopLevelwCLwITEwPair = unlines
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "     then"
  , "        (\"Hello, world!\", 0)"
  , "      else (\"Goodbye, world!\", 0)"
  ]

testMainwCLwITEwPair = unlines
  [ "main"
  , "  = \\input"
  , " -> if 1"
  , "     then"
  , "        (\"Hello, world!\", 0)"
  , "      else (\"Goodbye, world!\", 0)"
  ]

testList0 = unlines [ "[ 0"
  , ", 1"
  , ", 2"
  , "]"
  ]

testList1 = "[0,1,2]"

testList2 = "[ 0 , 1 , 2 ]"

testList3 = unlines
  [ "[ 0 , 1"
  , ", 2 ]"
  ]

testList4 = unlines
  [ "[ 0 , 1"
  , ",2 ]"
  ]

testList5 = unlines
  [ "[ 0,"
  , "  1,"
  , "  2 ]"
  ]

-- TODO: does it matter that one parses succesfuly and the other doesnt?
parseApplied0 = unlines
  [ "foo (bar baz"
  , "     )"
  ]
parseApplied1 = unlines
  [ "foo (bar baz"
  , "         )"
  ]


testShowBoard0 = unlines
  [ "main = or (and validPlace"
  , "                    (and (not winner)"
  , "                         (not filledBoard)))"
  , "          (1)"
  ]

testShowBoard1 = unlines
  [ "main = or (0)"
  , "               (1)"
  ]

testShowBoard2 = unlines
  [ "main = or (and 1"
  , "                    0)"
  , "               (1)"
  ]

testShowBoard3 = unlines
  [ "main = or (and x"
  , "                    0)"
  , "               (1)"
  ]

testShowBoard4 = unlines
  [ "main = or (and x"
  , "                    (or 0"
  , "                        (1)))"
  , "               (1)"
  ]

testShowBoard5 = unlines
  [ "main = or (or x"
  , "                   (or 0"
  , "                       1))"
  , "               (1)"
  ]

testLetShowBoard0 = unlines
  [ "let showBoard = or (and validPlace"
  , "                        (and (not winner)"
  , "                             (not filledBoard)"
  , "                        )"
  , "                   )"
  , "                   (not boardIn)"
  , "in 0"
  ]

testLetShowBoard1 = unlines
  [ "let showBoard = or (0)"
  , "                   (1)"
  , "in 0"
  ]

testLetShowBoard2 = unlines
  [ "let showBoard = or (and validPlace"
  , "                        1"
  , "                   )"
  , "                   (not boardIn)"
  , "in 0"
  ]

testLetShowBoard3 = unlines
  [ "or (and 1"
  , "        1"
  , "   )"
  , "   (not boardIn)"
  ]

testLetShowBoard4 = unlines
  [ "main = or (and 0"
  , "                    1)"
  , "               (not boardIn)"
  ]

testLetShowBoard5 = unlines
  [ "let showBoard = or (and validPlace"
  , "                        1)"
  , "                   (not boardIn)"
  , "in 0"
  ]

testShowBoard6 = unlines
  [ "or (or x"
  , "       (or 0"
  , "           1))"
  , "   (1)"
  ]

testLetShowBoard8 = unlines
  [ "or (0"
  , "   )"
  , "   1"
  ]
testLetShowBoard9 = unlines
  [ "or 0"
  , "   1"
  ]
