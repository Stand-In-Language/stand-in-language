{-# LANGUAGE LambdaCase          #-}
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
import Data.Fix (Fix (..))
import Data.Functor.Foldable
import Data.List
import qualified Data.List.NonEmpty as NE
import Data.Map (Map, fromList, toList)
import qualified Data.Map as Map
import Data.Ord
import qualified Data.Semigroup as Semigroup
import qualified Data.Set as Set
import Debug.Trace (trace, traceShowId)
import qualified System.IO.Strict as Strict
import System.Process hiding (createPipe)
import Telomare.Driver
import Telomare.Error
import Telomare.Eval.Reference
import Telomare.IR.Base
import Telomare.IR.Builder
import Telomare.IR.Core
import Telomare.IR.Loc
import Telomare.IR.Surface
import Telomare.IR.Types
import Telomare.Parse
import Telomare.Resolve
import Telomare.Sugar
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
tests = testGroup "Parser Tests" [unitTests, sugarTests]

-- |The desugaring pass ('Telomare.Sugar') as a stage of its own: raw
-- parser output goes in, sugar-free trees or 'SugarError's come out.
sugarTests :: TestTree
sugarTests = testGroup "Sugar pass"
  [ testCase "multi-pattern lambda desugars through buildMultiLambda" $ do
      raw <- runTelomareParser parseLongExpr "\\(x, y) z -> x"
      case raw of
        loc :< LamPatUPF pats body ->
          case desugarTerm raw of
            Left err -> assertFailure $ renderSugarError err
            Right desugared ->
              stripParserLocs desugared @?= stripParserLocs (buildMultiLambda loc pats body)
        _ -> assertFailure $ "expected raw LamPatUPF, got: " <> show raw
  , testCase "annotated pattern lambda cases on the validator result" $ do
      raw <- runTelomareParser parseLongExpr "\\(v : Nat) -> v"
      case desugarTerm raw of
        Right (_ :< UnprocessedParsedTermL (LamF binder
                (_ :< CaseUPF
                  (_ :< UnprocessedParsedTermL (AppF
                    (_ :< UnprocessedParsedTermL (VarF "Nat"))
                    (_ :< UnprocessedParsedTermL (VarF bound))))
                  [(Fix (PatternVarF "v"), _)]))) ->
          bound @?= locatedNameText binder
        other -> assertFailure $ "unexpected desugaring: " <> show other
  , testCase "refinement annotation folds into CheckF" $ do
      defs <- runTelomareParser parseDefinitions "main : T = 0\n"
      case desugarDefs defs of
        Right [(name, _ :< UnprocessedParsedTermH (CheckF
                 (_ :< UnprocessedParsedTermL (VarF "T"))
                 (_ :< IntUPF 0)))] ->
          locatedNameText name @?= "main"
        other -> assertFailure $ "unexpected desugaring: " <> show other
  , testCase "list assignment arity mismatch is a SugarError" $ do
      defs <- runTelomareParser parseDefinitions "[a, b] = [1, 2, 3]\n"
      case desugarDefs defs of
        Left (ListArityMismatch _ 2 3) -> pure ()
        other -> assertFailure $ "expected ListArityMismatch: " <> show other
  , testCase "UDT declaration whose body is not a list is a SugarError" $ do
      defs <- runTelomareParser parseDefinitions "[T, mk] = \\h -> 0\n"
      case desugarDefs defs of
        Left (UDTBodyNotList _ "T" _) -> pure ()
        other -> assertFailure $ "expected UDTBodyNotList: " <> show other
  , testCase "wrapMain without a main definition is MissingMain" $ do
      defs <- runTelomareParser parseDefinitions "foo = 0\n"
      (desugarDefs defs >>= wrapMain []) @?= Left MissingMain
  , testCase "desugared tictactoe.tel contains no raw sugar constructors" $ do
      content <- Strict.readFile "tictactoe.tel"
      case runParseModule "" content >>= first renderSugarError . desugarModule of
        Left err -> assertFailure err
        Right items ->
          let terms = either (: []) ((: []) . snd) =<< items
          in all noRawSugar terms @?= True
  ]

-- |No 'LamPatUPF', 'LetSugarUPF' or 'UDTUPF' anywhere, including inside
-- pattern annotations.
noRawSugar :: AUPT -> Bool
noRawSugar (_ :< term) = case term of
  LamPatUPF _ _        -> False
  LetSugarUPF _ _      -> False
  UDTUPF _ _           -> False
  CaseUPF scrutinee alternatives ->
    noRawSugar scrutinee
    && all (\(p, b) -> noRawSugarPattern p && noRawSugar b) alternatives
  other                -> all noRawSugar other

noRawSugarPattern :: PatternA -> Bool
noRawSugarPattern (Fix pat) = case pat of
  PatternAnnotatedF inner (AnnotatedUPT t) -> noRawSugarPattern inner && noRawSugar t
  other -> all noRawSugarPattern other

unitTests :: TestTree
unitTests = testGroup "Unit tests"
  [ testCase "parse uniqueUP" $ do
      res <- parseSuccessful parseHash "# (\\x -> x)"
      res @?= True
    -- Keep structured Megaparsec errors available for LSP ranges while
    -- preserving pretty text for CLI-style diagnostics.
  , testCase "runParseModuleDetailed exposes parse error offsets for diagnostics" $ do
      case runParseModuleDetailed "" "main = if 0 then 1" of
        Left bundle -> do
          errorOffset (NE.head $ bundleErrors bundle) >= 0 @?= True
          null (errorBundlePretty bundle) @?= False
        Right _     -> assertFailure "expected parse error"
    -- Source spans must cover only the token, not whitespace consumed by
    -- lexeme wrappers, otherwise editor diagnostics underline too much.
  , testCase "variable source spans exclude trailing whitespace" $ do
      case runParser parseVariable "" "foo   0" of
        Left err -> assertFailure $ errorBundlePretty err
        Right (SourceLoc span :< UnprocessedParsedTermL (VarF "foo")) -> do
          sourcePositionLine (sourceSpanStart span) @?= 1
          sourcePositionColumn (sourceSpanStart span) @?= 1
          sourcePositionLine (sourceSpanEnd span) @?= 1
          sourcePositionColumn (sourceSpanEnd span) @?= 4
        Right parsed -> assertFailure $ "unexpected parse result: " <> show parsed
  , testCase "let binding source spans exclude trailing whitespace" $ do
      case runParser parseLongExpr "" "let foo   = 0 in foo" of
        Left err -> assertFailure $ errorBundlePretty err
        Right (_ :< LetSugarUPF [SingleDefF name Nothing _] _) | SourceLoc span <- locatedNameLoc name -> do
          locatedNameText name @?= "foo"
          sourcePositionLine (sourceSpanStart span) @?= 1
          sourcePositionColumn (sourceSpanStart span) @?= 5
          sourcePositionLine (sourceSpanEnd span) @?= 1
          sourcePositionColumn (sourceSpanEnd span) @?= 8
        Right parsed -> assertFailure $ "unexpected parse result: " <> show parsed
  , testCase "lambda binding source spans exclude trailing whitespace" $ do
      case runParser parseLongExpr "" "\\foo   -> foo" of
        Left err -> assertFailure $ errorBundlePretty err
        Right (_ :< LamPatUPF [(binderLoc, Fix (PatternVarF "foo"))] _) -> case binderLoc of
          SourceLoc span -> do
            sourcePositionLine (sourceSpanStart span) @?= 1
            sourcePositionColumn (sourceSpanStart span) @?= 2
            sourcePositionLine (sourceSpanEnd span) @?= 1
            sourcePositionColumn (sourceSpanEnd span) @?= 5
          loc -> assertFailure $ "unexpected lambda binder location: " <> show loc
        Right parsed -> assertFailure $ "unexpected parse result: " <> show parsed
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
      res <- parseSuccessful (parseDefinitions <* eof) testParseAssignmentwCLwITEwPair1
      res @?= True
  , testCase "test if testParseTopLevelwCLwITEwPair parses successfuly" $ do
      res <- parseSuccessful (parseDefinitions <* eof) testParseTopLevelwCLwITEwPair
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
      res <- parseSuccessful (parseDefinitions <* scn <* eof) testShowBoard0
      res @?= True
  , testCase "testShowBoard1" $ do
      res <- parseSuccessful (parseDefinitions <* scn <* eof) testShowBoard1
      res @?= True
  , testCase "testShowBoard2" $ do
      res <- parseSuccessful (parseDefinitions <* scn <* eof) testShowBoard2
      res @?= True
  , testCase "testShowBoard3" $ do
      res <- parseSuccessful (parseDefinitions <* scn <* eof) testShowBoard3
      res @?= True
  , testCase "testShowBoard4" $ do
      res <- parseSuccessful (parseDefinitions <* scn <* eof) testShowBoard4
      res @?= True
  , testCase "testShowBoard5" $ do
      res <- parseSuccessful (parseDefinitions <* scn <* eof) testShowBoard5
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
      res <- parseSuccessful (parseDefinitions <* scn <* eof) testLetShowBoard4
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
      defs <- runTelomareParser parseDefinitions caseExpr0
      case desugarDefs defs >>= wrapMain [] of
        Left err  -> assertFailure $ renderSugarError err
        Right res -> stripParserLocs res @?= caseExpr0UPT
  , testCase "Simple import parsing" $ do
      res' <- runTelomareParser parseImport importExpr0str
      stripParserLocs res' @?= importExpr0
  , testCase "Simple import qualified parsing" $ do
      res' <- runTelomareParser parseImportQualified importQualifiedExpr0str
      stripParserLocs res' @?= importQualifiedExpr0
  , testCase "Simple import parsing with ." $ do
      res' <- runTelomareParser parseImport importExpr1str
      stripParserLocs res' @?= importExpr1
  , testCase "Simple import qualified parsing with ." $ do
      res' <- runTelomareParser parseImportQualified importQualifiedExpr1str
      stripParserLocs res' @?= importQualifiedExpr1
  ]

importQualifiedExpr1str = "import qualified Data.List as L"
importQualifiedExpr1 = UnknownLoc :< ImportQualifiedUPF "L" "Data.List"

importExpr1str = "import Control.Monad"
importExpr1 = UnknownLoc :< ImportUPF "Control.Monad"

importQualifiedExpr0str = "import qualified Foo as F"
importQualifiedExpr0 = UnknownLoc :< ImportQualifiedUPF "F" "Foo"

importExpr0str = "import Foo"
importExpr0 = UnknownLoc :< ImportUPF "Foo"

stripParserLocs :: AUPT -> AUPT
stripParserLocs (loc :< term) = UnknownLoc :< case term of
  LetUPF bindings body -> LetUPF ((\(name, value) -> (locatedName UnknownLoc $ locatedNameText name, stripParserLocs value)) <$> bindings) (stripParserLocs body)
  UnprocessedParsedTermL (LamF name body) -> UnprocessedParsedTermL (LamF (locatedName UnknownLoc $ locatedNameText name) (stripParserLocs body))
  CaseUPF scrutinee cases -> CaseUPF (stripParserLocs scrutinee) (bimap stripPatternLocs stripParserLocs <$> cases)
  LamPatUPF pats body -> LamPatUPF (bimap (const UnknownLoc) stripPatternLocs <$> pats) (stripParserLocs body)
  LetSugarUPF defs body -> LetSugarUPF (stripDefinitionLocs <$> defs) (stripParserLocs body)
  other -> stripParserLocs <$> other

stripDefinitionLocs :: DefinitionF AUPT -> DefinitionF AUPT
stripDefinitionLocs = \case
  SingleDefF name annot value ->
    SingleDefF (locatedName UnknownLoc $ locatedNameText name)
               (bimap (const UnknownLoc) stripParserLocs <$> annot)
               (stripParserLocs value)
  ListDefF _ names value ->
    ListDefF UnknownLoc (locatedName UnknownLoc . locatedNameText <$> names) (stripParserLocs value)

stripPatternLocs :: PatternA -> PatternA
stripPatternLocs (Fix patternF) = Fix $ case patternF of
  PatternAnnotatedF pat term -> PatternAnnotatedF (stripPatternLocs pat) (AnnotatedUPT . stripParserLocs $ unAnnotatedUPT term)
  other -> stripPatternLocs <$> other

caseExpr0UPT =
  UnknownLoc :< LetUPF
    [ ( locatedName UnknownLoc "foo"
      , UnknownLoc :< UnprocessedParsedTermL (LamF (locatedName UnknownLoc "a")
          (UnknownLoc :< CaseUPF (UnknownLoc :< UnprocessedParsedTermL (VarF "a"))
            [ (Fix $ PatternIntF 0, UnknownLoc :< UnprocessedParsedTermL (VarF "a"))
            , (Fix $ PatternVarF "x", UnknownLoc :< UnprocessedParsedTermL (AppF (UnknownLoc :< UnprocessedParsedTermL (VarF "succ")) (UnknownLoc :< UnprocessedParsedTermL (VarF "a"))))
            ]))
      )
    , ( locatedName UnknownLoc "main"
      , UnknownLoc :< UnprocessedParsedTermL (LamF (locatedName UnknownLoc "i")
          (UnknownLoc :< UnprocessedParsedTermB (PairSF (UnknownLoc :< StringUPF "Success") (UnknownLoc :< IntUPF 0))))
      )
    ]
    (UnknownLoc :< UnprocessedParsedTermL (LamF (locatedName UnknownLoc "i")
      (UnknownLoc :< UnprocessedParsedTermB (PairSF (UnknownLoc :< StringUPF "Success") (UnknownLoc :< IntUPF 0)))))
caseExpr0 = unlines
  [ "foo = \\a -> case a of"
  , "              0 -> a"
  , "              x -> succ a"
  , ""
  , "main = \\i -> (\"Success\", 0)"
  ]

test2UPT str =
  case runParseModule "" str >>= first renderSugarError . desugarModule of
    Right _ -> return True
    Left _  -> return False

testWtictactoe = Strict.readFile "tictactoe.tel" >>= test2UPT

runTestMainwCLwITEwPair = test2UPT testMainwCLwITEwPair

runTestMainWType = test2UPT "main : (\\x -> if x then \"fail\" else 0) = 0"

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
  case runParseDefinitions "" preludeFile >>= first renderSugarError . desugarDefs of
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
