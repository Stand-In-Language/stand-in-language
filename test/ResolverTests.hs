{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Main where

import CaseTests (qcPropsCase, unitTestsCase)
import Common
import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Exception (SomeException, try)
import Control.Monad.Except (ExceptT, MonadError, catchError, runExceptT,
                             throwError)
import Data.Algorithm.Diff (getGroupedDiff)
import Data.Algorithm.DiffOutput (ppDiff)
import Debug.Trace (trace, traceShow, traceShowId)
import System.IO
import qualified System.IO.Strict as Strict
import System.IO.Unsafe (unsafePerformIO)
import System.Posix.IO
import System.Posix.Process
import System.Posix.Types
import Telomare
import Telomare.Eval
import Telomare.Parser
import Telomare.Resolver
import Telomare.RunTime
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC
import Text.Megaparsec (eof)
import Text.Show.Pretty (ppShow)

type Term2' = ParserTerm () Int

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTests, qcProps, unitTestsCase, qcPropsCase]

---------------------
------ Property Tests
---------------------

qcProps = testGroup "Property tests (QuickCheck)"
  [ QC.testProperty "Arbitrary UnprocessedParsedTerm to test hash uniqueness of HashUP's" $
      \x' -> withMaxSuccess 16 $
        let x = forget x'
        in containsTHash x QC.==> checkAllHashes . forget . generateAllHashes $ x'
  , QC.testProperty "See that generateAllHashes only changes HashUP to ListUP" $
      \(x' :: Term2) -> withMaxSuccess 16 $
        let x = forget x'
        in containsTHash x QC.==> onlyHashUPsChanged x
  , QC.testProperty "Check recursive imports work" $
      \() -> withMaxSuccess 16 . QC.idempotentIOProperty $ do
        modules <- generate genRecursiveImports
        let expectedValue = recursiveImportsResult modules <> "\ndone"
        result <- runMain_ modules "Main"
        pure $ result === expectedValue
  , QC.testProperty "Cyclic imports are stopped to avoid loops" $
      \() -> withMaxSuccess 16 . QC.idempotentIOProperty $ do
        modules <- generate genRecursiveImportsWithCycle
        result <- try (runMain_ modules "Main") :: IO (Either SomeException String)
        let cycleModules = concat (detectCycle (constructModules modules))
            unwrappedExpectedError = formatCycleError cycleModules
            expectedError = "failed to parse Main " <> unwrappedExpectedError
        case result of
          Left err  -> pure $ trimEnd (removeCallStack (show err)) === trimEnd expectedError
          Right res -> pure $ res === trimEnd expectedError
  , QC.testProperty "Check recursive let work backward" $
      \() -> withMaxSuccess 16 . QC.idempotentIOProperty $ do
        assignments <- generate genRecursiveLet
        let dummymodule = wrapRecursiveBackwardLet assignments
            expectedValue = recursiveLetResult assignments <> "\ndone"
        result <- testUserDefAdHocTypes dummymodule
        pure $ result === expectedValue
  , QC.testProperty "Check recursive let work forward" $
      \() -> withMaxSuccess 16 . QC.idempotentIOProperty $ do
        assignments <- generate genRecursiveLet
        let dummymodule = wrapRecursiveForwardLet assignments
            expectedValue = recursiveLetResult assignments <> "\ndone"
        result <- testUserDefAdHocTypes dummymodule
        pure $ result === expectedValue
  -- TODO: Refactor with runCycleLet responses
  -- , QC.testProperty "Cyclic let backward are stopped to avoid loops" $
  --     \() -> withMaxSuccess 16 . QC.idempotentIOProperty $ do
  --       assignments <- generate genRecursiveLetWithCycle
  --       let dummymodule = wrapRecursiveBackwardLet assignments
  --           expectedValue = recursiveLetResult assignments <> "\ndone"
  --       result <- testUserDefAdHocTypes dummymodule
  --       pure $ result === expectedValue
  -- , QC.testProperty "Cyclic let forward are stopped to avoid loops" $
  --     \() -> withMaxSuccess 16 . QC.idempotentIOProperty $ do
  --       assignments <- generate genRecursiveLetWithCycle
  --       let dummymodule = wrapRecursiveForwardLet assignments
  --           expectedValue = recursiveLetResult assignments <> "\ndone"
  --       result <- testUserDefAdHocTypes dummymodule
  --       pure $ result === expectedValue
  ]

removeCallStack :: String -> String
removeCallStack = unlines . takeWhile (/= "CallStack (from HasCallStack):") . lines

recursiveResult :: String -> String
recursiveResult = init . tail . drop 2 . dropWhile (/= '=')

recursiveLetResult :: [String] -> String
recursiveLetResult = recursiveResult . last

recursiveImportsResult :: [(String, String)] -> String
recursiveImportsResult = recursiveResult . snd . last

-- Variable and Import str generator
genName :: Gen String
genName = do
  firstChar <- elements $ ['a'..'z'] <> ['A'..'Z']
  len <- choose (3, 15)
  rest <- vectorOf (len - 1)
                   (frequency [ (10, elements (['a'..'z'] <> ['A'..'Z'] <> ['0'..'9']))
                              , (1, pure '_')
                              , (1, pure '.')
                              ])
  pure $ firstChar : rest

removeDuplicates :: Eq a => [a] -> [a]
removeDuplicates = foldr (\x acc -> if x `elem` acc then acc else x : acc) []

genAssignment :: Gen (String, String)
genAssignment = do
  varName <- genName
  value <- genName
  pure (varName, varName <> " = " <> show value)

genRecursiveImports :: Gen [(String, String)]
genRecursiveImports = do
  numModules               <- choose (3, 7)
  rawModuleNames           <- vectorOf numModules genName
  let moduleNames = removeDuplicates $ filter (/= "Main") rawModuleNames
  (varName, assignmentStr) <- genAssignment
  let
    assignments = fmap ( "import " <> ) (tail moduleNames) <> [assignmentStr]
    mainModule  = ("Main", "import " <> head moduleNames <> "\nmain = \\input -> (" <> varName <> ",0)")
  pure $ mainModule : zip moduleNames assignments

genRecursiveImportsWithCycle :: Gen [(String, String)]
genRecursiveImportsWithCycle = do
  modules <- genRecursiveImports
  let moduleNames = fmap fst modules
  cycleModuleIndex <- choose (1, length modules - 1)
  let (before, (modName, modContent) : after) = splitAt cycleModuleIndex modules
      modContent' = modContent <> "\nimport Main"
  pure $ before <> ((modName, modContent') : after)

genRecursiveLetWithCycle :: Gen [String]
genRecursiveLetWithCycle = do
  assignments <- genRecursiveLet
  cycleLetIndex <- choose (1, length assignments - 1)
  let (before, assignment : after) = splitAt cycleLetIndex assignments
      assignment' = takeWhile (/= '=') assignment
                 <> "= concat ["
                 <> (drop 2 . dropWhile (/= '=')) assignment
                 <> " , "
                 <> ( takeWhile (/= ' ' ) . head) assignments
                 <> "]"
  pure $ before <> [assignment'] <> after

genRecursiveLet :: Gen [String]
genRecursiveLet = do
  numLines <- choose (4, 8)
  rawVarNames <- vectorOf numLines genName
  lastValue <- genName
  let varNames = (fmap ( filter (/= '.') ) . removeDuplicates) $
                 filter (`notElem` ["Main", "input"]) rawVarNames
      assignments = fmap (\i -> varNames !! i <> " = " <> varNames !! (i + 1)) [0 .. length varNames - 2]
      lastVar = last varNames
      lastLine = lastVar <> " = " <> show lastValue
  pure (assignments <> [lastLine])

linewrap :: String -> String -> String -> String
linewrap firstAssignment letBlock firstVar =
  unlines
    [ "import Prelude"
    , "main = let " <> firstAssignment
    , letBlock <> "       in \\input -> (" <> firstVar <> ", 0)"
    ]

wrapRecursiveForwardLet :: [String] -> String
wrapRecursiveForwardLet assignments = do
  let firstVar = takeWhile (/= ' ') (head assignments)
      firstAssignment = head assignments
      letBlock = unlines $ fmap ("           " <>) (tail assignments)
  linewrap firstAssignment letBlock firstVar

wrapRecursiveBackwardLet :: [String] -> String
wrapRecursiveBackwardLet assignments = do
  let firstVar = takeWhile (/= ' ') (head assignments)
      firstAssignment = last assignments
      letBlock = unlines $ fmap ("           " <>) ((tail . reverse) assignments)
  linewrap firstAssignment letBlock firstVar

containsTHash :: Term2' -> Bool
containsTHash = \case
  THash _    -> True
  TLimitedRecursion a b c -> containsTHash a || containsTHash b || containsTHash c
  TITE a b c -> containsTHash a || containsTHash b || containsTHash c
  TPair a b  -> containsTHash a || containsTHash b
  TApp a b   -> containsTHash a || containsTHash b
  TCheck a b -> containsTHash a || containsTHash b
  TLam _ a   -> containsTHash a
  TLeft a    -> containsTHash a
  TRight a   -> containsTHash a
  TTrace a   -> containsTHash a
  x          -> False

onlyHashUPsChanged :: Term2' -> Bool
onlyHashUPsChanged term2 = all (isHash . fst) diffList where
  diffList :: [(Term2', Term2')]
  diffList = diffTerm2 (term2, forget . generateAllHashes . tag DummyLoc $ term2)
  isHash :: Term2' -> Bool
  isHash = \case
    THash _ -> True
    _       -> False

checkAllHashes :: Term2' -> Bool
checkAllHashes = noDups . allHashesToTerm2

noDups = not . f []
  where
    f seen (x:xs) = x `elem` seen || f (x:seen) xs
    f seen []     = False

allHashesToTerm2 :: Term2' -> [Term2']
allHashesToTerm2 term2 =
  let term2WithoutTHash = forget . generateAllHashes . tag DummyLoc $ term2
      interm :: (Term2', Term2') -> [Term2']
      interm = \case
        (THash _ , x) -> [x]
        (TITE a b c, TITE a' b' c') -> interm (a, a') <> interm (b, b') <> interm (c, c')
        (TLimitedRecursion a b c, TLimitedRecursion a' b' c') -> interm (a, a') <> interm (b, b') <> interm (c, c')
        (TPair a b, TPair a' b') -> interm (a, a') <> interm (b, b')
        (TApp a b, TApp a' b') -> interm (a, a') <> interm (b, b')
        (TCheck a b, TCheck a' b') -> interm (a, a') <> interm (b, b')
        (TLam _ a, TLam _ a') -> interm (a, a')
        (TLeft a, TLeft a') -> interm (a, a')
        (TRight a, TRight a') -> interm (a, a')
        (TTrace a, TTrace a') -> interm (a, a')
        (x, x') | x /= x' -> error "x and x' should be the same (inside of allHashesToTerm2, within interm)"
        (x, x') -> []
  in curry interm term2 term2WithoutTHash

diffTerm2 :: (Term2', Term2') -> [(Term2', Term2')]
diffTerm2 = \case
  (TITE a b c, TITE a' b' c') -> diffTerm2 (a, a') <> diffTerm2 (b, b') <> diffTerm2 (c, c')
  (TLimitedRecursion a b c, TLimitedRecursion a' b' c') -> diffTerm2 (a, a') <> diffTerm2 (b, b') <> diffTerm2 (c, c')
  (TPair a b, TPair a' b') -> diffTerm2 (a, a') <> diffTerm2 (b, b')
  (TApp a b, TApp a' b') -> diffTerm2 (a, a') <> diffTerm2 (b, b')
  (TCheck a b, TCheck a' b') -> diffTerm2 (a, a') <> diffTerm2 (b, b')
  (TLam _ a, TLam _ a') -> diffTerm2 (a, a')
  (TLeft a, TLeft a') -> diffTerm2 (a, a')
  (TRight a, TRight a') -> diffTerm2 (a, a')
  (TTrace a, TTrace a') -> diffTerm2 (a, a')
  (x, x') | x /= x' -> [(x, x')]
  _ -> []

-----------------
------ Unit Tests
-----------------

unitTests :: TestTree
unitTests = testGroup "Unit tests"
  [
    testCase "different values get different hashes" $ do
      let res1 = generateAllHashes <$> runTelomareParser2Term2 parseLet hashtest0
          res2 = generateAllHashes <$> runTelomareParser2Term2 parseLet hashtest1
      (res1 == res2) `compare` False @?= EQ
  , testCase "same functions have the same hash even with different variable names" $ do
     let res1 = generateAllHashes <$> runTelomareParser2Term2 parseLet hashtest2
         res2 = generateAllHashes <$> runTelomareParser2Term2 parseLet hashtest3
     res1 @?= res2
  , testCase "Ad hoc user defined types success" $ do
      res <- testUserDefAdHocTypes userDefAdHocTypesSuccess
      res @?= "\a\ndone"
  , testCase "Ad hoc user defined types failure" $ do
      res <- testUserDefAdHocTypes userDefAdHocTypesFailure
      res @?= "MyInt must not be 0\ndone"
  , testCase "test automatic open close lambda" $ do
      res <- runTelomareParser (parseLambda <* scn <* eof) "\\x -> \\y -> (x, y)"
      (forget <$> validateVariables res) @?= Right closedLambdaPair
  , testCase "test automatic open close lambda 2" $ do
      res <- runTelomareParser (parseLambda <* scn <* eof) "\\x y -> (x, y)"
      (forget <$> validateVariables res) @?= Right closedLambdaPair
  , testCase "test automatic open close lambda 3" $ do
      res <- runTelomareParser (parseLambda <* scn <* eof) "\\x -> \\y -> \\z -> z"
      (forget <$> validateVariables res) @?= Right expr6
  , testCase "test automatic open close lambda 4" $ do
      res <- runTelomareParser (parseLambda <* scn <* eof) "\\x -> (x, x)"
      (forget <$> validateVariables res) @?= Right expr5
  , testCase "test automatic open close lambda 5" $ do
      res <- runTelomareParser (parseLambda <* scn <* eof) "\\x -> \\x -> \\x -> x"
      (forget <$> validateVariables res) @?= Right expr4
  , testCase "test automatic open close lambda 6" $ do
      res <- runTelomareParser (parseLambda <* scn <* eof) "\\x -> \\y -> \\z -> [x,y,z]"
      (forget <$> validateVariables res) @?= Right expr3
  , testCase "test automatic open close lambda 7" $ do
      res <- runTelomareParser (parseLambda <* scn <* eof) "\\a -> (a, (\\a -> (a,0)))"
      (forget <$> validateVariables res) @?= Right expr2
  , testCase "test tictactoe.tel" $ do
      res <- tictactoe
      res @?= fullRunTicTacToeString
  , testCase "test recursive imports" $ do
      res <- runMain_ aux222 "Main"
      res @?= "whattt\ndone"
  , testCase "test recursive imports with simple cycle" $ do
      result <- try (runMain_ simpleCycle "Main") :: IO (Either SomeException String)
      let trimEnd s = reverse (dropWhile (`elem` [' ', '\n']) (reverse s))
      case result of
          Left err -> trimEnd (removeCallStack (show err)) @?= trimEnd runsimpleCycle
          Right res -> trimEnd res @?= trimEnd runsimpleCycle
  , testCase "test recursive imports with full cycle" $ do
      result <- try (runMain_ fullCycle "Main") :: IO (Either SomeException String)
      case result of
          Left err -> trimEnd (removeCallStack (show err)) @?= trimEnd runfullCycle
          Right res -> trimEnd res @?= trimEnd runfullCycle
  , testCase "test recursive backward let" $ do
      res <- testUserDefAdHocTypes recursiveBackwardLet
      res @?= "whattt\ndone"
  , testCase "test recursive forward let" $ do
      res <- testUserDefAdHocTypes recursiveForwardLet
      res @?= "whattt\ndone"
  -- TODO: Refactor with runCycleLet responses
  , testCase "test backward cycle let" $ do
      res <- testUserDefAdHocTypes backwardCycleLet
      res @?= "whattt\ndone"
  , testCase "test forward cycle let" $ do
      res <- testUserDefAdHocTypes forwardCycleLet
      res @?= "whattt\ndone"
  ]

runCycleLet = undefined

backwardCycleLet = unlines
  [ "import Prelude"
  , "main = let ghi = succ abc"
  , "           def = ghi"
  , "           abc = def"
  , "       in \\input -> (abc, 0)"
  ]

forwardCycleLet = unlines
  [ "import Prelude"
  , "main = let abc = def"
  , "           def = ghi"
  , "           ghi = succ abc"
  , "       in \\input -> (abc, 0)"
  ]

recursiveBackwardLet = unlines
  [ "main = let xyz = \"whattt\""
  , "           ghi = xyz"
  , "           def = ghi"
  , "           abc = def"
  , "       in  \\input -> (abc, 0)"
  ]

recursiveForwardLet = unlines
  [ "main = let abc = def"
  , "           def = ghi"
  , "           ghi = xyz"
  , "           xyz = \"whattt\""
  , "       in \\input -> (abc, 0)"
  ]

aux222 =
  [ ("Main", "import Abc\nmain = \\input -> (xyz, 0)")
  , ("Abc", "import Def")
  , ("Def", "import Ghi")
  , ("Ghi", "xyz = \"whattt\"")
  ]

fullCycle =
  [ ("Main", "import Abc\nmain = \\input -> (xyz, 0)")
  , ("Abc", "import Def")
  , ("Def", "import Ghi")
  , ("Ghi", "import Jkl")
  , ("Jkl", "import Main\nxyz = \"whattt\"")]

runfullCycle = unlines
  [ "failed to parse Main "
  , "Module imports form a cycle:"
  , "      module Main"
  , "      imports module Abc"
  , "which imports module Def"
  , "which imports module Ghi"
  , "which imports module Jkl"
  , "which imports module Main"
  ]

simpleCycle =
  [ ("Main","import Abc\nmain = \\input -> (xyz,0)")
  , ("Abc","import Def\nimport Main")
  , ("Def","import Ghi")
  , ("Ghi","import Jkl")
  , ("Jkl","xyz = \"CdVK\"")]

runsimpleCycle= unlines
  [ "failed to parse Main "
  , "Module imports form a cycle:"
  , "      module Main"
  , "      imports module Abc"
  , "which imports module Main"
  ]

tictactoe :: IO String
tictactoe = do
  telStr <- Strict.readFile "tictactoe.tel"
  preludeStr <- Strict.readFile "Prelude.tel"
  runMainWithInput ["1", "9", "2", "8", "3"] [("Prelude", preludeStr), ("tictactoe", telStr)] "tictactoe"

fullRunTicTacToeString = init . unlines $
  [ "1|2|3"
  , "-+-+-"
  , "4|5|6"
  , "-+-+-"
  , "7|8|9"
  , "Player 2's turn"
  , "please input number of square: "
  , "O|2|3"
  , "-+-+-"
  , "4|5|6"
  , "-+-+-"
  , "7|8|9"
  , "Player 1's turn"
  , "please input number of square: "
  , "O|2|3"
  , "-+-+-"
  , "4|5|6"
  , "-+-+-"
  , "7|8|X"
  , "Player 2's turn"
  , "please input number of square: "
  , "O|O|3"
  , "-+-+-"
  , "4|5|6"
  , "-+-+-"
  , "7|8|X"
  , "Player 1's turn"
  , "please input number of square: "
  , "O|O|3"
  , "-+-+-"
  , "4|5|6"
  , "-+-+-"
  , "7|X|X"
  , "Player 2's turn"
  , "please input number of square: "
  , "Player 2 wins!"
  , "done"
  ]

-- | Telomare Parser AST representation of: \x -> \y -> \z -> z
expr6 =
  TLam (Closed "x")
       (TLam (Closed "y")
         (TLam (Closed "z")
           (TVar "z")))

-- | Telomare Parser AST representation of: \x -> (x, x)
expr5 = TLam (Closed "x")
          (TPair
            (TVar "x")
            (TVar "x"))

-- | Telomare Parser AST representation of: \x -> \x -> \x -> x
expr4 = TLam (Closed "x")
          (TLam (Closed "x")
            (TLam (Closed "x")
              (TVar "x")))

-- | Telomare Parser AST representation of: \x -> \y -> \z -> [x,y,z]
expr3 = TLam (Closed "x")
          (TLam (Open "y")
            (TLam (Open "z")
              (TPair
                (TVar "x")
                (TPair
                  (TVar "y")
                  (TPair
                    (TVar "z")
                    TZero)))))

-- | Telomare Parser AST representation of: \a -> (a, (\a -> (a,0)))
expr2 = TLam (Closed "a")
          (TPair
            (TVar "a")
            (TLam (Closed "a")
              (TPair
                (TVar "a")
                TZero)))

closedLambdaPair = TLam (Closed "x") (TLam (Open "y") (TPair (TVar "x") (TVar "y")))

testUserDefAdHocTypes :: String -> IO String
testUserDefAdHocTypes input = do
  preludeString <- Strict.readFile "Prelude.tel"
  runMain_ [("Prelude", preludeString), ("DummyModule", input)] "DummyModule"

userDefAdHocTypesSuccess = unlines
  [ "import Prelude"
  , "MyInt = let wrapper = \\h -> ( \\i -> if not i"
  , "                                      then \"MyInt must not be 0\""
  , "                                      else  i"
  , "                             , \\i -> if dEqual (left i) h"
  , "                                      then 0"
  , "                                      else \"expecting MyInt\""
  , "                             )"
  , "        in wrapper (# wrapper)"
  , "main = \\i -> ((left MyInt) 8, 0)"
  ]

userDefAdHocTypesFailure = unlines
  [ "import Prelude"
  , "MyInt = let wrapper = \\h -> ( \\i -> if not i"
  , "                                      then \"MyInt must not be 0\""
  , "                                      else  i"
  , "                             , \\i -> if dEqual (left i) h"
  , "                                      then 0"
  , "                                      else \"expecting MyInt\""
  , "                             )"
  , "        in wrapper (# wrapper)"
  , "main = \\i -> ((left MyInt) 0, 0)"
  ]

hashtest0 = unlines ["let wrapper = 2",
                "  in (# wrapper)"]

hashtest1 = unlines ["let var = 3",
                "  in (# var)"]
hashtest2 = unlines [ "let a = \\y -> y"
               , "in (# a)"
               ]
hashtest3 = unlines [ "let b = \\x -> x"
               , "in (# b)"
               ]

-- TODO: do something with this
showAllTransformations :: String -- ^ Telomare code
                       -> IO ()
showAllTransformations input = do
  preludeFile <- Strict.readFile "Prelude.tel"
  let section description body = do
        putStrLn "\n-----------------------------------------------------------------"
        putStrLn $ "----" <> description <> ":\n"
        putStrLn body
      prelude = case parsePrelude preludeFile of
                  Right x  -> x
                  Left err -> error err
      upt = case parseWithPrelude prelude input of
              Right x -> x
              Left x  -> error x
  section "Input" input
  section "UnprocessedParsedTerm" $ show upt
  section "optimizeBuiltinFunctions" . show . optimizeBuiltinFunctions $ upt
  let optimizeBuiltinFunctionsVar = optimizeBuiltinFunctions upt
      str1 = lines . show $ optimizeBuiltinFunctionsVar
      str0 = lines . show $ upt
      diff = getGroupedDiff str0 str1
  section "Diff optimizeBuiltinFunctions" $ ppDiff diff
  -- let optimizeBindingsReferenceVar = optimizeBindingsReference optimizeBuiltinFunctionsVar
  --     str2 = lines . show $ optimizeBindingsReferenceVar
  --     diff = getGroupedDiff str1 str2
  -- section "optimizeBindingsReference" . show $ optimizeBindingsReferenceVar
  -- section "Diff optimizeBindingsReference" $ ppDiff diff
  let validateVariablesVar = validateVariables optimizeBuiltinFunctionsVar
      str3 = lines . show $ validateVariablesVar
      diff = getGroupedDiff str3 str1
  section "validateVariables" . show $ validateVariablesVar
  section "Diff validateVariables" $ ppDiff diff
  let Right debruijinizeVar = (>>= debruijinize []) validateVariablesVar
      str4 = lines . show $ debruijinizeVar
      diff = getGroupedDiff str4 str3
  section "debruijinize" . show $ debruijinizeVar
  section "Diff debruijinize" $ ppDiff diff
  let splitExprVar = splitExpr debruijinizeVar
      str5 = lines . ppShow $ splitExprVar
      diff = getGroupedDiff str5 str4
  section "splitExpr" . ppShow $ splitExprVar
  section "Diff splitExpr" $ ppDiff diff
  let Right (Just toTelomareVar) = fmap toTelomare . findChurchSize $ splitExprVar
      str6 = lines . show $ toTelomareVar
      diff = getGroupedDiff str6 str5
  section "toTelomare" . show $ toTelomareVar
  section "Diff toTelomare" $ ppDiff diff
  putStrLn "\n-----------------------------------------------------------------"
  putStrLn "---- stepEval:\n"
  x <- stepIEval toTelomareVar
  print x
  -- let iEvalVar0 = iEval () Zero toTelomareVar

stepIEval :: IExpr -> IO IExpr
stepIEval =
  let wio :: IExpr -> IExpr
      wio = rEval Zero
  in pure . wio

newtype WrappedIO a = WrappedIO
  { wioIO :: IO a
  } deriving (Functor)

instance Show (WrappedIO IExpr) where
  show = show . unsafePerformIO . wioIO

instance Applicative WrappedIO where
  pure = WrappedIO . pure
  (<*>) (WrappedIO f) (WrappedIO a) = WrappedIO $ f <*> a

instance Monad WrappedIO where
  (>>=) (WrappedIO a) f = WrappedIO $ a >>= wioIO . f

instance (MonadError RunTimeError) WrappedIO where
  throwError = undefined
  catchError = undefined
