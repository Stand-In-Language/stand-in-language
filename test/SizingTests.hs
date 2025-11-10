module SizingTests where

import Control.Applicative (liftA2)
import Control.Exception (SomeException, evaluate, try)
import Control.Monad.IO.Class
import Control.Monad.Reader (Reader, runReader)
import qualified Control.Monad.State as State
import Data.Bifunctor
import Data.Char
import Data.List (partition)
import qualified Data.Map as Map
import Data.Monoid
import Debug.Trace
import Naturals
import System.Exit
import System.IO
import qualified System.IO.Strict as Strict
import Telomare
import Telomare.Decompiler
import Telomare.Eval
import Telomare.Optimizer
import Telomare.Parser
import Telomare.Possible (evalBU, evalBU')
import Telomare.Resolver
import Telomare.RunTime
import Telomare.TypeChecker
import Test.Hspec
import Test.Hspec.Core.QuickCheck (modifyMaxSuccess)
import Test.QuickCheck

-- Common datatypes for generating Telomare AST.
import Common



{- works for now!
-- | Creates a simplified version of the test defined in Spec.hs that fails when
-- | using sizing but passes when using a fixed size of 255
createMinimalSizingTest :: Spec
createMinimalSizingTest = do

  describe "tests highlight divergence of sizing behavior" $ do
    -- Minimal test content
    testContent <- runIO $ Strict.readFile "tc.tel"
    parsedContent <- runIO $ parsePreludeWithFile "Prelude.tel" testContent
    let eval s i = (\g -> sizingFunWrap evalBU g i) <$> compileWithSizing s parsedContent

    -- Test using sizing (throws exception that is caught by test)
    result <- runIO . try @SomeException . evaluate $ eval True (Just ("A", Zero))
    it "Test with sizing (should fail)" $ case result of
        Left _ -> pure () -- Expected to fail with an exception
        Right r -> expectationFailure ("Expected compilation to fail but it succeeded with result:\n" <> show r)

    -- Test using fixed size (should pass)
    result <- runIO . try @SomeException . evaluate $ eval False (Just ("A", Zero))
    it "Test with fixed size (should pass)" $ case result of
        Left e -> expectationFailure ("Exception hit:\n" <> show e)
        Right r -> r `shouldBe` (Right ("R O", Just Zero))
-}

-- | Helper function to parse prelude with a file
-- parsePrelude :: String -> Either String [(String, AnnotatedUPT)]
parsePreludeWithFile :: FilePath -> String -> IO Term3
parsePreludeWithFile preludePath telFile = do
  preludeString <- Strict.readFile preludePath
  case parsePrelude preludeString >>= (`parseMain` telFile) of
    Right p -> pure p
    Left e  -> error e

-- | Compile using our sizing toggle function
compileWithSizing :: Bool -> Term3 -> Either EvalError IExpr
compileWithSizing useSizing term = case typeCheck (PairTypeP (ArrTypeP ZeroTypeP ZeroTypeP) AnyType) term of
  Just e -> Left $ TCE e
  _      -> compileWithSizing' useSizing term

compileWithSizing' :: Bool -> Term3 -> Either EvalError IExpr
compileWithSizing' useSizing t =
  case toTelomare . removeChecks <$> findChurchSizeD useSizing t of
    Right (Just i) -> pure i
    Right Nothing  -> Left CompileConversionError
    Left e         -> Left e

-- | Converts between easily understood Haskell types and untyped IExprs around an iteration of a Telomare expression
-- | Renamed to avoid conflict with Telomare.Eval.funWrap'
sizingFunWrap :: (IExpr -> IExpr) -> IExpr -> Maybe (String, IExpr) -> (String, Maybe IExpr)
sizingFunWrap eval fun inp =
  let iexpInp = case inp of
        Nothing                  -> Zero
        Just (userInp, oldState) -> Pair (s2g userInp) oldState
  in case eval (app fun iexpInp) of
    Zero               -> ("aborted", Nothing)
    Pair disp newState -> (g2s disp, Just newState)
    z                  -> ("runtime error, dumped:\n" <> show z, Nothing)
