{-# LANGUAGE LambdaCase #-}
module SizingTests where

import Control.Applicative (liftA2)
import Control.Exception (SomeException (SomeException), evaluate, try)
import Control.Monad.IO.Class
import Control.Monad.Reader (Reader, runReader)
import qualified Control.Monad.State as State
import Data.Bifunctor
import Data.Char
import Data.List (partition)
import qualified Data.Map as Map
import Data.Monoid
import Debug.Trace
import System.Exit
import System.IO
import qualified System.IO.Strict as Strict
import Telomare
import Telomare.Decompiler
import Telomare.Eval
import Telomare.Parser
import Telomare.Possible (SizingSettings (SizingSettings),
                          UnexpectedGrammarException, appB)
import Telomare.Resolver
import Telomare.RunTime
import Telomare.TypeChecker
import Test.Hspec
import Test.Hspec.Core.QuickCheck (modifyMaxSuccess)
import Test.QuickCheck

-- Common datatypes for generating Telomare AST.
import Common


twoFailedApproaches :: Spec
twoFailedApproaches =
  describe "I wish something like this worked" $ do
    -- Minimal test content
    preludeFile <- runIO $ Strict.readFile "Prelude.tel"
    -- testContent <- runIO $ Strict.readFile "sizing_fail5.tel"
    -- let try' :: IO a -> IO (Either SomeException a)
    let try' :: IO a -> IO (Either UnexpectedGrammarException a)
        try' = try
        prelude' = case parsePrelude preludeFile of
          Right p -> p
          Left pe -> error $ show pe
        prelude :: [(String, [Either AnnotatedUPT (String, AnnotatedUPT)])]
        prelude = [("Prelude", Right <$> prelude')]
        parseAuxModule :: String -> (String, [Either AnnotatedUPT (String, AnnotatedUPT)])
        parseAuxModule str =
          case sequence ("AuxModule", parseModule ("import Prelude\n" <> str)) of
            Left e    -> error $ show e
            Right pam -> pam
        parse :: Bool -> String -> Either String Term3
        parse appLet str = if appLet
          then first show $ main2Term3let (parseAuxModule str:prelude) "AuxModule"
          else first show $ main2Term3 (parseAuxModule str:prelude) "AuxModule"
        buildMainTest ss s = case fmap (compileMain' ss) (parse True s) of
          Right (Right g) -> let eval = funWrap g appB
                                 mi i = "main input " <> i <> " and SizingSettings " <> show ss
                             -- in pure $ \s i e -> it ("main input " <> i) $ eval (Just (i, s)) `shouldBe` e
                             in pure $ \s i e -> runIO (try' . evaluate . eval $ Just (i, s)) >>=
                                                 \case
                                                   Left z -> runIO $ expectationFailure (mi i <> " threw exception " <> show z)
                                                   Right r' -> it (mi i) $ r' `shouldBe` e
          z -> pure $ \ss i e -> runIO . expectationFailure $ "failed to compile main:\n" <> show s <> "\nbecause:\n" <> show z
    -- unitTestMain <- buildMainTest (SizingSettings 255 True) testContent
    -- unitTestMain (Pair (Pair Zero Zero) (Pair Zero (Pair Zero (Pair Zero (Pair Zero (Pair Zero (Pair Zero (Pair Zero (Pair Zero (Pair Zero Zero)))))))))) "3" ("2", Right zeroB)
    pure ()


-- | Helper function to parse prelude with a file
-- parsePrelude :: String -> Either String [(String, AnnotatedUPT)]
parsePreludeWithFile :: FilePath -> String -> IO Term3
parsePreludeWithFile preludePath telFile = do
  preludeString <- Strict.readFile preludePath
  case first ParseError (parsePrelude preludeString) >>= (`parseMain` telFile) of
    Right p -> pure p
    Left e  -> error $ show e

-- | Compile using our sizing toggle function
compileWithSizing :: SizingOption -> Term3 -> Either EvalError CompiledExpr
compileWithSizing useSizing term = case typeCheck (PairTypeP (ArrTypeP ZeroTypeP ZeroTypeP) AnyType) term of
  Just e -> Left $ TCE e
  _      -> compileWithSizing' useSizing term

compileWithSizing' :: SizingOption -> Term3 -> Either EvalError CompiledExpr
compileWithSizing' useSizing t =
  case removeChecks <$> findChurchSizeD useSizing t of
    Right i -> pure i
    Left e  -> Left e

-- | Converts between easily understood Haskell types and untyped IExprs around an iteration of a Telomare expression
-- | Renamed to avoid conflict with Telomare.Eval.funWrap'
sizingFunWrap :: (StuckExpr -> StuckExpr) -> StuckExpr -> Maybe (String, StuckExpr) -> (String, Maybe StuckExpr)
sizingFunWrap evalFn fun inp =
  let iexpInp = case inp of
        Nothing                  -> zeroB
        Just (userInp, oldState) -> pairB (s2b userInp) oldState
  in case evalFn (appB fun iexpInp) of
    ZeroB               -> ("aborted", Nothing)
    PairB disp newState -> (case b2s disp of { Just s -> s; Nothing -> show disp }, Just newState)
    z                   -> ("runtime error, dumped:\n" <> show z, Nothing)
