{-# LANGUAGE CApiFFI               #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant $" #-}

module Main where

import Control.Comonad.Cofree (Cofree (..))
import qualified Control.Exception as Exception
import Control.Monad.IO.Class
import qualified Control.Monad.State as State
import Data.Bifunctor (first)
import Data.Functor ((<&>))
import Data.List (intercalate, isPrefixOf, singleton, stripPrefix)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace (trace)
import Naturals
import Options.Applicative hiding ((<|>))
import qualified Options.Applicative as O
import PrettyPrint
import System.Console.Haskeline
import System.Exit (exitSuccess)
import qualified System.IO.Strict as Strict
import Telomare
import Telomare.Eval (EvalError (..), compileUnitTestNoAbort)
import Telomare.Parser (TelomareParser,
                        parseAssignment,
                        parseLongExpr, parsePrelude)
import Telomare.Possible (evalPartial', deferB)
import Telomare.PossibleData (CompiledExpr, setEnvB, pairB, zeroB)
import Telomare.Resolver (process)
import Telomare.RunTime (fastInterpretEval, simpleEval)
import Telomare.TypeChecker (inferType)
import Text.Megaparsec
import Text.Megaparsec.Char

-- Parsers for assignments/expressions within REPL
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
--   Things in the REPL behave slightly different
-- than in the compiler. For example it is possible.
-- to overwrite top-level bindings.

-- | Assignment parsing from the repl.
parseReplAssignment :: TelomareParser [(String, UnprocessedParsedTerm)]
parseReplAssignment = singleton . fmap forget <$> (parseAssignment <* eof)

-- | Parse only an expression
parseReplExpr :: TelomareParser [(String, UnprocessedParsedTerm)]
parseReplExpr = do
  expr <- parseLongExpr <* eof
  pure [("_tmp_", forget expr)]

-- | Information about what has the REPL parsed.
data ReplStep a = ReplAssignment a
                | ReplExpr a
                deriving (Eq, Ord, Show, Functor)

-- | Combination of `parseReplExpr` and `parseReplAssignment`
parseReplStep :: TelomareParser (ReplStep [(String, UnprocessedParsedTerm )])
parseReplStep = try (parseReplAssignment <&> ReplAssignment)
                <|> (parseReplExpr <&> ReplExpr)

-- | Try to parse the given string and update the bindings.
runReplParser :: [(String, UnprocessedParsedTerm)]
              -> String
              -> Either String (ReplStep [(String, UnprocessedParsedTerm)])
runReplParser prelude str = fmap (prelude <>) <$> first errorBundlePretty (runParser parseReplStep "" str)

-- Common functions
-- ~~~~~~~~~~~~~~~~

-- |Forget Left helper function.
rightToMaybe :: Either a b -> Maybe b
rightToMaybe (Right b) = Just b
rightToMaybe _         = Nothing

maybeToRight :: Maybe a -> Either EvalError a
maybeToRight (Just x) = Right x
-- This will become a Maybe right after being used, so it doesn't matter what error is present
maybeToRight Nothing  = Left CompileConversionError

-- |Obtain expression from the bindings and transform them into maybe a Term3.
resolveBinding' :: String
                -> [(String, UnprocessedParsedTerm)]
                -> Maybe Term3
resolveBinding' name bindings = lookup name taggedBindings >>= (rightToMaybe . process)
  where
    taggedBindings = (fmap . fmap) (tag DummyLoc) bindings

-- |Obtain expression from the bindings and transform them maybe into a IExpr.
resolveBinding :: String -> [(String, UnprocessedParsedTerm)] -> Maybe CompiledExpr
resolveBinding name bindings = rightToMaybe $ compileUnitTestNoAbort =<< maybeToRight (resolveBinding' name bindings)

resolveBindingI :: String -> [(String, UnprocessedParsedTerm)] -> Maybe IExpr
resolveBindingI name bindings = resolveBinding name bindings >>= toTelomare

-- |Print last expression bound to
-- the _tmp_ variable in the bindings
printLastExpr :: (IExpr -> Either RunTimeError IExpr) -- ^Telomare backend
              -> [(String, UnprocessedParsedTerm)]
              -> IO ()
printLastExpr eval bindings = do
  let bindings' = (fmap . fmap) (tag DummyLoc) bindings
  res :: Either Exception.SomeException () <- Exception.try $
    case lookup "_tmp_" bindings' of
      Nothing -> putStrLn "Could not find _tmp_ in bindings"
      Just upt -> do
        let compile' x = case compileUnitTestNoAbort x of
                           Left err -> Left . show $ err
                           Right r  -> case toTelomare r of
                             Just te -> pure $ fromTelomare te
                             _ -> Left $ "conversion error from compiled expr:\n" <> prettyPrint r
        case compile' =<< process (DummyLoc :< LetUPF bindings' upt) of
          Left err -> putStrLn err
          Right iexpr' -> case eval iexpr' of
              Left e -> putStrLn $ "error: " <> show e
              Right expr' -> print . PrettyIExpr $ expr'
  case res of
    Left err -> print err
    Right _  -> pure ()

-- REPL related logic
-- ~~~~~~~~~~~~~~~~~~

data ReplState = ReplState
  { replBindings :: [(String, UnprocessedParsedTerm)]
  , replEval     :: IExpr -> Either RunTimeError IExpr
  , loadedFiles  :: Set FilePath
  -- ^ Backend function used to compile IExprs.
  }

-- | Enter a single line assignment or expression.
replStep :: (IExpr -> Either RunTimeError IExpr)
         -> [(String, UnprocessedParsedTerm)]
         -> String
         -> InputT IO [(String, UnprocessedParsedTerm)]
replStep eval bindings s = do
  let e_new_bindings = runReplParser bindings s
  case e_new_bindings of
    Left err -> do
      outputStrLn ("Parse error: " <> err)
      pure bindings
    Right (ReplExpr new_bindings) -> do
      liftIO $ printLastExpr eval new_bindings
      pure bindings
    Right (ReplAssignment new_bindings) -> pure new_bindings

-- | Obtain a multiline string.
replMultiline :: [String] -> InputT IO String
replMultiline buffer = do
  minput <- getInputLine ""
  case minput of
    Nothing   -> pure ""
    Just ":}" -> pure $ intercalate "\n" (reverse buffer)
    Just s    -> replMultiline (s : buffer)

-- | Main loop for the REPL.
replLoop :: ReplState -> InputT IO ()
replLoop (ReplState bs eval sf) = do
  minput <- getInputLine "telomare> "
  case minput of
    Nothing   -> pure ()
    Just ":q" -> liftIO exitSuccess
    Just ":{" -> do
      new_bs <- replStep eval bs =<< replMultiline []
      replLoop $ ReplState new_bs eval sf
    Just s | ":dn" `isPrefixOf` s -> do
      liftIO $ case runReplParser bs . dropWhile (== ' ') <$> stripPrefix ":dn" s of
        Just (Right (ReplExpr new_bindings)) -> case resolveBindingI "_tmp_" new_bindings of
          Just expr -> case toTelomare expr of
            Just iexpr -> do
              putStrLn . showNExprs $ fromTelomare iexpr
              putStrLn . showNIE $ fromTelomare iexpr
            _ -> putStrLn "conversion error from CompiledExpr"
          _ -> putStrLn "some sort of error?"
        _ -> putStrLn "parse error"
      replLoop $ ReplState bs eval sf
    Just s | ":d" `isPrefixOf` s -> do
      liftIO $ case runReplParser bs . dropWhile (== ' ') <$> stripPrefix ":d" s of
        Just (Right (ReplExpr new_bindings)) -> case resolveBindingI "_tmp_" new_bindings of
          Just iexpr -> putStrLn $ showPIE iexpr
          _          -> putStrLn "some sort of error?"
        _ -> putStrLn "parse error"
      replLoop $ ReplState bs eval sf
    Just s | ":p" `isPrefixOf` s -> do
      liftIO $ case runReplParser bs . dropWhile (== ' ') <$> stripPrefix ":p" s of
        Just (Right (ReplExpr new_bindings)) -> case resolveBindingI "_tmp_" new_bindings of
          Just iexpr -> putStrLn . showPIE $ evalPartial' iexpr
          _          -> putStrLn "some sort of error?"
        _ -> putStrLn "parse error"
      replLoop $ ReplState bs eval sf
{-
    Just s | ":tt" `isPrefixOf` s -> do
      liftIO $ case (runReplParser bs . dropWhile (== ' ')) <$> stripPrefix ":tt" s of
        Just (Right (ReplExpr, new_bindings)) -> case resolveBinding "_tmp_" new_bindings of
          Just iexpr -> print . showTraceTypes $ iexpr
          _ -> putStrLn "some sort of error?"
        _ -> putStrLn "parse error"
      replLoop $ ReplState bs eval
-}
    Just s | ":t" `isPrefixOf` s -> do
      liftIO $ case runReplParser bs . dropWhile (== ' ') <$> stripPrefix ":t" s of
        Just (Right (ReplExpr new_bindings)) -> case resolveBinding' "_tmp_" new_bindings of
          Just iexpr -> print $ PrettyPartialType <$> inferType iexpr
          _          -> putStrLn "some sort of error?"
        _ -> putStrLn "parse error"
      replLoop $ ReplState bs eval sf
    Just ":r" -> do
      let loadFile :: FilePath -> InputT IO [(String, UnprocessedParsedTerm)]
          loadFile fileName = do
            fileString <- liftIO $ Strict.readFile fileName
            case parsePrelude fileString of
              Left errStr -> do
                liftIO . putStrLn $ "Error from loaded file: " <> errStr
                pure []
              Right fileBindings -> do
                liftIO . putStrLn $ "File " <> fileName <> " successfully loaded."
                pure . (fmap . fmap) forget $ fileBindings
      bs' <- concat <$> mapM loadFile (Set.toList sf)
      replLoop $ ReplState bs' eval sf
    Just fileName | ":l " `isPrefixOf` fileName -> do
      let fileName' = drop 3 fileName
      fileString <- liftIO $ Strict.readFile fileName'
      case parsePrelude fileString of
        Left errStr -> do
          liftIO . putStrLn $ "Error from loaded file: " <> errStr
          replLoop $ ReplState bs eval sf
        Right fileBindings -> do
                liftIO . putStrLn $ "File " <> fileName' <> " successfully loaded."
                replLoop $ ReplState (bs <> (fmap . fmap) forget fileBindings) eval (Set.insert fileName' sf)
    Just s -> do
      new_bs <- replStep eval bs s
      replLoop $ ReplState new_bs eval sf

-- Command line settings
-- ~~~~~~~~~~~~~~~~~~~~~

data ReplBackend = SimpleBackend
                 | NaturalsBackend
                 deriving (Show, Eq, Ord)

data ReplSettings = ReplSettings
  { _backend :: ReplBackend
  , _expr    :: Maybe String
  } deriving (Show, Eq)

-- | Choose a backend option between Haskell, Naturals.
-- Haskell is default.
backendOpts :: Parser ReplBackend
backendOpts = flag' SimpleBackend   (long "haskell"  <> help "Haskell Backend (default)")
          <|> flag' NaturalsBackend (long "naturals" <> help "Naturals Interpretation Backend")
          <|> pure SimpleBackend

-- | Process a given expression instead of entering the repl.
exprOpts :: Parser (Maybe String)
exprOpts = optional $ strOption ( long "expr" <> short 'e' <> help "Expression to be computed")

-- | Combined options
opts :: ParserInfo ReplSettings
opts = info (settings <**> helper)
  ( fullDesc
  <> progDesc "Stand-in-language simple read-eval-print-loop")
    where settings = ReplSettings <$> backendOpts <*> exprOpts

-- Program
-- ~~~~~~~

-- | Start REPL loop.
startLoop :: ReplState -> IO ()
startLoop state = runInputT defaultSettings $ replLoop state

-- | Compile and output a Telomare expression.
startExpr :: (IExpr -> Either RunTimeError IExpr)
          -> [(String, UnprocessedParsedTerm)]
          -> String
          -> IO ()
startExpr eval bindings s_expr = case runReplParser bindings s_expr of
  Left err                 -> error $ ("Parse error: " <> err)
  Right (ReplAssignment _) -> error "Expression is an assignment"
  Right (ReplExpr binds)   -> printLastExpr eval binds

main = do
  e_prelude <- parsePrelude <$> Strict.readFile "Prelude.tel"
  settings  <- execParser opts
  let eval' = case _backend settings of
               SimpleBackend   -> wrapEval simpleEval'
               NaturalsBackend -> wrapEval natEval
      simpleEval' :: IExpr -> Either RunTimeError IExpr
      simpleEval' = eval
      natEval :: NExprs -> Either RunTimeError NExprs
      natEval = eval
      wrapEval f = conv . fmap toTelomare . f . fromTelomare . (\x -> SetEnv (Pair (Defer x) Zero))
      conv = \case
        Right (Just x) -> Right x
        Left e -> Left e
        _ -> Left $ ResultConversionError "failed converting back to iexpr after eval"
      bindings = (fmap . fmap) forget $
        case e_prelude of
          Left  _   ->  []
          Right bds -> bds
  case _expr settings of
    Just  s -> startExpr eval' bindings s
    Nothing -> startLoop (ReplState bindings eval Set.empty)
