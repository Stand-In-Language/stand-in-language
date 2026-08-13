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
import Control.Monad.Identity (runIdentity)
import Control.Monad.IO.Class
import Data.Bifunctor (first)
import Data.Functor ((<&>))
import Data.Functor.Foldable (Corecursive (embed), cata)
import Data.List (intercalate, isPrefixOf, stripPrefix)
import Data.Set (Set)
import qualified Data.Set as Set
import Options.Applicative hiding ((<|>))
import System.Console.Haskeline
import System.Exit (exitSuccess)
import qualified System.IO.Strict as Strict
import Telomare.Desugar (desugarTerm)
import Telomare.Driver (compileUnitTestNoAbort)
import Telomare.Error
import Telomare.Eval.Reference (evalPartial)
import Telomare.Expand (ExpansionError, expandDefs, expandTerm,
                        renderExpansionError)
import Telomare.IR.Base
import Telomare.IR.Core
import Telomare.IR.Loc
import Telomare.IR.Surface
import Telomare.Parse (TelomareParser, parseLongExpr, parseSingleDefinition,
                       runParseDefinitions)
import Telomare.PrettyPrint
import Telomare.Resolve (process)
import Telomare.Size.IR (PartialExpr)
import Telomare.TypeCheck (inferType)
import Text.Megaparsec

-- Parsers for assignments/expressions within REPL
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
--   Things in the REPL behave slightly different
-- than in the compiler. For example it is possible.
-- to overwrite top-level bindings.

-- |Lift an expansion result into the REPL's parsers, rendering errors the
-- same way parse errors are shown.
expandedRepl :: Either ExpansionError a -> TelomareParser a
expandedRepl = either (fail . renderExpansionError) pure

-- | Assignment parsing from the repl.
parseReplAssignment :: TelomareParser [(String, ExpandedSurfaceTerm)]
parseReplAssignment = do
  def <- parseSingleDefinition <* eof
  fmap (first locatedNameText) <$> expandedRepl (expandDefs [def])

-- | Parse only an expression
parseReplExpr :: TelomareParser [(String, ExpandedSurfaceTerm)]
parseReplExpr = do
  expr <- parseLongExpr <* eof
  expandedExpr <- expandedRepl (expandTerm expr)
  pure [("_tmp_", expandedExpr)]

-- | Information about what has the REPL parsed.
data ReplStep a = ReplAssignment a
                | ReplExpr a
                deriving (Eq, Ord, Show, Functor)

-- | Combination of `parseReplExpr` and `parseReplAssignment`
parseReplStep :: TelomareParser (ReplStep [(String, ExpandedSurfaceTerm)])
parseReplStep = try (parseReplAssignment <&> ReplAssignment)
                <|> (parseReplExpr <&> ReplExpr)

-- | Try to parse the given string and update the bindings.
runReplParser :: [(String, ExpandedSurfaceTerm)]
              -> String
              -> Either String (ReplStep [(String, ExpandedSurfaceTerm)])
runReplParser prelude input = fmap (prelude <>) <$> first errorBundlePretty (runParser parseReplStep "" input)

-- |Parse and expand a file of definitions (a prelude or a @:l@-loaded
-- file) into REPL bindings.
parseDefinitionsFile :: String -> Either String [(String, ExpandedSurfaceTerm)]
parseDefinitionsFile input = do
  defs <- runParseDefinitions "" input
  bindings <- first renderExpansionError $ expandDefs defs
  pure $ first locatedNameText <$> bindings

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
                -> [(String, ExpandedSurfaceTerm)]
                -> Maybe Term3
resolveBinding' name bindings =
  lookup name bindings >>= (rightToMaybe . process . desugarTerm)

-- |Obtain expression from the bindings and transform them maybe into a IExpr.
resolveBinding :: String -> [(String, ExpandedSurfaceTerm)] -> Maybe CompiledExpr
resolveBinding name bindings = rightToMaybe $ compileUnitTestNoAbort =<< maybeToRight (resolveBinding' name bindings)

-- |Print last expression bound to
-- the _tmp_ variable in the bindings
printLastExpr :: (StuckExpr -> Either RunTimeError StuckExpr) -- ^Telomare backend
              -> [(String, ExpandedSurfaceTerm)]
              -> IO ()
printLastExpr evalFn bindings = do
  res :: Either Exception.SomeException () <- Exception.try $
    case lookup "_tmp_" bindings of
      Nothing -> putStrLn "Could not find _tmp_ in bindings"
      Just upt -> do
        let compile' :: Term3 -> Either EvalError StuckExpr
            compile' x = case compileUnitTestNoAbort x of
                           Left err -> Left  err
                           Right r  -> case toTelomare r of
                             Just te -> pure te
                             _ -> Left . RTE . ResultConversionError $ "conversion error from compiled expr:\n" <> prettyPrint r
        case compile' =<< first RE (process . desugarTerm $ UnknownLoc :< LetUPF (first (locatedName UnknownLoc) <$> bindings) upt) of
          Left err -> print err
          Right iexpr' -> case evalFn iexpr' of
              Left e      -> putStrLn $ "error: " <> show e
              Right expr' -> print . PrettyStuckExpr $ expr'
  case res of
    Left err -> print err
    Right _  -> pure ()

-- REPL related logic
-- ~~~~~~~~~~~~~~~~~~

data ReplState = ReplState
  { replBindings :: [(String, ExpandedSurfaceTerm)]
  , replEval     :: StuckExpr -> Either RunTimeError StuckExpr
  , loadedFiles  :: Set FilePath
  -- ^ Backend function used to compile IExprs.
  }

-- | Enter a single line assignment or expression.
replStep :: (StuckExpr -> Either RunTimeError StuckExpr)
         -> [(String, ExpandedSurfaceTerm)]
         -> String
         -> InputT IO [(String, ExpandedSurfaceTerm)]
replStep evalFn bindings s = do
  let e_new_bindings = runReplParser bindings s
  case e_new_bindings of
    Left err -> do
      outputStrLn ("Parse error: " <> err)
      pure bindings
    Right (ReplExpr new_bindings) -> do
      liftIO $ printLastExpr evalFn new_bindings
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

evalPartial' :: CompiledExpr -> CompiledExpr
evalPartial' = convertF . evalPartial . convertT where
  convertT :: CompiledExpr -> PartialExpr
  convertT = runIdentity . cata (convertBasic (convertStuck (convertAbort convertUnknown)))
  convertUnknown = error "could not convert for evalPartial'"
  convertF :: PartialExpr -> CompiledExpr
  convertF = runIdentity . cata (convertBasic (convertStuck convertOther))
  convertOther = error "could not convert back from evalPartial'"

-- | Main loop for the REPL.
replLoop :: ReplState -> InputT IO ()
replLoop (ReplState bs evalFn sf) = do
  minput <- getInputLine "telomare> "
  case minput of
    Nothing   -> pure ()
    Just ":q" -> liftIO exitSuccess
    Just ":{" -> do
      new_bs <- replStep evalFn bs =<< replMultiline []
      replLoop $ ReplState new_bs evalFn sf
    Just s | ":d" `isPrefixOf` s -> do
      liftIO $ case runReplParser bs . dropWhile (== ' ') <$> stripPrefix ":d" s of
        Just (Right (ReplExpr new_bindings)) -> case resolveBinding "_tmp_" new_bindings of
          Just iexpr -> putStrLn $ prettyPrint iexpr
          _          -> putStrLn "some sort of error?"
        _ -> putStrLn "parse error"
      replLoop $ ReplState bs evalFn sf
    Just s | ":p" `isPrefixOf` s -> do
      liftIO $ case runReplParser bs . dropWhile (== ' ') <$> stripPrefix ":p" s of
        Just (Right (ReplExpr new_bindings)) -> case resolveBinding "_tmp_" new_bindings of
          -- Just iexpr -> putStrLn . showPIE $ evalPartial' iexpr
          Just iexpr -> print . PrettyCompiledExpr $ evalPartial' iexpr
          _          -> putStrLn "some sort of error?"
        _ -> putStrLn "parse error"
      replLoop $ ReplState bs evalFn sf
    Just s | ":t" `isPrefixOf` s -> do
      liftIO $ case runReplParser bs . dropWhile (== ' ') <$> stripPrefix ":t" s of
        Just (Right (ReplExpr new_bindings)) -> case resolveBinding' "_tmp_" new_bindings of
          Just iexpr -> print $ PrettyPartialType <$> inferType iexpr
          _          -> putStrLn "some sort of error?"
        _ -> putStrLn "parse error"
      replLoop $ ReplState bs evalFn sf
    Just ":r" -> do
      let loadFile :: FilePath -> InputT IO [(String, ExpandedSurfaceTerm)]
          loadFile fileName = do
            fileString <- liftIO $ Strict.readFile fileName
            case parseDefinitionsFile fileString of
              Left errStr -> do
                liftIO . putStrLn $ "Error from loaded file: " <> errStr
                pure []
              Right fileBindings -> do
                liftIO . putStrLn $ "File " <> fileName <> " successfully loaded."
                pure fileBindings
      bs' <- concat <$> mapM loadFile (Set.toList sf)
      replLoop $ ReplState bs' evalFn sf
    Just fileName | ":l " `isPrefixOf` fileName -> do
      let fileName' = drop 3 fileName
      fileString <- liftIO $ Strict.readFile fileName'
      case parseDefinitionsFile fileString of
        Left errStr -> do
          liftIO . putStrLn $ "Error from loaded file: " <> errStr
          replLoop $ ReplState bs evalFn sf
        Right fileBindings -> do
                liftIO . putStrLn $ "File " <> fileName' <> " successfully loaded."
                replLoop $ ReplState (bs <> fileBindings) evalFn (Set.insert fileName' sf)
    Just s -> do
      new_bs <- replStep evalFn bs s
      replLoop $ ReplState new_bs evalFn sf

-- Command line settings
-- ~~~~~~~~~~~~~~~~~~~~~

data ReplBackend = SimpleBackend
                 deriving (Show, Eq, Ord)

data ReplSettings = ReplSettings
  { _backend :: ReplBackend
  , _expr    :: Maybe String
  } deriving (Show, Eq)

-- | Choose a backend option between Haskell, Naturals.
-- Haskell is default.
backendOpts :: Parser ReplBackend
backendOpts = flag' SimpleBackend   (long "haskell"  <> help "Haskell Backend (default)")
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
startExpr :: (StuckExpr -> Either RunTimeError StuckExpr)
          -> [(String, ExpandedSurfaceTerm)]
          -> String
          -> IO ()
startExpr evalFn bindings s_expr = case runReplParser bindings s_expr of
  Left err                 -> error $ ("Parse error: " <> err)
  Right (ReplAssignment _) -> error "Expression is an assignment"
  Right (ReplExpr binds)   -> printLastExpr evalFn binds

main :: IO ()
main = do
  e_prelude <- parseDefinitionsFile <$> Strict.readFile "Prelude.tel"
  settings  <- execParser opts
  let eval' = case _backend settings of
               SimpleBackend   -> wrapEval simpleEval'
      simpleEval' :: StuckExpr -> Either RunTimeError StuckExpr
      simpleEval' = eval
      wrapEval f = conv . fmap toTelomare . f . fromTelomare . (\x -> SetEnvB (PairB (embed . embedS $ DeferSF (toEnum (-1)) x) ZeroB))
      conv = \case
        Right (Just x) -> Right x
        Left e -> Left e
        _ -> Left $ ResultConversionError "failed converting back to iexpr after eval"
      bindings = case e_prelude of
          Left  _   ->  []
          Right bds -> bds
  case _expr settings of
    Just  s -> startExpr eval' bindings s
    Nothing -> startLoop (ReplState bindings eval Set.empty)
