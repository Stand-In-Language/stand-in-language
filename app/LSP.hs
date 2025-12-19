{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module Main where

import Control.Concurrent.STM
import Control.Exception (IOException, try)
import Control.Monad (forM, void)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.Either (isRight)
import Data.List (sortOn)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import System.FilePath ((</>))

import Control.Lens ((^.))
import qualified Data.Aeson as JSON
import qualified Language.LSP.Protocol.Lens as LSP
import Language.LSP.Protocol.Message (SMethod (..))
import qualified Language.LSP.Protocol.Message as LSPMsg
import Language.LSP.Protocol.Types (NormalizedUri, Position (..), Range (..),
                                    UInt, toNormalizedUri, type (|?))
import qualified Language.LSP.Protocol.Types as LSPTypes
import Language.LSP.Server

import Telomare (IExpr)
import Telomare.Eval (eval2IExpr)
import Telomare.Parser (AnnotatedUPT, parseModule)

--------------------------------------------------------------------------------
-- Document state tracking

-- Results of parseModule:
--   Either errorString or a list of either imports or (name, binding) pairs.
type ParseResult = [Either AnnotatedUPT (String, AnnotatedUPT)]

-- Store module bindings for evaluation context
type ModuleBindings = [(String, ParseResult)]

data DocState = DocState
  { docText    :: T.Text
  , docVersion :: Int
  , docParse   :: Either String ParseResult
  } deriving (Show)

type DocStore = TVar (Map.Map NormalizedUri DocState)

-- Global state for prelude and other module bindings
data GlobalState = GlobalState
  { docStore       :: DocStore
  , moduleBindings :: TVar ModuleBindings
  }

--------------------------------------------------------------------------------
-- Lexer for syntax highlighting (kept as-is for now)

data Token = Token
  { tLine   :: UInt
  , tStart  :: UInt
  , tLength :: UInt
  , tType   :: UInt
  } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- LSP Server

main :: IO ()
main = do
  docStore' <- newTVarIO Map.empty

  -- Load Prelude.tel if available
  preludeBindings <- loadPrelude
  moduleBindings' <- newTVarIO preludeBindings

  let globalState = GlobalState docStore' moduleBindings'

  void . runServer $ ServerDefinition
    { parseConfig      = const . const $ Right ()
    , onConfigChange   = const $ pure ()
    , defaultConfig    = ()
    , configSection    = "telomare"
    , doInitialize     = \env _req -> pure $ Right env
    , staticHandlers   = \_caps -> mconcat [handlers globalState, commandHandlers globalState]
    , interpretHandler = \env -> Iso (runLspT env) liftIO
    , options          = serverOptions
    }

-- Load Prelude.tel and parse it
loadPrelude :: IO ModuleBindings
loadPrelude = do
  -- Try to load Prelude.tel from common locations
  let preludePaths = ["Prelude.tel", "lib/Prelude.tel", "../lib/Prelude.tel"]
  preludeContents <- tryLoadFiles preludePaths
  case preludeContents of
    Nothing -> return []
    Just content ->
      case parseModule content of
        Left err -> do
          putStrLn $ "Warning: Failed to parse Prelude.tel: " <> err
          return []
        Right parsed -> return [("Prelude", parsed)]
  where
    tryLoadFiles :: [FilePath] -> IO (Maybe String)
    tryLoadFiles [] = return Nothing
    tryLoadFiles (path:paths) = do
      result <- try (readFile path) :: IO (Either IOException String)
      case result of
        Right content -> return (Just content)
        Left _        -> tryLoadFiles paths

-- Server options (plain TextDocumentSyncOptions for lsp-types-2.3.x)
serverOptions :: Options
serverOptions =
  let syncOpts =
        LSPTypes.TextDocumentSyncOptions
          (Just True)                               -- openClose
          (Just LSPTypes.TextDocumentSyncKind_Full) -- change
          (Just False)                              -- willSave
          (Just False)                              -- willSaveWaitUntil
          Nothing                                   -- save
  in defaultOptions { optTextDocumentSync = Just syncOpts
                    , optExecuteCommandCommands = Just ["telomare.partialEval"]
                    }

-- Token type indices (matching the server's reported legend)
tokComment, tokKeyword, tokString, tokNumber, tokOperator, tokVariable, tokFunction, tokType :: UInt
tokKeyword  = 1   -- "keyword"
tokComment  = 0   -- "comment"
tokString   = 2   -- "string"
tokNumber   = 3   -- "number"
tokOperator = 5   -- "operator"
tokVariable = 19  -- "variable"
tokFunction = 13  -- "function"
tokType     = 7    -- "type"

--------------------------------------------------------------------------------
-- Handlers

handlers :: GlobalState -> Handlers (LspM ())
handlers gState = mconcat
  [ notificationHandler SMethod_Initialized                   $ \_ -> pure ()
  , notificationHandler SMethod_TextDocumentDidOpen           $ didOpenHandler (docStore gState)
  , notificationHandler SMethod_TextDocumentDidChange         $ didChangeHandler (docStore gState)
  , notificationHandler SMethod_TextDocumentDidClose          $ didCloseHandler (docStore gState)
  , requestHandler     SMethod_TextDocumentSemanticTokensFull  $ semanticTokensFullHandler (docStore gState)
  , requestHandler     SMethod_TextDocumentSemanticTokensRange $ semanticTokensRangeHandler (docStore gState)
  , requestHandler     SMethod_TextDocumentCodeAction          $ codeActionHandler gState
  , requestHandler     SMethod_CodeActionResolve               $ codeActionResolveHandler gState
  ]

-- Command handlers
commandHandlers :: GlobalState -> Handlers (LspM ())
commandHandlers gState = mconcat
  [ requestHandler SMethod_WorkspaceExecuteCommand $ executeCommandHandler gState
  ]

-- Execute command handler
executeCommandHandler :: GlobalState
                      -> LSPMsg.TRequestMessage LSPMsg.Method_WorkspaceExecuteCommand
                      -> (Either (LSPMsg.TResponseError LSPMsg.Method_WorkspaceExecuteCommand)
                               (JSON.Value LSPTypes.|? LSPTypes.Null)
                         -> LspM () ())
                      -> LspM () ()
executeCommandHandler gState req respond = do
  let command = req ^. LSP.params . LSP.command
      mArgs = req ^. LSP.params . LSP.arguments

  case command of
    "telomare.partialEval" -> do
      case mArgs of
        Just args | length args >= 3 -> do
          -- Parse the JSON values
          let uriResult = JSON.fromJSON (head args) :: JSON.Result LSPTypes.Uri
              rangeResult = JSON.fromJSON (args !! 1) :: JSON.Result Range
              exprResult = JSON.fromJSON (args !! 2) :: JSON.Result T.Text

          case (uriResult, rangeResult, exprResult) of
            (JSON.Success uri, JSON.Success range, JSON.Success exprText) -> do
              executePartialEvaluation gState uri range exprText
              respond . Right $ LSPTypes.InL JSON.Null
            _ -> respond . Right $ LSPTypes.InL JSON.Null
        _ -> respond . Right $ LSPTypes.InL JSON.Null
    _ -> respond . Right $ LSPTypes.InL JSON.Null

--------------------------------------------------------------------------------
-- Helpers: centralize parsing through parseModule

parseTelomareModule :: T.Text -> Either String ParseResult
parseTelomareModule = parseModule . T.unpack

storeParsedDoc
  :: DocStore
  -> LSPTypes.Uri
  -> Int
  -> T.Text
  -> LspM () ()
storeParsedDoc docStore' uri version text = do
  let parseRes = parseTelomareModule text
  liftIO . atomically . modifyTVar' docStore' $
    Map.insert (toNormalizedUri uri) (DocState text version parseRes)

--------------------------------------------------------------------------------
-- Document lifecycle handlers

didOpenHandler :: DocStore
               -> LSPMsg.TNotificationMessage 'LSPMsg.Method_TextDocumentDidOpen
               -> LspM () ()
didOpenHandler docStore' notification = do
  let doc     = notification ^. LSP.params . LSP.textDocument
      uri     = doc ^. LSP.uri
      version = fromIntegral (doc ^. LSP.version)
      text    = doc ^. LSP.text
  storeParsedDoc docStore' uri version text

didChangeHandler :: DocStore
                 -> LSPMsg.TNotificationMessage 'LSPMsg.Method_TextDocumentDidChange
                 -> LspM () ()
didChangeHandler docStore' notification = do
  let doc     = notification ^. LSP.params . LSP.textDocument
      uri     = doc ^. LSP.uri
      version = fromIntegral (doc ^. LSP.version)
      changes = notification ^. LSP.params . LSP.contentChanges
  case changes of
    [] -> pure ()
    (LSPTypes.TextDocumentContentChangeEvent changeData : _) -> do
      -- Extract text from union (partial vs whole)
      let newText = case changeData of
                      LSPTypes.InL partial -> partial ^. LSP.text
                      LSPTypes.InR whole   -> whole   ^. LSP.text
      storeParsedDoc docStore' uri version newText

didCloseHandler :: DocStore
                -> LSPMsg.TNotificationMessage 'LSPMsg.Method_TextDocumentDidClose
                -> LspM () ()
didCloseHandler docStore' notification = do
  let uri = notification ^. LSP.params . LSP.textDocument . LSP.uri
  liftIO . atomically . modifyTVar' docStore' $ Map.delete (toNormalizedUri uri)

--------------------------------------------------------------------------------
-- Semantic tokens (kept using the simple lexer for now)

semanticTokensFullHandler docStore' req respond = do
  let uri = req ^. LSP.params . LSP.textDocument . LSP.uri
  mDoc <- liftIO . atomically $ Map.lookup (toNormalizedUri uri) <$> readTVar docStore'
  case mDoc of
    Nothing -> respond . Right . LSPTypes.InL $ LSPTypes.SemanticTokens Nothing []
    Just docState -> do
      let tokens  = lexTelomare (docText docState)
          encoded = tokensToLSP tokens
      respond . Right . LSPTypes.InL $ LSPTypes.SemanticTokens Nothing encoded

semanticTokensRangeHandler docStore' req respond = do
  let uri   = req ^. LSP.params . LSP.textDocument . LSP.uri
      range = req ^. LSP.params . LSP.range
  mDoc <- liftIO . atomically $ Map.lookup (toNormalizedUri uri) <$> readTVar docStore'
  case mDoc of
    Nothing -> respond . Right . LSPTypes.InL $ LSPTypes.SemanticTokens Nothing []
    Just docState -> do
      let tokens  = filter (withinRange range) (lexTelomare (docText docState))
          encoded = tokensToLSP tokens
      respond . Right . LSPTypes.InL $ LSPTypes.SemanticTokens Nothing encoded

--------------------------------------------------------------------------------
-- Code Actions for Partial Evaluation

codeActionHandler :: GlobalState
                  -> LSPMsg.TRequestMessage LSPMsg.Method_TextDocumentCodeAction
                  -> (Either (LSPMsg.TResponseError LSPMsg.Method_TextDocumentCodeAction)
                           ([LSPTypes.Command LSPTypes.|? LSPTypes.CodeAction] LSPTypes.|? LSPTypes.Null)
                     -> LspM () ())
                  -> LspM () ()
codeActionHandler gState req respond = do
  let uri = req ^. LSP.params . LSP.textDocument . LSP.uri
      range = req ^. LSP.params . LSP.range
      context = req ^. LSP.params . LSP.context

  mDoc <- liftIO . atomically $ Map.lookup (toNormalizedUri uri) <$> readTVar (docStore gState)
  case mDoc of
    Nothing -> respond . Right . LSPTypes.InL $ []
    Just docState -> do
      case docParse docState of
        Left err -> respond . Right . LSPTypes.InL $ []
        Right parsedDoc -> do
          -- Get the selected text
          let text = docText docState
              selectedText = getTextInRange text range

          case selectedText of
            Nothing -> respond . Right . LSPTypes.InL $ []
            Just exprText -> do
              -- Create a code action for partial evaluation
              let title = T.pack $ "Partially evaluate: " <>
                            take 20 (T.unpack exprText) <>
                            if T.length exprText > 20 then "..." else ""
                  codeAction =
                    LSPTypes.CodeAction
                      title
                      (Just LSPTypes.CodeActionKind_RefactorExtract)
                      Nothing
                      (Just False)
                      Nothing
                      Nothing
                      (Just (LSPTypes.Command
                              "Partial Evaluation"
                              "telomare.partialEval"
                              (Just [ JSON.toJSON uri
                                   , JSON.toJSON range
                                   , JSON.toJSON exprText
                                   ])))
                      Nothing

              respond . Right $ LSPTypes.InL [LSPTypes.InR codeAction]

codeActionResolveHandler :: GlobalState
                         -> LSPMsg.TRequestMessage LSPMsg.Method_CodeActionResolve
                         -> (Either (LSPMsg.TResponseError LSPMsg.Method_CodeActionResolve)
                                  LSPTypes.CodeAction
                            -> LspM () ())
                         -> LspM () ()
codeActionResolveHandler gState req respond = do
  -- For now, just return the action as-is since we're using commands
  -- The request body should contain a CodeAction
  let codeAction = req ^. LSP.params
  respond $ Right codeAction

-- Execute partial evaluation and show result
executePartialEvaluation :: GlobalState -> LSPTypes.Uri -> Range -> T.Text -> LspM () ()
executePartialEvaluation gState uri range exprText = do
  bindings <- liftIO $ readTVarIO (moduleBindings gState)
  let evaluationResult = evaluateExpression bindings exprText
      message = case evaluationResult of
        Left e    -> T.pack $ "Evaluation Error: " <> e
        Right res -> T.pack $ "Result: " <> res

  -- Show result as a window message
  sendNotification SMethod_WindowShowMessage $
    LSPTypes.ShowMessageParams
      LSPTypes.MessageType_Info
      message

-- Get text within a range
getTextInRange :: T.Text -> Range -> Maybe T.Text
getTextInRange text (Range (Position startLine startChar) (Position endLine endChar)) = do
  let textLines = T.lines text
  guard $ startLine < fromIntegral (length textLines) && endLine < fromIntegral (length textLines)

  if startLine == endLine
    then do
      let line = textLines !! fromIntegral startLine
      Just . T.take (fromIntegral $ endChar - startChar) $ T.drop (fromIntegral startChar) line
    else do
      let firstLine = T.drop (fromIntegral startChar) $ textLines !! fromIntegral startLine
          middleLines = take (fromIntegral $ endLine - startLine - 1) $ drop (fromIntegral startLine + 1) textLines
          lastLine = T.take (fromIntegral endChar) $ textLines !! fromIntegral endLine
      Just . T.intercalate "\n" $ [firstLine] <> middleLines <> [lastLine]

--------------------------------------------------------------------------------
-- Partial evaluation using eval2IExpr

evaluateExpression :: ModuleBindings -> T.Text -> Either String String
evaluateExpression bindings expr =
  case eval2IExpr bindings (T.unpack expr) of
    Left err    -> Left err
    Right iexpr -> Right (show iexpr)

--------------------------------------------------------------------------------
-- Simple lexer (still useful for semantic tokens)

keywords :: [T.Text]
keywords =
  [ "let", "in", "if", "then", "else", "case", "of"
  , "import", "qualified", "as", "where"
  ]

lexTelomare :: T.Text -> [Token]
lexTelomare text = concat $ zipWith lexLine [0..] (T.lines text)
  where
    lexLine :: UInt -> T.Text -> [Token]
    lexLine lineNum lineText = go 0 (T.unpack lineText)
      where
        go _ [] = []
        go col str@(c:cs)
          | c `elem` (" \t" :: String) = go (col + 1) cs

          -- Comments (but not inside strings)
          | c == '-' && not (null cs) && head cs == '-' =
              [Token lineNum col (fromIntegral $ length str) tokComment]

          -- String literals (must come before comment check)
          | c == '"' =
              let (len, rest) = spanString cs 1
              in Token lineNum col len tokString : go (col + len) rest

          -- Church numerals ($123)
          | c == '$' && not (null cs) && isDigit (head cs) =
              let (len, rest) = spanChurch cs 1
              in Token lineNum col len tokNumber : go (col + len) rest

          -- Regular numbers
          | isDigit c =
              let (len, rest) = spanDigits (c:cs) 0
              in Token lineNum col len tokNumber : go (col + len) rest

          -- Lambda syntax (\x -> ...)
          | c == '\\' && (null cs || not (isOperatorChar (head cs))) =
              Token lineNum col 1 tokKeyword : go (col + 1) cs

          -- Pattern arrow (->) and operators
          | c == '-' && not (null cs) && head cs == '>' =
              Token lineNum col 2 tokKeyword : go (col + 2) (tail cs)

          -- Hash syntax for HashUP
          | c == '#' =
              Token lineNum col 1 tokOperator : go (col + 1) cs

          -- Identifiers and keywords
          | isIdentStart c =
              let (ident, rest) = spanIdent (c:cs)
                  identText = T.pack ident
                  ttype = if identText `elem` keywords then tokKeyword else tokVariable
              in Token lineNum col (fromIntegral $ length ident) ttype
                   : go (col + fromIntegral (length ident)) rest

          -- Other operators
          | isOperatorChar c =
              let (len, rest) = spanOperator (c:cs) 0
              in Token lineNum col len tokOperator : go (col + len) rest

          -- Parentheses, brackets, braces (structure tokens)
          | c `elem` ("()[]{}" :: String) =
              Token lineNum col 1 tokOperator : go (col + 1) cs

          -- Comma (special separator)
          | c == ',' =
              Token lineNum col 1 tokOperator : go (col + 1) cs

          | otherwise = go (col + 1) cs

        -- Span church numeral (after $)
        spanChurch :: String -> UInt -> (UInt, String)
        spanChurch [] n = (n, [])
        spanChurch s@(d:ds) n
          | isDigit d = spanChurch ds (n + 1)
          | otherwise = (n, s)

        spanString :: String -> UInt -> (UInt, String)
        spanString [] n          = (n, [])
        spanString ('\\':_:xs) n = spanString xs (n + 2)
        spanString ('"':xs) n    = (n + 1, xs)
        spanString (_:xs) n      = spanString xs (n + 1)

        spanDigits :: String -> UInt -> (UInt, String)
        spanDigits [] n       = (n, [])
        spanDigits s@(d:ds) n
          | isDigit d = spanDigits ds (n + 1)
          | otherwise = (n, s)

        spanIdent :: String -> (String, String)
        spanIdent = span isIdentChar

        spanOperator :: String -> UInt -> (UInt, String)
        spanOperator [] n     = (n, [])
        spanOperator s@(c:cs) n
          | isOperatorChar c  = spanOperator cs (n + 1)
          | otherwise         = (n, s)

        isIdentStart c = isAsciiLower c
                      || isAsciiUpper c
                      || c == '_'

        isIdentChar c = isIdentStart c
                      || isDigit c
                      || c == '\''
                      || c == '.'  -- Added dot for qualified names

        -- Adjusted operator chars (removed some that have special meaning)
        isOperatorChar c = c `elem` ("!@%^&*+=:/|<>?-" :: String)

-- Encode tokens to LSP format (delta encoding, relative positions)
tokensToLSP :: [Token] -> [UInt]
tokensToLSP tokens = go 0 0 (sortOn (\t -> (tLine t, tStart t)) tokens)
  where
    go _ _ [] = []
    go prevLine prevStart (t:ts)
      | tLine t == prevLine =
          -- SAME LINE: deltaLine must be 0
          0 : (tStart t - prevStart) : tLength t : tType t : 0
          : go prevLine (tStart t) ts
      | otherwise =
          -- NEW LINE: delta from previous line, start is absolute column
          (tLine t - prevLine) : tStart t : tLength t : tType t : 0
          : go (tLine t) (tStart t) ts

-- Range filter for tokens
withinRange :: Range -> Token -> Bool
withinRange (Range (Position sl sc) (Position el ec)) tok =
  let line  = tLine tok
      start = tStart tok
      end   = start + tLength tok
      startOk = (line > fromIntegral sl) || (line == fromIntegral sl && start >= fromIntegral sc)
      endOk   = (line < fromIntegral el) || (line == fromIntegral el && end <= fromIntegral ec)
  in startOk && endOk

--------------------------------------------------------------------------------
-- tiny Maybe guard (avoid Control.Monad.guard)

guard :: Bool -> Maybe ()
guard True  = Just ()
guard False = Nothing
