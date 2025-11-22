{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}

module Main where

import Control.Concurrent.STM
import Control.Exception (try, IOException)
import Control.Monad (void, forM)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Data.List (sortOn)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import Data.Either (isRight)
import System.FilePath ((</>))

import Language.LSP.Server
import qualified Language.LSP.Protocol.Types as LSPTypes
import Language.LSP.Protocol.Types
  ( Position(..), Range(..), UInt, NormalizedUri, toNormalizedUri )
import Language.LSP.Protocol.Message (SMethod(..))
import Control.Lens ((^.))
import qualified Language.LSP.Protocol.Lens as LSP
import qualified Language.LSP.Protocol.Message as LSPMsg

import Telomare.Parser (parseModule, AnnotatedUPT)
import Telomare.Eval (eval2IExpr)
import Telomare (IExpr)

--------------------------------------------------------------------------------
-- Document state tracking

-- Results of parseModule:
--   Either errorString or a list of either imports or (name, binding) pairs.
type ParseResult = [Either AnnotatedUPT (String, AnnotatedUPT)]

-- Store module bindings for evaluation context
type ModuleBindings = [(String, ParseResult)]

data DocState = DocState
  { docText   :: T.Text
  , docVersion :: Int
  , docParse  :: Either String ParseResult
  } deriving (Show)

type DocStore = TVar (Map.Map NormalizedUri DocState)

-- Global state for prelude and other module bindings
data GlobalState = GlobalState
  { docStore :: DocStore
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
  
  void $ runServer $ ServerDefinition
    { parseConfig      = const $ const $ Right ()
    , onConfigChange   = const $ pure ()
    , defaultConfig    = ()
    , configSection    = "telomare"
    , doInitialize     = \env _req -> pure $ Right env
    , staticHandlers   = \_caps -> handlers globalState
    , interpretHandler = \env -> Iso (runLspT env) liftIO
    , options          = serverOptions
    }

-- Load Prelude.tel and parse it
loadPrelude :: IO ModuleBindings
loadPrelude = do
  -- Try to load Prelude.tel from common locations
  let preludePaths = ["~/src/telomare/Prelude.tel", "Prelude.tel", "lib/Prelude.tel", "../lib/Prelude.tel"]
  preludeContents <- tryLoadFiles preludePaths
  case preludeContents of
    Nothing -> return []
    Just content -> 
      case parseModule content of
        Left err -> do
          putStrLn $ "Warning: Failed to parse Prelude.tel: " ++ err
          return []
        Right parsed -> return [("Prelude", parsed)]
  where
    tryLoadFiles :: [FilePath] -> IO (Maybe String)
    tryLoadFiles [] = return Nothing
    tryLoadFiles (path:paths) = do
      result <- try (readFile path) :: IO (Either IOException String)
      case result of
        Right content -> return (Just content)
        Left _ -> tryLoadFiles paths

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
  in defaultOptions { optTextDocumentSync = Just syncOpts }

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
  , requestHandler     SMethod_TextDocumentHover               $ hoverHandler gState
  ]

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
  liftIO . atomically $
    modifyTVar' docStore' $
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
  liftIO $ atomically $ modifyTVar' docStore' $ Map.delete (toNormalizedUri uri)

--------------------------------------------------------------------------------
-- Semantic tokens (kept using the simple lexer for now)

semanticTokensFullHandler docStore' req respond = do
  let uri = req ^. LSP.params . LSP.textDocument . LSP.uri
  mDoc <- liftIO $ atomically $ Map.lookup (toNormalizedUri uri) <$> readTVar docStore'
  case mDoc of
    Nothing -> respond $ Right $ LSPTypes.InL $ LSPTypes.SemanticTokens Nothing []
    Just docState -> do
      let tokens  = lexTelomare (docText docState)
          encoded = tokensToLSP tokens
      respond $ Right $ LSPTypes.InL $ LSPTypes.SemanticTokens Nothing encoded

semanticTokensRangeHandler docStore' req respond = do
  let uri   = req ^. LSP.params . LSP.textDocument . LSP.uri
      range = req ^. LSP.params . LSP.range
  mDoc <- liftIO $ atomically $ Map.lookup (toNormalizedUri uri) <$> readTVar docStore'
  case mDoc of
    Nothing -> respond $ Right $ LSPTypes.InL $ LSPTypes.SemanticTokens Nothing []
    Just docState -> do
      let tokens  = filter (withinRange range) (lexTelomare (docText docState))
          encoded = tokensToLSP tokens
      respond $ Right $ LSPTypes.InL $ LSPTypes.SemanticTokens Nothing encoded

--------------------------------------------------------------------------------
-- Hover with Partial Evaluation

hoverHandler gState req respond = do
  let uri = req ^. LSP.params . LSP.textDocument . LSP.uri
      pos = req ^. LSP.params . LSP.position
  mDoc <- liftIO $ atomically $ Map.lookup (toNormalizedUri uri) <$> readTVar (docStore gState)
  case mDoc of
    Nothing -> respond $ Right $ LSPTypes.InR LSPTypes.Null
    Just docState -> do
      -- If parse failed, surface error immediately (using current cursor as range anchor)
      case docParse docState of
        Left err -> do
          let md  = LSPTypes.MarkupContent LSPTypes.MarkupKind_Markdown
                    (T.pack $ "**Parse Error**\n\n```\n" <> err <> "\n```")
              rng = Range pos pos
              hov = LSPTypes.Hover (LSPTypes.InL md) (Just rng)
          respond $ Right $ LSPTypes.InL hov
        Right parsedDoc -> do
          -- Get expression at cursor position
          let text = docText docState
          case getExpressionAtPosition text pos of
            Nothing -> respond $ Right $ LSPTypes.InR LSPTypes.Null
            Just (exprText, exprRange) -> do
              -- Get module bindings for evaluation context
              bindings <- liftIO $ readTVarIO (moduleBindings gState)
              
              -- Attempt partial evaluation using eval2IExpr
              let evaluationResult = evaluateExpression bindings exprText
                  markdown = case evaluationResult of
                    Left e -> 
                      T.pack $ "**Expression:**\n```telomare\n" ++ T.unpack exprText
                            ++ "\n```\n\n**Error:**\n```\n" ++ e ++ "\n```"
                    Right res ->
                      T.pack $ "**Expression:**\n```telomare\n" ++ T.unpack exprText
                            ++ "\n```\n\n**Partial Evaluation:**\n```\n" ++ res ++ "\n```"
                  hoverContent = LSPTypes.MarkupContent LSPTypes.MarkupKind_Markdown markdown
                  hover = LSPTypes.Hover (LSPTypes.InL hoverContent) (Just exprRange)
              respond $ Right $ LSPTypes.InL hover

--------------------------------------------------------------------------------
-- Partial evaluation using eval2IExpr

evaluateExpression :: ModuleBindings -> T.Text -> Either String String
evaluateExpression bindings expr = 
  case eval2IExpr bindings (T.unpack expr) of
    Left err -> Left err
    Right iexpr -> Right (show iexpr)

--------------------------------------------------------------------------------
-- Extract expression at cursor position
-- Enhanced to handle more complex expressions

getExpressionAtPosition :: T.Text -> Position -> Maybe (T.Text, Range)
getExpressionAtPosition text (Position line char) = do
  let textLines = T.lines text
  guard $ line < fromIntegral (length textLines)
  let targetLine = textLines !! fromIntegral line
      lineOffset = fromIntegral line
      charOffset = fromIntegral char
  
  -- Try multiple strategies to find the expression
  findExpression targetLine charOffset lineOffset
    <|> findSimpleIdentifier targetLine charOffset lineOffset
  where
    -- Try to find a complete expression (handles parentheses, lambdas, etc.)
    findExpression :: T.Text -> UInt -> UInt -> Maybe (T.Text, Range)
    findExpression lineText col lineNum = do
      -- Look for balanced expressions around cursor
      let beforeCursor = T.take (fromIntegral col) lineText
          afterCursor = T.drop (fromIntegral col) lineText
      
      -- Check if we're inside parentheses or at a lambda
      case findBalancedExpr lineText col of
        Just (startCol, endCol) -> 
          let expr = T.take (fromIntegral $ endCol - startCol) $ 
                     T.drop (fromIntegral startCol) lineText
          in Just (expr, Range 
                    (Position lineNum startCol)
                    (Position lineNum endCol))
        Nothing -> Nothing
    
    -- Fallback: find simple identifier or operator
    findSimpleIdentifier :: T.Text -> UInt -> UInt -> Maybe (T.Text, Range)
    findSimpleIdentifier lineText col lineNum = do
      let (before, after) = T.splitAt (fromIntegral col) lineText
          beforeRev = T.reverse before
          identStart = T.dropWhile isIdentChar beforeRev
          wordBefore = T.reverse $ T.take (T.length beforeRev - T.length identStart) beforeRev
          wordAfter = T.takeWhile isIdentChar after
          word = wordBefore <> wordAfter
      if T.null word
        then Nothing
        else Just
          ( word
          , Range
              (Position lineNum (col - fromIntegral (T.length wordBefore)))
              (Position lineNum (col + fromIntegral (T.length wordAfter)))
          )
    
    -- Find balanced expression (parentheses, lambdas, etc.)
    findBalancedExpr :: T.Text -> UInt -> Maybe (UInt, UInt)
    findBalancedExpr lineText col = 
      -- Simple heuristic: find the innermost balanced parentheses containing the cursor
      findParens 0 0 0 (T.unpack lineText)
      where
        findParens :: Int -> UInt -> UInt -> String -> Maybe (UInt, UInt)
        findParens _ _ _ [] = Nothing
        findParens depth start pos ('(':rest)
          | pos <= col = findParens (depth + 1) (if depth == 0 then pos else start) (pos + 1) rest
          | otherwise = if depth > 0 && start < col then Just (start, pos) else Nothing
        findParens depth start pos (')':rest)
          | pos > col && depth == 1 = Just (start, pos + 1)
          | otherwise = findParens (depth - 1) start (pos + 1) rest
        findParens depth start pos (_:rest) = findParens depth start (pos + 1) rest
    
    isIdentChar c = c `elem` ("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'." :: String)

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
          | c >= '0' && c <= '9' =
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

        -- Helper to check if character is a digit
        isDigit c = c >= '0' && c <= '9'

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
        spanIdent s = span isIdentChar s

        spanOperator :: String -> UInt -> (UInt, String)
        spanOperator [] n     = (n, [])
        spanOperator s@(c:cs) n
          | isOperatorChar c  = spanOperator cs (n + 1)
          | otherwise         = (n, s)

        isIdentStart c = (c >= 'a' && c <= 'z')
                      || (c >= 'A' && c <= 'Z')
                      || c == '_'

        isIdentChar c = isIdentStart c
                      || (c >= '0' && c <= '9')
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

-- Alternative operator for Maybe
(<|>) :: Maybe a -> Maybe a -> Maybe a
Nothing <|> b = b
a <|> _ = a
