{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}

module Main where

import Control.Concurrent.STM
import Control.Monad (void)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Data.List (sortOn)
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)
import qualified Data.Text as T
import Language.LSP.Server
import Language.LSP.Protocol.Types
import Language.LSP.Protocol.Message
import Control.Lens ((^.))
import qualified Language.LSP.Protocol.Lens as LSP

-- Import from telomare library - adjust these imports based on actual module structure
-- import Telomare.Parser (parseOneExprOrTopLevelDefs, runParser)
-- import Telomare.Eval (eval2IExpr, process, compileUnitTest)
-- import Telomare.Types (UnprocessedParsedTerm, AnnotatedUPT, IExpr)

-- Document state tracking
data DocState = DocState
  { docText :: T.Text
  , docVersion :: Int
  } deriving (Show)

type DocStore = TVar (Map.Map NormalizedUri DocState)

main :: IO ()
main = do
  docStore <- newTVarIO Map.empty

  void $ runServer $ ServerDefinition
    { parseConfig = const $ const $ Right ()
    , onConfigChange = const $ pure ()
    , defaultConfig = ()
    , configSection = "telomare"
    , doInitialize = \env _req -> pure $ Right env
    , staticHandlers = \_caps -> handlers docStore
    , interpretHandler = \env -> Iso (runLspT env) liftIO
    , options = serverOptions
    }

-- Server capabilities
serverOptions :: Options
serverOptions = defaultOptions
  { optTextDocumentSync = Just $ InL $ TextDocumentSyncOptions
      { _openClose = Just True
      , _change = Just TextDocumentSyncKind_Full
      , _willSave = Just False
      , _willSaveWaitUntil = Just False
      , _save = Just $ InR $ SaveOptions { _includeText = Just False }
      }
  , optSemanticTokensProvider = Just $ InL $ SemanticTokensRegistrationOptions
      { _documentSelector = Nothing
      , _workDoneProgress = Nothing
      , _legend = tokenLegend
      , _range = Just $ InL True
      , _full = Just $ InL True
      , _id = Nothing
      }
  , optHoverProvider = Just $ InL True
  }

-- Token types legend - note: needs SemanticTokensLegend with Text not enum
tokenLegend :: SemanticTokensLegend
tokenLegend = SemanticTokensLegend
  { _tokenTypes =
      [ "keyword"      -- 0: let, in, if, case, etc
      , "string"       -- 1: string literals
      , "number"       -- 2: integers
      , "operator"     -- 3: ->, \, #, etc
      , "variable"     -- 4: identifiers
      , "comment"      -- 5: comments
      , "function"     -- 6: function names
      , "type"         -- 7: type constructors
      ]
  , _tokenModifiers = []
  }

-- Token type indices
tokKeyword, tokString, tokNumber, tokOperator, tokVariable, tokComment, tokFunction, tokType :: UInt
tokKeyword = 0
tokString = 1
tokNumber = 2
tokOperator = 3
tokVariable = 4
tokComment = 5
tokFunction = 6
tokType = 7

-- LSP Handlers
handlers :: DocStore -> Handlers (LspM ())
handlers docStore = mconcat
  [ notificationHandler SMethod_Initialized $ \_notification -> pure ()
  , notificationHandler SMethod_TextDocumentDidOpen $ didOpenHandler docStore
  , notificationHandler SMethod_TextDocumentDidChange $ didChangeHandler docStore
  , notificationHandler SMethod_TextDocumentDidClose $ didCloseHandler docStore
  , requestHandler SMethod_TextDocumentSemanticTokensFull $ semanticTokensFullHandler docStore
  , requestHandler SMethod_TextDocumentSemanticTokensRange $ semanticTokensRangeHandler docStore
  , requestHandler SMethod_TextDocumentHover $ hoverHandler docStore
  ]

-- Document lifecycle handlers
didOpenHandler :: DocStore -> NotificationMessage Method_TextDocumentDidOpen -> LspM () ()
didOpenHandler docStore notification = do
  let doc = notification ^. LSP.params . LSP.textDocument
      uri = doc ^. LSP.uri
      version = doc ^. LSP.version
      text = doc ^. LSP.text
  liftIO $ atomically $ modifyTVar' docStore $
    Map.insert (toNormalizedUri uri) (DocState text (fromIntegral version))

didChangeHandler :: DocStore -> NotificationMessage Method_TextDocumentDidChange -> LspM () ()
didChangeHandler docStore notification = do
  let doc = notification ^. LSP.params . LSP.textDocument
      uri = doc ^. LSP.uri
      version = doc ^. LSP.version
      changes = notification ^. LSP.params . LSP.contentChanges
  -- Take the last change (full sync mode sends complete text)
  case changes of
    (change:_) -> do
      let newText = change ^. LSP.text
      liftIO $ atomically $ modifyTVar' docStore $
        Map.insert (toNormalizedUri uri) (DocState newText (fromIntegral version))
    _ -> pure ()

didCloseHandler :: DocStore -> NotificationMessage Method_TextDocumentDidClose -> LspM () ()
didCloseHandler docStore notification = do
  let uri = notification ^. LSP.params . LSP.textDocument . LSP.uri
  liftIO $ atomically $ modifyTVar' docStore $ Map.delete (toNormalizedUri uri)

-- Semantic tokens handler
semanticTokensFullHandler :: DocStore -> RequestMessage Method_TextDocumentSemanticTokensFull -> (Either ResponseError (InL SemanticTokens |? InR SemanticTokensDelta) -> LspM () ()) -> LspM () ()
semanticTokensFullHandler docStore req respond = do
  let uri = req ^. LSP.params . LSP.textDocument . LSP.uri
  mDoc <- liftIO $ atomically $ Map.lookup (toNormalizedUri uri) <$> readTVar docStore
  case mDoc of
    Nothing -> respond $ Right $ InL $ SemanticTokens Nothing []
    Just docState -> do
      let tokens = lexTelomare (docText docState)
          encoded = tokensToLSP tokens
      respond $ Right $ InL $ SemanticTokens Nothing encoded

semanticTokensRangeHandler :: DocStore -> RequestMessage Method_TextDocumentSemanticTokensRange -> (Either ResponseError SemanticTokens -> LspM () ()) -> LspM () ()
semanticTokensRangeHandler docStore req respond = do
  let uri = req ^. LSP.params . LSP.textDocument . LSP.uri
      range = req ^. LSP.params . LSP.range
  mDoc <- liftIO $ atomically $ Map.lookup (toNormalizedUri uri) <$> readTVar docStore
  case mDoc of
    Nothing -> respond $ Right $ SemanticTokens Nothing []
    Just docState -> do
      let tokens = filter (withinRange range) (lexTelomare (docText docState))
          encoded = tokensToLSP tokens
      respond $ Right $ SemanticTokens Nothing encoded

-- Hover handler with partial evaluation
hoverHandler :: DocStore -> RequestMessage Method_TextDocumentHover -> (Either ResponseError (InL Null |? InR Hover) -> LspM () ()) -> LspM () ()
hoverHandler docStore req respond = do
  let uri = req ^. LSP.params . LSP.textDocument . LSP.uri
      pos = req ^. LSP.params . LSP.position
  mDoc <- liftIO $ atomically $ Map.lookup (toNormalizedUri uri) <$> readTVar docStore
  case mDoc of
    Nothing -> respond $ Right $ InL Null
    Just docState -> do
      -- Get the word/expression at cursor position
      let text = docText docState
          expr = getExpressionAtPosition text pos
      case expr of
        Nothing -> respond $ Right $ InL Null
        Just (exprText, exprRange) -> do
          -- Try to evaluate the expression
          -- For now, just show the expression itself
          -- TODO: Integrate with eval2IExpr once we have proper imports
          let evaluationResult = evaluateExpression exprText
              markdown = case evaluationResult of
                Left err -> T.pack $ "**Parse Error:**\n```\n" ++ err ++ "\n```"
                Right result -> T.pack $ "**Expression:**\n```telomare\n" ++ T.unpack exprText ++ "\n```\n\n**Partial Evaluation:**\n```\n" ++ result ++ "\n```"
              hoverContent = MarkupContent MarkupKind_Markdown markdown
          respond $ Right $ InR $ Hover (InL hoverContent) (Just exprRange)

-- Placeholder evaluation function - replace with actual eval2IExpr integration
evaluateExpression :: T.Text -> Either String String
evaluateExpression expr =
  Right $ "TODO: Integrate eval2IExpr\nExpression: " ++ T.unpack expr

-- Extract expression at cursor position
getExpressionAtPosition :: T.Text -> Position -> Maybe (T.Text, Range)
getExpressionAtPosition text (Position line char) = do
  let textLines = T.lines text
  guard $ line < fromIntegral (Prelude.length textLines)
  let targetLine = textLines !! fromIntegral line
      (before, after) = T.splitAt (fromIntegral char) targetLine
      -- Extend backwards to start of word/expression
      beforeRev = T.reverse before
      identStart = T.dropWhile isIdentChar beforeRev
      wordBefore = T.reverse $ T.take (T.length beforeRev - T.length identStart) beforeRev
      -- Extend forwards to end of word/expression
      wordAfter = T.takeWhile isIdentChar after
      word = wordBefore <> wordAfter
  if T.null word
    then Nothing
    else Just (word, Range
                (Position line (char - fromIntegral (T.length wordBefore)))
                (Position line (char + fromIntegral (T.length wordAfter))))
  where
    isIdentChar c = c `elem` ("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'" :: String)

-- Lexer for syntax highlighting
data Token = Token
  { tLine :: UInt
  , tStart :: UInt
  , tLength :: UInt
  , tType :: UInt
  } deriving (Eq, Show)

keywords :: [T.Text]
keywords =
  [ "let", "in", "if", "then", "else", "case", "of"
  , "left", "right", "not", "trace", "check"
  ]

lexTelomare :: T.Text -> [Token]
lexTelomare text = concat $ zipWith lexLine [0..] (T.lines text)
  where
    lexLine :: UInt -> T.Text -> [Token]
    lexLine lineNum lineText = go 0 (T.unpack lineText)
      where
        go _ [] = []
        go col (c:cs)
          | c `elem` (" \t" :: String) = go (col + 1) cs
          | c == '-' && not (null cs) && head cs == '-' =
              [Token lineNum col (fromIntegral $ Prelude.length (c:cs)) tokComment]
          | c == '"' =
              let (len, rest) = spanString cs 1
              in Token lineNum col len tokString : go (col + len) rest
          | c >= '0' && c <= '9' =
              let (len, rest) = spanDigits (c:cs) 0
              in Token lineNum col len tokNumber : go (col + len) rest
          | isIdentStart c =
              let (ident, rest) = spanIdent (c:cs)
                  identText = T.pack ident
                  ttype = if identText `elem` keywords then tokKeyword else tokVariable
              in Token lineNum col (fromIntegral $ Prelude.length ident) ttype : go (col + fromIntegral (Prelude.length ident)) rest
          | isOperatorChar c =
              let (len, rest) = spanOperator (c:cs) 0
              in Token lineNum col len tokOperator : go (col + len) rest
          | otherwise = go (col + 1) cs

        spanString :: String -> UInt -> (UInt, String)
        spanString [] n = (n, [])
        spanString ('\\':x:xs) n = spanString xs (n + 2)
        spanString ('"':xs) n = (n + 1, xs)
        spanString (_:xs) n = spanString xs (n + 1)

        spanDigits :: String -> UInt -> (UInt, String)
        spanDigits [] n = (n, [])
        spanDigits s@(d:ds) n
          | d >= '0' && d <= '9' = spanDigits ds (n + 1)
          | otherwise = (n, s)

        spanIdent :: String -> (String, String)
        spanIdent s = span (\c -> isIdentChar c) s

        spanOperator :: String -> UInt -> (UInt, String)
        spanOperator [] n = (n, [])
        spanOperator s@(c:cs) n
          | isOperatorChar c = spanOperator cs (n + 1)
          | otherwise = (n, s)

        isIdentStart c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_'
        isIdentChar c = isIdentStart c || (c >= '0' && c <= '9') || c == '\''
        isOperatorChar c = c `elem` ("!@$%^&*-=+:/\\|<>?#." :: String)

-- Encode tokens to LSP format (delta encoding)
tokensToLSP :: [Token] -> [UInt]
tokensToLSP tokens = go 0 0 (sortOn (\t -> (tLine t, tStart t)) tokens)
  where
    go _ _ [] = []
    go prevLine prevStart (t:ts)
      | tLine t == prevLine =
          let deltaStart = tStart t - prevStart
          in deltaStart : tLength t : tType t : 0 : 0 : go prevLine (tStart t) ts
      | otherwise =
          let deltaLine = tLine t - prevLine
          in deltaLine : tStart t : tLength t : tType t : 0 : go (tLine t) (tStart t) ts

-- Check if token is within range
withinRange :: Range -> Token -> Bool
withinRange (Range (Position sl sc) (Position el ec)) tok =
  let line = tLine tok
      start = tStart tok
      end = start + tLength tok
      startOk = (line > fromIntegral sl) || (line == fromIntegral sl && start >= fromIntegral sc)
      endOk = (line < fromIntegral el) || (line == fromIntegral el && end <= fromIntegral ec)
  in startOk && endOk

guard :: Bool -> Maybe ()
guard True = Just ()
guard False = Nothing
