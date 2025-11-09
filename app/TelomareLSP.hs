{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.Concurrent.STM
import Control.Monad (void)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Data.List (sortOn)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T

import Language.LSP.Server
import qualified Language.LSP.Protocol.Types as LSPTypes
import Language.LSP.Protocol.Types
  ( Position(..), Range(..), UInt, NormalizedUri, toNormalizedUri )
import Language.LSP.Protocol.Message (SMethod(..))
import Control.Lens ((^.))
import qualified Language.LSP.Protocol.Lens as LSP

-- Document state tracking
data DocState = DocState
  { docText    :: T.Text
  , docVersion :: Int
  } deriving (Show)

type DocStore = TVar (Map.Map NormalizedUri DocState)

main :: IO ()
main = do
  docStore <- newTVarIO Map.empty
  void $ runServer $ ServerDefinition
    { parseConfig      = const $ const $ Right ()
    , onConfigChange   = const $ pure ()
    , defaultConfig    = ()
    , configSection    = "telomare"
    , doInitialize     = \env _req -> pure $ Right env
    , staticHandlers   = \_caps -> handlers docStore
    , interpretHandler = \env -> Iso (runLspT env) liftIO
    , options          = serverOptions
    }

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

-- Token legend (not actively used by serverOptions here)
tokenLegend :: LSPTypes.SemanticTokensLegend
tokenLegend = LSPTypes.SemanticTokensLegend
  [ "keyword", "string", "number", "operator", "variable", "comment", "function", "type" ]
  []

-- Token type indices
tokKeyword, tokString, tokNumber, tokOperator, tokVariable, tokComment, tokFunction, tokType :: UInt
tokKeyword  = 0
tokString   = 1
tokNumber   = 2
tokOperator = 3
tokVariable = 4
tokComment  = 5
tokFunction = 6
tokType     = 7

-- LSP Handlers
handlers :: DocStore -> Handlers (LspM ())
handlers docStore = mconcat
  [ notificationHandler SMethod_Initialized                   $ \_ -> pure ()
  , notificationHandler SMethod_TextDocumentDidOpen           $ didOpenHandler docStore
  , notificationHandler SMethod_TextDocumentDidChange         $ didChangeHandler docStore
  , notificationHandler SMethod_TextDocumentDidClose          $ didCloseHandler docStore
  , requestHandler     SMethod_TextDocumentSemanticTokensFull  $ semanticTokensFullHandler docStore
  , requestHandler     SMethod_TextDocumentSemanticTokensRange $ semanticTokensRangeHandler docStore
  , requestHandler     SMethod_TextDocumentHover               $ hoverHandler docStore
  ]

-- Document lifecycle handlers (leave types inferred)
didOpenHandler docStore notification = do
  let doc     = notification ^. LSP.params . LSP.textDocument
      uri     = doc ^. LSP.uri
      version = doc ^. LSP.version
      text    = doc ^. LSP.text
  liftIO $ atomically $ modifyTVar' docStore $
    Map.insert (toNormalizedUri uri) (DocState text (fromIntegral version))

didChangeHandler docStore notification = do
  let doc     = notification ^. LSP.params . LSP.textDocument
      uri     = doc ^. LSP.uri
      version = doc ^. LSP.version
      changes = notification ^. LSP.params . LSP.contentChanges
  case changes of
    [] -> pure ()
    (LSPTypes.TextDocumentContentChangeEvent changeData : _) -> do
      -- Extract text from the union type using record pattern matching
      let newText = case changeData of
                      LSPTypes.InL partial -> partial ^. LSP.text
                      LSPTypes.InR whole -> whole ^. LSP.text
      liftIO $ atomically $ modifyTVar' docStore $
        Map.insert (toNormalizedUri uri) (DocState newText (fromIntegral version))

didCloseHandler docStore notification = do
  let uri = notification ^. LSP.params . LSP.textDocument . LSP.uri
  liftIO $ atomically $ modifyTVar' docStore $ Map.delete (toNormalizedUri uri)

-- Semantic tokens (full): result is (SemanticTokens |? SemanticTokensDelta)
semanticTokensFullHandler docStore req respond = do
  let uri = req ^. LSP.params . LSP.textDocument . LSP.uri
  mDoc <- liftIO $ atomically $ Map.lookup (toNormalizedUri uri) <$> readTVar docStore
  case mDoc of
    Nothing -> respond $ Right $ LSPTypes.InL $ LSPTypes.SemanticTokens Nothing []
    Just docState -> do
      let tokens  = lexTelomare (docText docState)
          encoded = tokensToLSP tokens
      respond $ Right $ LSPTypes.InL $ LSPTypes.SemanticTokens Nothing encoded
  -- For deltas, reply InR (SemanticTokensDelta ...).

-- Semantic tokens (range): order -> (SemanticTokens |? Null)
semanticTokensRangeHandler docStore req respond = do
  let uri   = req ^. LSP.params . LSP.textDocument . LSP.uri
      range = req ^. LSP.params . LSP.range
  mDoc <- liftIO $ atomically $ Map.lookup (toNormalizedUri uri) <$> readTVar docStore
  case mDoc of
    Nothing -> respond $ Right $ LSPTypes.InL $ LSPTypes.SemanticTokens Nothing []
    Just docState -> do
      let tokens  = filter (withinRange range) (lexTelomare (docText docState))
          encoded = tokensToLSP tokens
      respond $ Right $ LSPTypes.InL $ LSPTypes.SemanticTokens Nothing encoded

-- Hover: order -> (Hover |? Null)
hoverHandler docStore req respond = do
  let uri = req ^. LSP.params . LSP.textDocument . LSP.uri
      pos = req ^. LSP.params . LSP.position
  mDoc <- liftIO $ atomically $ Map.lookup (toNormalizedUri uri) <$> readTVar docStore
  case mDoc of
    Nothing -> respond $ Right $ LSPTypes.InR LSPTypes.Null
    Just docState -> do
      let text = docText docState
      case getExpressionAtPosition text pos of
        Nothing -> respond $ Right $ LSPTypes.InR LSPTypes.Null
        Just (exprText, exprRange) -> do
          let evaluationResult = evaluateExpression exprText
              markdown = case evaluationResult of
                Left err    -> T.pack $ "**Parse Error:**\n```\n" ++ err ++ "\n```"
                Right result ->
                  T.pack $ "**Expression:**\n```telomare\n" ++ T.unpack exprText
                        ++ "\n```\n\n**Partial Evaluation:**\n```\n" ++ result ++ "\n```"
              hoverContent = LSPTypes.MarkupContent LSPTypes.MarkupKind_Markdown markdown
              hover = LSPTypes.Hover (LSPTypes.InL hoverContent) (Just exprRange)
          respond $ Right $ LSPTypes.InL hover

-- Placeholder evaluation function - replace with actual eval integration later
evaluateExpression :: T.Text -> Either String String
evaluateExpression expr =
  Right $ "TODO: Integrate eval2IExpr\nExpression: " ++ T.unpack expr

-- Extract expression at cursor position
getExpressionAtPosition :: T.Text -> Position -> Maybe (T.Text, Range)
getExpressionAtPosition text (Position line char) = do
  let textLines = T.lines text
  guard $ line < fromIntegral (length textLines)
  let targetLine = textLines !! fromIntegral line
      (before, after) = T.splitAt (fromIntegral char) targetLine
      beforeRev  = T.reverse before
      identStart = T.dropWhile isIdentChar beforeRev
      wordBefore = T.reverse $ T.take (T.length beforeRev - T.length identStart) beforeRev
      wordAfter  = T.takeWhile isIdentChar after
      word       = wordBefore <> wordAfter
  if T.null word
    then Nothing
    else Just
      ( word
      , Range
          (Position line (char - fromIntegral (T.length wordBefore)))
          (Position line (char + fromIntegral (T.length wordAfter)))
      )
  where
    isIdentChar c = c `elem` ("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'" :: String)

-- Lexer for syntax highlighting
data Token = Token
  { tLine   :: UInt
  , tStart  :: UInt
  , tLength :: UInt
  , tType   :: UInt
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
              [Token lineNum col (fromIntegral $ length (c:cs)) tokComment]
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
              in Token lineNum col (fromIntegral $ length ident) ttype
                   : go (col + fromIntegral (length ident)) rest
          | isOperatorChar c =
              let (len, rest) = spanOperator (c:cs) 0
              in Token lineNum col len tokOperator : go (col + len) rest
          | otherwise = go (col + 1) cs

        spanString :: String -> UInt -> (UInt, String)
        spanString [] n          = (n, [])
        spanString ('\\':_:xs) n = spanString xs (n + 2)
        spanString ('"':xs) n    = (n + 1, xs)
        spanString (_:xs) n      = spanString xs (n + 1)

        spanDigits :: String -> UInt -> (UInt, String)
        spanDigits [] n       = (n, [])
        spanDigits s@(d:ds) n
          | d >= '0' && d <= '9' = spanDigits ds (n + 1)
          | otherwise            = (n, s)

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
          in  deltaStart : tLength t : tType t : 0 : 0 : go prevLine (tStart t) ts
      | otherwise =
          let deltaLine = tLine t - prevLine
          in  deltaLine : tStart t : tLength t : tType t : 0 : go (tLine t) (tStart t) ts

-- Range filter for tokens
withinRange :: Range -> Token -> Bool
withinRange (Range (Position sl sc) (Position el ec)) tok =
  let line  = tLine tok
      start = tStart tok
      end   = start + tLength tok
      startOk = (line > fromIntegral sl) || (line == fromIntegral sl && start >= fromIntegral sc)
      endOk   = (line < fromIntegral el) || (line == fromIntegral el && end <= fromIntegral ec)
  in startOk && endOk

-- tiny Maybe guard (avoid Control.Monad.guard)
guard :: Bool -> Maybe ()
guard True  = Just ()
guard False = Nothing
