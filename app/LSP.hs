{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module Main where

import Control.Applicative ((<|>))
import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Concurrent.STM
import Control.Exception (IOException, try)
import Control.Monad (void)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Bifunctor (first)
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.List (find, sortOn)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe, mapMaybe)
import qualified Data.Text as T
import Data.Time (defaultTimeLocale, formatTime, parseTimeM, zonedTimeToUTC)
import Data.Time.LocalTime (ZonedTime)
import Data.Void (Void)
import System.Directory (doesFileExist, makeAbsolute)
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.FilePath (takeDirectory, (<.>), (</>))
import System.Process (readProcessWithExitCode)

import Control.Lens ((^.))
import qualified Data.Aeson as JSON
import qualified Language.LSP.Protocol.Lens as LSP
import Language.LSP.Protocol.Message (SMethod (..))
import qualified Language.LSP.Protocol.Message as LSPMsg
import Language.LSP.Protocol.Types (NormalizedUri, Position (..), Range (..),
                                    UInt, toNormalizedUri)
import qualified Language.LSP.Protocol.Types as LSPTypes
import Language.LSP.Server

import Telomare (LocTag (..), Pattern (..), ResolverError (..),
                 SourcePosition (..), SourceSpan (..),
                 UnprocessedParsedTermF (..), locStartLineColumn,
                 renderResolverError)
import Telomare.Eval (eval2IExpr)
import Telomare.Parser (AnnotatedUPT, parseModule, parseModuleDetailed)
import Telomare.Resolver (main2Term3)
import Text.Megaparsec.Error (ParseErrorBundle (..), errorBundlePretty,
                              errorOffset)

--------------------------------------------------------------------------------
-- Document state tracking

-- Results of parseModule:
--   Either errorString or a list of either imports or (name, binding) pairs.
type ParseResult = [Either AnnotatedUPT (String, AnnotatedUPT)]

-- Store module bindings for evaluation context
type ModuleBindings = [(String, ParseResult)]

data DocState = DocState
  { docText        :: T.Text
  , docVersion     :: Int
  , docParse       :: Either String ParseResult
  , docDiagnostics :: [LSPTypes.Diagnostic]
  } deriving (Show)

type DocStore = TVar (Map.Map NormalizedUri DocState)

data SymbolIndex = SymbolIndex
  { symbolDefinitions :: Map.Map T.Text LSPTypes.Location
  , symbolReferences  :: Map.Map T.Text [Range]
  } deriving (Eq, Show)

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
                    , optExecuteCommandCommands = Just [ "telomare.partialEval"
                                                       , "telomare.version"
                                                       ]
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
  , notificationHandler SMethod_TextDocumentDidOpen           $ didOpenHandler gState
  , notificationHandler SMethod_TextDocumentDidChange         $ didChangeHandler gState
  , notificationHandler SMethod_TextDocumentDidClose          $ didCloseHandler (docStore gState)
  , requestHandler     SMethod_TextDocumentSemanticTokensFull  $ semanticTokensFullHandler (docStore gState)
  , requestHandler     SMethod_TextDocumentSemanticTokensRange $ semanticTokensRangeHandler (docStore gState)
  , requestHandler     SMethod_TextDocumentDefinition          $ definitionHandler gState
  , requestHandler     SMethod_TextDocumentReferences          $ referencesHandler (docStore gState)
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
    "telomare.version" -> do
      version <- liftIO lspVersion
      sendNotification SMethod_WindowShowMessage $
        LSPTypes.ShowMessageParams
          LSPTypes.MessageType_Info
          ("Telomare LSP version: " <> version)
      respond . Right . LSPTypes.InL . JSON.String $ version
    _ -> respond . Right $ LSPTypes.InL JSON.Null

lspVersion :: IO T.Text
lspVersion = do
  parentTimestamp <- gitParentCommitTimestamp
  case parentTimestamp of
    Just timestamp -> pure timestamp
    Nothing -> do
      envVersion <- lookupEnv "TELOMARE_LSP_VERSION"
      pure . maybe "unknown" T.pack $ envVersion

gitParentCommitTimestamp :: IO (Maybe T.Text)
gitParentCommitTimestamp = do
  result <- try (readProcessWithExitCode "git" ["log", "-1", "--format=%cI", "HEAD^"] "") :: IO (Either IOException (ExitCode, String, String))
  pure $ case result of
    Right (ExitSuccess, stdout, _) -> formatTimestampMinutesUTC stdout
    _                              -> Nothing

formatTimestampMinutesUTC :: String -> Maybe T.Text
formatTimestampMinutesUTC rawTimestamp = do
  zonedTime <- parseTimeM True defaultTimeLocale "%Y-%m-%dT%H:%M:%S%Q%z" (takeWhile (/= '\n') rawTimestamp) :: Maybe ZonedTime
  pure . T.pack $ formatTime defaultTimeLocale "%Y-%m-%dT%H:%MZ" (zonedTimeToUTC zonedTime)

--------------------------------------------------------------------------------
-- Helpers: centralize parsing through parseModule

parseTelomareModule :: T.Text -> Either String ParseResult
parseTelomareModule = parseModule . T.unpack

parseTelomareModuleDetailed :: T.Text -> Either (ParseErrorBundle String Void) ParseResult
parseTelomareModuleDetailed = parseModuleDetailed . T.unpack

storeParsedDoc
  :: GlobalState
  -> LSPTypes.Uri
  -> Int
  -> T.Text
  -> LspM () ()
storeParsedDoc gState uri version text = do
  modules <- liftIO $ readTVarIO (moduleBindings gState)
  let detailedParse = parseTelomareModuleDetailed text
      parseRes = first errorBundlePretty detailedParse
      diagnostics = case detailedParse of
        Left err     -> parseDiagnostics text err
        Right parsed -> resolverDiagnostics modules parsed
  liftIO . atomically . modifyTVar' (docStore gState) $
    Map.insert (toNormalizedUri uri) (DocState text version parseRes diagnostics)
  publishDocumentDiagnostics uri version diagnostics

--------------------------------------------------------------------------------
-- Document lifecycle handlers

didOpenHandler :: GlobalState
               -> LSPMsg.TNotificationMessage 'LSPMsg.Method_TextDocumentDidOpen
               -> LspM () ()
didOpenHandler gState notification = do
  let doc     = notification ^. LSP.params . LSP.textDocument
      uri     = doc ^. LSP.uri
      version = fromIntegral (doc ^. LSP.version)
      text    = doc ^. LSP.text
  storeParsedDoc gState uri version text

didChangeHandler :: GlobalState
                  -> LSPMsg.TNotificationMessage 'LSPMsg.Method_TextDocumentDidChange
                  -> LspM () ()
didChangeHandler gState notification = do
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
      storeParsedDoc gState uri version newText

didCloseHandler :: DocStore
                -> LSPMsg.TNotificationMessage 'LSPMsg.Method_TextDocumentDidClose
                -> LspM () ()
didCloseHandler docStore' notification = do
  let uri = notification ^. LSP.params . LSP.textDocument . LSP.uri
  liftIO . atomically . modifyTVar' docStore' $ Map.delete (toNormalizedUri uri)
  publishDocumentDiagnostics uri 0 []

publishDocumentDiagnostics :: LSPTypes.Uri -> Int -> [LSPTypes.Diagnostic] -> LspM () ()
publishDocumentDiagnostics uri version diagnostics =
  sendNotification SMethod_TextDocumentPublishDiagnostics $
    LSPTypes.PublishDiagnosticsParams uri (Just $ fromIntegral version) diagnostics

parseDiagnostics :: T.Text -> ParseErrorBundle String Void -> [LSPTypes.Diagnostic]
parseDiagnostics text bundle =
  [ mkDiagnostic (offsetToRange text . errorOffset . NE.head $ bundleErrors bundle)
      "parser"
      (T.pack . diagnosticFirstLine $ errorBundlePretty bundle)
  ]

resolverDiagnostics :: ModuleBindings -> ParseResult -> [LSPTypes.Diagnostic]
resolverDiagnostics modules parsed =
  case main2Term3 (("Current", parsed) : modules) "Current" of
    Left NoMainFunction{} -> []
    Left err              -> resolverErrorDiagnostics err
    Right _               -> []

resolverErrorDiagnostics :: ResolverError -> [LSPTypes.Diagnostic]
resolverErrorDiagnostics err =
  case err of
    MissingDefinitionAt loc _ ->
      [mkDiagnostic (locTagToRange loc) "resolver" (T.pack $ renderResolverError err)]
    _ ->
      [mkDiagnostic fallbackRange "resolver" (T.pack $ renderResolverError err)]

mkDiagnostic :: Range -> T.Text -> T.Text -> LSPTypes.Diagnostic
mkDiagnostic range source message =
  LSPTypes.Diagnostic
    range
    (Just LSPTypes.DiagnosticSeverity_Error)
    Nothing
    Nothing
    (Just source)
    message
    Nothing
    Nothing
    Nothing

locTagToRange :: LocTag -> Range
locTagToRange loc = case loc of
  SourceLoc sourceSpan -> sourceSpanToRange sourceSpan
  _                    -> locTagStartToRange loc

locTagStartToRange :: LocTag -> Range
locTagStartToRange loc = case locStartLineColumn loc of
  Just (line, column) -> pointRange (line - 1) (column - 1)
  Nothing             -> fallbackRange

sourceSpanToRange :: SourceSpan -> Range
sourceSpanToRange sourceSpan =
  Range
    (sourcePositionToLSP $ sourceSpanStart sourceSpan)
    (sourcePositionToLSP $ sourceSpanEnd sourceSpan)

sourcePositionToLSP :: SourcePosition -> Position
sourcePositionToLSP pos =
  Position
    (fromIntegral . max 0 $ sourcePositionLine pos - 1)
    (fromIntegral . max 0 $ sourcePositionColumn pos - 1)

offsetToRange :: T.Text -> Int -> Range
offsetToRange text offset =
  let prefix = T.take offset text
      line = T.count "\n" prefix
      column = T.length . last $ T.splitOn "\n" prefix
  in pointRange line column

pointRange :: Int -> Int -> Range
pointRange line column =
  let line' = max 0 line
      column' = max 0 column
  in Range (Position (fromIntegral line') (fromIntegral column'))
           (Position (fromIntegral line') (fromIntegral $ column' + 1))

fallbackRange :: Range
fallbackRange = pointRange 0 0

diagnosticFirstLine :: String -> String
diagnosticFirstLine = takeWhile (/= '\n')

definitionHandler :: GlobalState
                  -> LSPMsg.TRequestMessage LSPMsg.Method_TextDocumentDefinition
                  -> (Either (LSPMsg.TResponseError LSPMsg.Method_TextDocumentDefinition)
                            (LSPTypes.Definition LSPTypes.|? ([LSPTypes.DefinitionLink] LSPTypes.|? LSPTypes.Null))
                       -> LspM () ())
                  -> LspM () ()
definitionHandler gState req respond = do
  let uri = req ^. LSP.params . LSP.textDocument . LSP.uri
      position = req ^. LSP.params . LSP.position
  mDoc <- liftIO . atomically $ Map.lookup (toNormalizedUri uri) <$> readTVar (docStore gState)
  mDefinition <- liftIO $ maybe (pure Nothing) (definitionAt gState uri position) mDoc
  case mDefinition of
    Just location -> respond . Right . LSPTypes.InL . LSPTypes.Definition . LSPTypes.InL $ location
    Nothing       -> respond . Right . LSPTypes.InR . LSPTypes.InR $ LSPTypes.Null

referencesHandler :: DocStore
                  -> LSPMsg.TRequestMessage LSPMsg.Method_TextDocumentReferences
                  -> (Either (LSPMsg.TResponseError LSPMsg.Method_TextDocumentReferences)
                           ([LSPTypes.Location] LSPTypes.|? LSPTypes.Null)
                      -> LspM () ())
                  -> LspM () ()
referencesHandler docStore' req respond = do
  let uri = req ^. LSP.params . LSP.textDocument . LSP.uri
      position = req ^. LSP.params . LSP.position
      includeDeclaration = req ^. LSP.params . LSP.context . LSP.includeDeclaration
  mDoc <- liftIO . atomically $ Map.lookup (toNormalizedUri uri) <$> readTVar docStore'
  let locations = foldMap (referencesAt uri includeDeclaration position) mDoc
  case locations of
    [] -> respond . Right $ LSPTypes.InR LSPTypes.Null
    _  -> respond . Right . LSPTypes.InL $ locations

--------------------------------------------------------------------------------
-- Source index for definition/reference requests

definitionAt :: GlobalState -> LSPTypes.Uri -> Position -> DocState -> IO (Maybe LSPTypes.Location)
definitionAt gState uri position docState = case docParse docState of
  Left _ -> pure Nothing
  Right parsed -> do
    importedDefinitions <- importedDefinitionIndex gState uri parsed
    let currentIndex = buildSymbolIndex uri (docText docState) parsed
        definitions = symbolDefinitions currentIndex <> importedDefinitions
    pure $ do
      symbol <- symbolAtPosition position currentIndex
      Map.lookup symbol definitions

referencesAt :: LSPTypes.Uri -> Bool -> Position -> DocState -> [LSPTypes.Location]
referencesAt uri includeDeclaration position docState =
  case docParse docState of
    Left _ -> []
    Right parsed ->
      let index = buildSymbolIndex uri (docText docState) parsed
          symbol = symbolAtPosition position index
      in case symbol of
        Nothing -> []
        Just name ->
          let refs = Map.findWithDefault [] name (symbolReferences index)
              defs = foldMap (pure . locationRange) $ Map.lookup name (symbolDefinitions index)
              ranges = if includeDeclaration then defs <> refs else refs
          in LSPTypes.Location uri <$> ranges

importedDefinitionIndex :: GlobalState -> LSPTypes.Uri -> ParseResult -> IO (Map.Map T.Text LSPTypes.Location)
importedDefinitionIndex gState currentUri parsed = do
  imports <- mapM (loadImportedDefinitionIndex gState currentUri) $ moduleImports parsed
  pure . Map.unions $ imports

loadImportedDefinitionIndex :: GlobalState -> LSPTypes.Uri -> ModuleImport -> IO (Map.Map T.Text LSPTypes.Location)
loadImportedDefinitionIndex gState currentUri moduleImport = do
  mModule <- loadImportedModule gState currentUri (importModuleName moduleImport)
  case mModule of
    Nothing -> pure Map.empty
    Just (moduleUri, moduleText, moduleParsed) -> do
      let definitions = symbolDefinitions $ buildSymbolIndex moduleUri moduleText moduleParsed
      pure $ qualifyDefinitions moduleImport definitions

qualifyDefinitions :: ModuleImport -> Map.Map T.Text LSPTypes.Location -> Map.Map T.Text LSPTypes.Location
qualifyDefinitions moduleImport definitions = case importQualifier moduleImport of
  Nothing        -> definitions
  Just qualifier -> Map.mapKeys ((T.pack qualifier <> ".") <>) definitions

data ModuleImport = ModuleImport
  { importModuleName :: String
  , importQualifier  :: Maybe String
  } deriving (Eq, Show)

moduleImports :: ParseResult -> [ModuleImport]
moduleImports = mapMaybe $ \case
  Left (_ :< ImportUPF moduleName) ->
    Just $ ModuleImport moduleName Nothing
  Left (_ :< ImportQualifiedUPF qualifier moduleName) ->
    Just $ ModuleImport moduleName (Just qualifier)
  _ -> Nothing

loadImportedModule :: GlobalState -> LSPTypes.Uri -> String -> IO (Maybe (LSPTypes.Uri, T.Text, ParseResult))
loadImportedModule gState currentUri moduleName = do
  candidates <- moduleFileCandidates currentUri moduleName
  mPath <- firstExistingFile candidates
  case mPath of
    Nothing -> pure Nothing
    Just path -> do
      absolutePath <- makeAbsolute path
      let moduleUri = LSPTypes.filePathToUri absolutePath
      openDocs <- readTVarIO $ docStore gState
      case Map.lookup (toNormalizedUri moduleUri) openDocs of
        Just docState | Right parsed <- docParse docState ->
          pure $ Just (moduleUri, docText docState, parsed)
        _ -> do
          loaded <- try (readFile absolutePath) :: IO (Either IOException String)
          pure $ case loaded of
            Left _ -> Nothing
            Right content -> case parseTelomareModule (T.pack content) of
              Left _       -> Nothing
              Right parsed -> Just (moduleUri, T.pack content, parsed)

moduleFileCandidates :: LSPTypes.Uri -> String -> IO [FilePath]
moduleFileCandidates currentUri moduleName = do
  cwdModule <- makeAbsolute moduleFile
  pure $ maybe [cwdModule, "lib" </> moduleFile]
               (\currentPath -> [takeDirectory currentPath </> moduleFile, cwdModule, "lib" </> moduleFile])
               (LSPTypes.uriToFilePath currentUri)
  where
    moduleFile = moduleName <.> "tel"

firstExistingFile :: [FilePath] -> IO (Maybe FilePath)
firstExistingFile [] = pure Nothing
firstExistingFile (path:paths) = do
  exists <- doesFileExist path
  if exists
    then pure $ Just path
    else firstExistingFile paths

locationRange :: LSPTypes.Location -> Range
locationRange (LSPTypes.Location _ range) = range

symbolAtPosition :: Position -> SymbolIndex -> Maybe T.Text
symbolAtPosition position index =
  locatedDefinition <|> locatedReference
  where
    locatedDefinition = fst <$> find (positionInRange position . locationRange . snd) (Map.toList $ symbolDefinitions index)
    locatedReference = fst <$> find (any (positionInRange position) . snd) (Map.toList $ symbolReferences index)

buildSymbolIndex :: LSPTypes.Uri -> T.Text -> ParseResult -> SymbolIndex
buildSymbolIndex uri text parsed = SymbolIndex definitions references
  where
    definitions = topLevelDefinitions uri text parsed
    references = Map.fromListWith (<>)
      [ (T.pack name, [range])
      | Right (_, term) <- parsed
      , (name, range) <- termReferences [] term
      ]

topLevelDefinitions :: LSPTypes.Uri -> T.Text -> ParseResult -> Map.Map T.Text LSPTypes.Location
topLevelDefinitions uri text parsed = Map.fromList
  [ (T.pack name, LSPTypes.Location uri range)
  | Right (name, _) <- parsed
  , Just range <- [findTopLevelDefinition text (T.pack name)]
  ]

findTopLevelDefinition :: T.Text -> T.Text -> Maybe Range
findTopLevelDefinition text name =
  let indexedLines = zip [0..] $ T.lines text
      matchingLines =
        [ textRange line column (T.length name)
        | (line, lineText) <- indexedLines
        , Just column <- [findTopLevelIdentifier name lineText]
        ]
  in listToMaybe matchingLines

findTopLevelIdentifier :: T.Text -> T.Text -> Maybe Int
findTopLevelIdentifier name lineText
  | not (isTopLevelLine lineText) = Nothing
  | T.isInfixOf "=" lineText = findIdentifierInLhs name lineText
  | T.stripEnd lineText == name = Just 0
  | otherwise = Nothing

isTopLevelLine :: T.Text -> Bool
isTopLevelLine lineText =
  not (T.null lineText)
    && notElem (T.head lineText) [' ', '\t']
    && not ("--" `T.isPrefixOf` lineText)

findIdentifierInLhs :: T.Text -> T.Text -> Maybe Int
findIdentifierInLhs name lineText = go 0 lhs
  where
    lhs = T.takeWhile (/= '=') lineText
    go column remaining
      | T.null remaining = Nothing
      | T.isPrefixOf name remaining && beforeBoundary column && afterBoundary remaining = Just column
      | otherwise = go (column + 1) (T.tail remaining)
    beforeBoundary column =
      column == 0 || not (lspIdentChar . T.last $ T.take column lhs)
    afterBoundary remaining =
      let afterName = T.drop (T.length name) remaining
      in T.null afterName || not (lspIdentChar $ T.head afterName)

termReferences :: [String] -> AnnotatedUPT -> [(String, Range)]
termReferences bound (loc :< term) =
  let children = case term of
        VarUPF name
          | name `elem` bound -> []
          | otherwise         -> [(name, locTagToRange loc)]
        ITEUPF i t e -> termReferences bound i <> termReferences bound t <> termReferences bound e
        LetUPF bindings body ->
          let localNames = fst <$> bindings
              bound' = localNames <> bound
          in concatMap (termReferences bound' . snd) bindings <> termReferences bound' body
        ListUPF items -> concatMap (termReferences bound) items
        PairUPF a b -> termReferences bound a <> termReferences bound b
        AppUPF f x -> termReferences bound f <> termReferences bound x
        LamUPF var body -> termReferences (var : bound) body
        LeftUPF x -> termReferences bound x
        RightUPF x -> termReferences bound x
        TraceUPF x -> termReferences bound x
        CheckUPF checkExpr body -> termReferences bound checkExpr <> termReferences bound body
        HashUPF x -> termReferences bound x
        UDTUPF names body -> termReferences (names <> bound) body
        CaseUPF scrutinee cases -> termReferences bound scrutinee <> concatMap caseReferences cases
        _ -> []
  in children
  where
    caseReferences (pat, body) = termReferences (patternBoundNames pat <> bound) body

patternBoundNames :: Pattern -> [String]
patternBoundNames = \case
  PatternVar name -> [name]
  PatternAnnotated pat _ -> patternBoundNames pat
  PatternPair left right -> patternBoundNames left <> patternBoundNames right
  _ -> []

lspIdentChar :: Char -> Bool
lspIdentChar c = isAsciiLower c || isAsciiUpper c || isDigit c || c == '_' || c == '.' || c == '\''

textRange :: Int -> Int -> Int -> Range
textRange line column len =
  Range
    (Position (fromIntegral line) (fromIntegral column))
    (Position (fromIntegral line) (fromIntegral $ column + len))

positionInRange :: Position -> Range -> Bool
positionInRange (Position line char) (Range (Position startLine startChar) (Position endLine endChar)) =
  (line > startLine || line == startLine && char >= startChar)
    && (line < endLine || line == endLine && char < endChar)

--------------------------------------------------------------------------------
-- Semantic tokens (kept using the simple lexer for now)

semanticTokensFullHandler :: DocStore
                          -> LSPMsg.TRequestMessage LSPMsg.Method_TextDocumentSemanticTokensFull
                          -> (Either (LSPMsg.TResponseError LSPMsg.Method_TextDocumentSemanticTokensFull)
                                   (LSPTypes.SemanticTokens LSPTypes.|? LSPTypes.Null)
                             -> LspM () ())
                          -> LspM () ()
semanticTokensFullHandler docStore' req respond = do
  let uri = req ^. LSP.params . LSP.textDocument . LSP.uri
  mDoc <- liftIO . atomically $ Map.lookup (toNormalizedUri uri) <$> readTVar docStore'
  case mDoc of
    Nothing -> respond . Right . LSPTypes.InL $ LSPTypes.SemanticTokens Nothing []
    Just docState -> do
      let tokens  = lexTelomare (docText docState)
          encoded = tokensToLSP tokens
      respond . Right . LSPTypes.InL $ LSPTypes.SemanticTokens Nothing encoded

semanticTokensRangeHandler :: DocStore
                           -> LSPMsg.TRequestMessage LSPMsg.Method_TextDocumentSemanticTokensRange
                           -> (Either (LSPMsg.TResponseError LSPMsg.Method_TextDocumentSemanticTokensRange)
                                    (LSPTypes.SemanticTokens LSPTypes.|? LSPTypes.Null)
                              -> LspM () ())
                           -> LspM () ()
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

  mDoc <- liftIO . atomically $ Map.lookup (toNormalizedUri uri) <$> readTVar (docStore gState)
  case mDoc of
    Nothing -> respond . Right . LSPTypes.InL $ []
    Just docState -> do
      case docParse docState of
        Left _ -> respond . Right . LSPTypes.InL $ []
        Right _ -> do
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
codeActionResolveHandler _ req respond = do
  -- For now, just return the action as-is since we're using commands
  -- The request body should contain a CodeAction
  let codeAction = req ^. LSP.params
  respond $ Right codeAction

-- Execute partial evaluation and show result
executePartialEvaluation :: GlobalState -> LSPTypes.Uri -> Range -> T.Text -> LspM () ()
executePartialEvaluation gState _ _ exprText = do
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
