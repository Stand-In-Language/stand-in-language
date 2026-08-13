{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module Main where

import Control.Applicative ((<|>))
import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Concurrent.STM
import Control.Exception (IOException, try)
import Control.Monad (guard, join, void)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Bifunctor (first)
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.Fix (Fix (..))
import Data.List (find, sortOn)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe, mapMaybe)
import qualified Data.Set as Set
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

import Telomare.Driver (eval2IExpr)
import Telomare.Error
import Telomare.Expand (ExpansionError, expandModule, expansionErrorLoc,
                        renderExpansionError)
import Telomare.IR.Base
import Telomare.IR.Loc
import Telomare.IR.Surface
import Telomare.Parse (runParseModule, runParseModuleDetailed)
import Telomare.Resolve (main2Term3)
import Text.Megaparsec.Error (ParseErrorBundle (..), errorBundlePretty,
                              errorOffset)

--------------------------------------------------------------------------------
-- Document state tracking

data DocState = DocState
  { docText        :: T.Text
  , docVersion     :: Int
  , docParse       :: Either String ExpandedModule
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
  , moduleBindings :: TVar ExpandedModules
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
loadPrelude :: IO ExpandedModules
loadPrelude = do
  -- Try to load Prelude.tel from common locations
  let preludePaths = ["Prelude.tel", "lib/Prelude.tel", "../lib/Prelude.tel"]
  preludeContents <- tryLoadFiles preludePaths
  case preludeContents of
    Nothing -> return []
    Just content ->
      case parseTelomareModule (T.pack content) of
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
tokComment, tokKeyword, tokString, tokNumber, tokOperator, tokVariable :: UInt
tokKeyword  = 1   -- "keyword"
tokComment  = 0   -- "comment"
tokString   = 2   -- "string"
tokNumber   = 3   -- "number"
tokOperator = 5   -- "operator"
tokVariable = 19  -- "variable"

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
-- Helpers: centralize parsing through runParseModule + expandModule

parseTelomareModule :: T.Text -> Either String ExpandedModule
parseTelomareModule text =
  runParseModule "" (T.unpack text)
    >>= first renderExpansionError . expandModule

-- |Raw parse only, keeping the megaparsec bundle so parse diagnostics can
-- use 'errorOffset'. Callers run 'expandModule' on the result themselves.
parseTelomareModuleDetailed :: T.Text -> Either (ParseErrorBundle String Void) [ModuleItem ParsedSurfaceTerm]
parseTelomareModuleDetailed = runParseModuleDetailed "" . T.unpack

storeParsedDoc
  :: GlobalState
  -> LSPTypes.Uri
  -> Int
  -> T.Text
  -> LspM () ()
storeParsedDoc gState uri version text = do
  modules <- liftIO $ readTVarIO (moduleBindings gState)
  let detailedParse = parseTelomareModuleDetailed text
      expanded = expandModule <$> detailedParse
      parseRes = case expanded of
        Left parseErr      -> Left $ errorBundlePretty parseErr
        Right (Left err)   -> Left $ renderExpansionError err
        Right (Right tree) -> Right tree
  diagnostics' <- case expanded of
    Left err -> pure $ parseDiagnostics text err
    Right (Left err) -> pure $ expansionDiagnostics text err
    Right (Right parsed) -> do
      importedModules <- liftIO $ concat <$> mapM (loadImportedModuleBinding gState uri) (moduleImports parsed)
      let modules' = importedModules <> modules
          importDiagnostics' = importDiagnostics text modules' parsed
          semanticDiagnostics = undefinedVariableDiagnostics text modules' parsed
      pure . dedupeDiagnostics $ importDiagnostics'
          <> semanticDiagnostics
          <> if null importDiagnostics'
             then resolverDiagnostics text modules' parsed
             else []
  liftIO . atomically . modifyTVar' (docStore gState) $
    Map.insert (toNormalizedUri uri) (DocState text version parseRes diagnostics')
  publishDocumentDiagnostics uri version diagnostics'

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
      (T.pack $ errorBundlePretty bundle)
  ]

-- |Expansion errors point at the 'LocTag' the 'ExpansionError' carries (falling
-- back to the start of the document when it has none).
expansionDiagnostics :: T.Text -> ExpansionError -> [LSPTypes.Diagnostic]
expansionDiagnostics text err =
  [ mkDiagnostic range "expand" (T.pack $ renderExpansionError err) ]
  where
    range = maybe fallbackRange (locTagToRangeIn text) $ expansionErrorLoc err

loadImportedModuleBinding :: GlobalState -> LSPTypes.Uri -> ImportDecl -> IO ExpandedModules
loadImportedModuleBinding gState currentUri moduleImport = do
  mModule <- loadImportedModule gState currentUri (importModuleName moduleImport)
  pure $ case mModule of
    Nothing             -> []
    Just (_, _, parsed) -> [(importModuleName moduleImport, parsed)]

importDiagnostics :: T.Text -> ExpandedModules -> ExpandedModule -> [LSPTypes.Diagnostic]
importDiagnostics text modules parsed =
  [ mkDiagnostic (moduleImportRange text moduleImport) "resolver" $
      T.pack ("module not found " <> show (importModuleName moduleImport))
  | moduleImport <- moduleImports parsed
  , importModuleName moduleImport `notElem` (fst <$> modules)
  ]

moduleImportRange :: T.Text -> ImportDecl -> Range
moduleImportRange text = locTagToRangeIn text . locatedNameLoc . parsedImportModule

undefinedVariableDiagnostics :: T.Text -> ExpandedModules -> ExpandedModule -> [LSPTypes.Diagnostic]
undefinedVariableDiagnostics text modules parsed =
  dedupeDiagnostics
    [ mkDiagnostic range "resolver" $ T.pack ("missing definition " <> show name)
    | (name, range) <- unresolvedReferences text globals parsed
    ]
  where
    globals = Set.fromList $ builtinNames <> importedDefinitionNames modules parsed <> currentDefinitionNames parsed

builtinNames :: [String]
builtinNames = ["zero", "left", "right", "trace", "pair", "app"]

importedDefinitionNames :: ExpandedModules -> ExpandedModule -> [String]
importedDefinitionNames modules parsed =
  [ maybe name (<> ('.' : name)) (importQualifier moduleImport)
  | moduleImport <- moduleImports parsed
  , Just moduleParsed <- [lookup (importModuleName moduleImport) modules]
  , ExpandedModuleBinding locatedName' _ <- moduleParsed
  , let name = locatedNameText locatedName'
  ]

currentDefinitionNames :: ExpandedModule -> [String]
currentDefinitionNames parsed =
  [ locatedNameText name | ExpandedModuleBinding name _ <- parsed ]

unresolvedReferences :: T.Text -> Set.Set String -> ExpandedModule -> [(String, Range)]
unresolvedReferences text globals parsed =
  concatMap (unresolvedTerm text globals)
    [term | ExpandedModuleBinding _ term <- parsed]

unresolvedTerm :: T.Text -> Set.Set String -> ExpandedSurfaceTerm -> [(String, Range)]
unresolvedTerm text globals = go Set.empty
  where
    go bound (loc :< term) = case term of
      UnprocessedParsedTermL (VarF name)
        | name `Set.member` bound || name `Set.member` globals -> []
        | otherwise -> [(name, locTagToRangeIn text loc)]
      LetUPF bindings body ->
        let localNames = Set.fromList $ letBindingName <$> bindings
            bound' = localNames <> bound
        in concatMap (go bound' . letBindingValue) bindings <> go bound' body
      UnprocessedParsedTermL (LamF name body) -> go (Set.insert (locatedNameText name) bound) body
      CaseUPF scrutinee cases ->
        go bound scrutinee <> concatMap (caseRefs bound) cases
      UnprocessedParsedTermH (ITEF i t e) -> concatMap (go bound) [i, t, e]
      ListUPF items -> concatMap (go bound) items
      UnprocessedParsedTermB (PairSF a b) -> concatMap (go bound) [a, b]
      UnprocessedParsedTermL (AppF f x) -> concatMap (go bound) [f, x]
      UnprocessedParsedTermH (HLeftF x) -> go bound x
      UnprocessedParsedTermH (HRightF x) -> go bound x
      UnprocessedParsedTermH (HTraceF x) -> go bound x
      UnprocessedParsedTermH (CheckF checkExpr body) -> go bound checkExpr <> go bound body
      UnprocessedParsedTermH (HashF x) -> go bound x
      UnprocessedParsedTermH (RecursionF t r b) -> concatMap (go bound) [t, r, b]
      _ -> []

    caseRefs bound (pat, body) =
      concatMap (go bound) (patternAnnotationTerms pat)
        <> go (Set.union (Set.fromList $ patternBoundNames pat) bound) body

dedupeDiagnostics :: [LSPTypes.Diagnostic] -> [LSPTypes.Diagnostic]
dedupeDiagnostics = Map.elems . Map.fromList . fmap (\diagnostic -> (diagnosticKey diagnostic, diagnostic))

diagnosticKey :: LSPTypes.Diagnostic -> (Range, Maybe T.Text, T.Text)
diagnosticKey diagnostic =
  (diagnostic ^. LSP.range, diagnostic ^. LSP.source, diagnostic ^. LSP.message)

resolverDiagnostics :: T.Text -> ExpandedModules -> ExpandedModule -> [LSPTypes.Diagnostic]
resolverDiagnostics text modules parsed =
  case main2Term3 (("Current", parsed) : modules) "Current" of
    Left NoMainFunction{} -> []
    Left err              -> resolverErrorDiagnostics text err
    Right _               -> []

resolverErrorDiagnostics :: T.Text -> ResolverError -> [LSPTypes.Diagnostic]
resolverErrorDiagnostics text err =
  case err of
    MissingDefinitionAt loc _ ->
      [mkDiagnostic (locTagToRangeIn text loc) "resolver" (T.pack $ renderResolverError err)]
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

-- |Convert parser offsets through the document text. Megaparsec columns use
-- tab stops, while LSP character positions count a tab as one character.
locTagToRangeIn :: T.Text -> LocTag -> Range
locTagToRangeIn text loc = case loc of
  SourceLoc sourceSpan ->
    Range
      (offsetToPosition text . sourcePositionOffset $ sourceSpanStart sourceSpan)
      (offsetToPosition text . sourcePositionOffset $ sourceSpanEnd sourceSpan)
  _ -> locTagStartToRange loc

locTagStartToRange :: LocTag -> Range
locTagStartToRange loc = case locStartLineColumn loc of
  Just (line, column) -> pointRange (line - 1) (column - 1)
  Nothing             -> fallbackRange

offsetToRange :: T.Text -> Int -> Range
offsetToRange text offset =
  let position@(Position line character) = offsetToPosition text offset
  in Range position (Position line $ character + 1)

offsetToPosition :: T.Text -> Int -> Position
offsetToPosition text offset =
  let prefix = T.take offset text
      line = T.count "\n" prefix
      column = T.length . last $ T.splitOn "\n" prefix
  in Position (fromIntegral line) (fromIntegral column)

pointRange :: Int -> Int -> Range
pointRange line column =
  let line' = max 0 line
      column' = max 0 column
  in Range (Position (fromIntegral line') (fromIntegral column'))
           (Position (fromIntegral line') (fromIntegral $ column' + 1))

fallbackRange :: Range
fallbackRange = pointRange 0 0

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
      localDefinitionAt uri (docText docState) position parsed <|> do
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

importedDefinitionIndex :: GlobalState -> LSPTypes.Uri -> ExpandedModule -> IO (Map.Map T.Text LSPTypes.Location)
importedDefinitionIndex gState currentUri parsed = do
  imports <- mapM (loadImportedDefinitionIndex gState currentUri) $ moduleImports parsed
  pure . Map.unions $ imports

loadImportedDefinitionIndex :: GlobalState -> LSPTypes.Uri -> ImportDecl -> IO (Map.Map T.Text LSPTypes.Location)
loadImportedDefinitionIndex gState currentUri moduleImport = do
  mModule <- loadImportedModule gState currentUri (importModuleName moduleImport)
  case mModule of
    Nothing -> pure Map.empty
    Just (moduleUri, moduleText, moduleParsed) -> do
      let definitions = symbolDefinitions $ buildSymbolIndex moduleUri moduleText moduleParsed
      pure $ qualifyDefinitions moduleImport definitions

qualifyDefinitions :: ImportDecl -> Map.Map T.Text LSPTypes.Location -> Map.Map T.Text LSPTypes.Location
qualifyDefinitions moduleImport definitions = case importQualifier moduleImport of
  Nothing        -> definitions
  Just qualifier -> Map.mapKeys ((T.pack qualifier <> ".") <>) definitions

importModuleName :: ImportDecl -> String
importModuleName = locatedNameText . parsedImportModule

importQualifier :: ImportDecl -> Maybe String
importQualifier = fmap locatedNameText . parsedImportQualifier

moduleImports :: ExpandedModule -> [ImportDecl]
moduleImports parsed =
  [ importDecl | ExpandedModuleImport importDecl <- parsed ]

loadImportedModule :: GlobalState -> LSPTypes.Uri -> String -> IO (Maybe (LSPTypes.Uri, T.Text, ExpandedModule))
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

buildSymbolIndex :: LSPTypes.Uri -> T.Text -> ExpandedModule -> SymbolIndex
buildSymbolIndex uri text parsed = SymbolIndex definitions references
  where
    definitions = topLevelDefinitions uri text parsed
    references = Map.fromListWith (<>)
      [ (T.pack name, [range])
      | ExpandedModuleBinding _ term <- parsed
      , (name, range) <- termReferences text [] term
      ]

topLevelDefinitions :: LSPTypes.Uri -> T.Text -> ExpandedModule -> Map.Map T.Text LSPTypes.Location
topLevelDefinitions uri text parsed = Map.fromList
  [ (T.pack $ locatedNameText name, LSPTypes.Location uri range)
  | ExpandedModuleBinding name _ <- parsed
  , let range = locTagToRangeIn text $ locatedNameLoc name
  , SourceLoc _ <- [locatedNameLoc name]
  ]

termReferences :: T.Text -> [String] -> ExpandedSurfaceTerm -> [(String, Range)]
termReferences text bound (loc :< term) =
  let children = case term of
        UnprocessedParsedTermL (VarF name)
          | name `elem` bound -> []
          | otherwise         -> [(name, locTagToRangeIn text loc)]
        UnprocessedParsedTermH (ITEF i t e) -> termReferences text bound i <> termReferences text bound t <> termReferences text bound e
        LetUPF bindings body ->
          let localNames = letBindingName <$> bindings
              bound' = localNames <> bound
          in concatMap (termReferences text bound' . letBindingValue) bindings <> termReferences text bound' body
        ListUPF items -> concatMap (termReferences text bound) items
        UnprocessedParsedTermB (PairSF a b) -> termReferences text bound a <> termReferences text bound b
        UnprocessedParsedTermL (AppF f x) -> termReferences text bound f <> termReferences text bound x
        UnprocessedParsedTermL (LamF var body) -> termReferences text (locatedNameText var : bound) body
        UnprocessedParsedTermH (HLeftF x) -> termReferences text bound x
        UnprocessedParsedTermH (HRightF x) -> termReferences text bound x
        UnprocessedParsedTermH (HTraceF x) -> termReferences text bound x
        UnprocessedParsedTermH (CheckF checkExpr body) -> termReferences text bound checkExpr <> termReferences text bound body
        UnprocessedParsedTermH (HashF x) -> termReferences text bound x
        CaseUPF scrutinee cases -> termReferences text bound scrutinee <> concatMap caseReferences cases
        _ -> []
  in children
  where
    caseReferences (pat, body) =
      concatMap (termReferences text bound) (patternAnnotationTerms pat)
        <> termReferences text (patternBoundNames pat <> bound) body

localDefinitionAt :: LSPTypes.Uri -> T.Text -> Position -> ExpandedModule -> Maybe LSPTypes.Location
localDefinitionAt uri text position parsed =
  listToMaybe [ location
              | ExpandedModuleBinding _ term <- parsed
              , location <- foldMap pure $ localTermDefinitionAt uri text position Map.empty term
              ]

localTermDefinitionAt :: LSPTypes.Uri
                      -> T.Text
                      -> Position
                      -> Map.Map String (Maybe LSPTypes.Location)
                      -> ExpandedSurfaceTerm
                      -> Maybe LSPTypes.Location
localTermDefinitionAt uri text position env (loc :< term) = case term of
  UnprocessedParsedTermL (VarF name)
    | positionInRange position (locTagToRangeIn text loc) -> join $ Map.lookup name env
    | otherwise -> Nothing
  LetUPF bindings body ->
    let bindingLocations = Map.fromList
          [ (locatedNameText name, Just $ LSPTypes.Location uri (locTagToRangeIn text $ locatedNameLoc name))
          | (name, _) <- bindings
          ]
        env' = bindingLocations <> env
        bindingDefinition = listToMaybe
          [ LSPTypes.Location uri (locTagToRangeIn text $ locatedNameLoc name)
          | (name, _) <- bindings
          , positionInRange position (locTagToRangeIn text $ locatedNameLoc name)
          ]
        bindingRefs = listToMaybe
          [ location
          | binding <- bindings
          , location <- foldMap pure $ localTermDefinitionAt uri text position env' (letBindingValue binding)
          ]
    in bindingDefinition <|> bindingRefs <|> localTermDefinitionAt uri text position env' body
  UnprocessedParsedTermH (ITEF i t e) -> firstJust [i, t, e]
  ListUPF items -> firstJust items
  UnprocessedParsedTermB (PairSF a b) -> firstJust [a, b]
  UnprocessedParsedTermL (AppF f x) -> firstJust [f, x]
  UnprocessedParsedTermL (LamF name body) ->
    let nameLoc = locatedNameLoc name
        location = LSPTypes.Location uri (locTagToRangeIn text nameLoc)
        env' = Map.insert (locatedNameText name) (Just location) env
    in if positionInRange position (locTagToRangeIn text nameLoc)
         then Just location
         else localTermDefinitionAt uri text position env' body
  UnprocessedParsedTermH (HLeftF x) -> localTermDefinitionAt uri text position env x
  UnprocessedParsedTermH (HRightF x) -> localTermDefinitionAt uri text position env x
  UnprocessedParsedTermH (HTraceF x) -> localTermDefinitionAt uri text position env x
  UnprocessedParsedTermH (CheckF checkExpr body) -> firstJust [checkExpr, body]
  UnprocessedParsedTermH (HashF x) -> localTermDefinitionAt uri text position env x
  CaseUPF scrutinee cases ->
    localTermDefinitionAt uri text position env scrutinee
      <|> listToMaybe (mapMaybe caseDefinition cases)
  _ -> Nothing
  where
    firstJust = listToMaybe . mapMaybe (localTermDefinitionAt uri text position env)
    caseDefinition (pat, caseBody) =
      let bindings = patternBoundNamesLocated pat
          bindingLocation name = LSPTypes.Location uri (locTagToRangeIn text $ locatedNameLoc name)
          env' = foldr (\name -> Map.insert (locatedNameText name) (Just $ bindingLocation name)) env bindings
      in listToMaybe [ bindingLocation name
                     | name <- bindings
                      , positionInRange position (locTagToRangeIn text $ locatedNameLoc name)
                     ]
         <|> listToMaybe
           (mapMaybe (localTermDefinitionAt uri text position env) $ patternAnnotationTerms pat)
         <|> localTermDefinitionAt uri text position env' caseBody

patternBoundNames :: PatternA -> [String]
patternBoundNames = fmap locatedNameText . patternBoundNamesLocated

patternBoundNamesLocated :: PatternA -> [LocatedName]
patternBoundNamesLocated (Fix patternF) = case patternF of
  PatternVarF name        -> [name]
  PatternAnnotatedF pat _ -> patternBoundNamesLocated pat
  PatternPairF left right -> patternBoundNamesLocated left <> patternBoundNamesLocated right
  _                       -> []

patternAnnotationTerms :: PatternA -> [ExpandedSurfaceTerm]
patternAnnotationTerms (Fix patternF) = case patternF of
  PatternAnnotatedF pat annotation ->
    patternAnnotationTerms pat <> [unAnnotatedEST annotation]
  PatternPairF left right ->
    patternAnnotationTerms left <> patternAnnotationTerms right
  _ -> []

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

evaluateExpression :: ExpandedModules -> T.Text -> Either String String
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
