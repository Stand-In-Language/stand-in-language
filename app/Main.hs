{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.Monad (unless, void, when)
import Data.Maybe (fromMaybe)
import qualified Options.Applicative as O
import System.Directory (doesFileExist)
import System.Exit (exitFailure)
import System.FilePath (replaceExtension, takeBaseName)
import System.IO (hFlush, hPutStr, hPutStrLn, stderr, stdout)

import Telomare.Artifact (Artifact (..), isArtifactPath, nodeCount,
                          readArtifact, sourcesHash, telcExtension,
                          writeArtifact)
import Telomare.Certificate (renderStaticReport)
import Telomare.Driver (CompiledProgram (..), compileModules, evalLoop,
                        evalLoopIC, evalLoopMetered, programPlan)
import Telomare.Eval.IC (ICPlan, renderICMeter)
import Telomare.Eval.Meter (renderMeter)
import Telomare.Fast (compileFast, defaultFastFuel, renderFastMeter,
                      runFastLoop)
import Telomare.IR.Loc (locatedNameText)
import Telomare.IR.Surface (ImportDecl (parsedImportModule), ModuleItem (..))
import Telomare.Levels (levelsInfo)
import Telomare.Parse (runParseModule)
import Telomare.Size (SizingReport)

-- |What to do with the program.
data Action
  = Run
  | Compile (Maybe FilePath)
  -- ^Size it once and write the result, so later runs need not size again.
  | Certificate
  -- ^Report what is known about it statically, then exit.
  | Meter
  -- ^Run it, then report what the run cost.
  deriving (Eq, Show)

-- |How to get to a runnable program.
data Mode
  = Sized
  -- ^The usual route: infer every recursion's iteration count, which is what
  -- makes the program total.
  | Fast (Maybe Int)
  -- ^Skip sizing and run the recursion on demand, under a fuel cap. Faster to
  -- start, and proves nothing.
  | ICRuntime
  -- ^Size as usual, then run on the interaction-combinator runtime
  -- ('Telomare.IC'): admission-gated on the program's EAL certificate, and
  -- guided by the capture layouts the certificate publishes.
  deriving (Eq, Show)

-- |Which evaluator a run uses, once the program is compiled.
data Runtime = Reference | ICNet deriving (Eq, Show)

runtimeOf :: Mode -> Runtime
runtimeOf = \case
  ICRuntime -> ICNet
  _         -> Reference

data TelomareOpts = TelomareOpts
  { telomareFile   :: String
  , telomareAction :: Action
  , telomareMode   :: Mode
  }

telomareOpts :: O.Parser TelomareOpts
telomareOpts = TelomareOpts
  <$> O.argument O.str (O.metavar "TELOMARE-FILE")
  <*> action
  <*> mode
  where
    action = compileTo
         O.<|> O.flag' Certificate
               ( O.long "certificate"
                 <> O.help "Report each recursion site's inferred iteration count and \
                           \nesting level, then exit" )
         O.<|> O.flag' Meter
               ( O.long "meter"
                 <> O.help "Run the program, then report what the run cost" )
         O.<|> pure Run
    compileTo = O.flag' Compile
                  ( O.long "compile"
                    <> O.help ("Size the program once and write it to a " <> telcExtension
                               <> " file, which later runs can use directly") )
                <*> O.optional (O.strOption
                      ( O.long "output" <> O.short 'o' <> O.metavar "FILE"
                        <> O.help "Where to write the compiled program" ))
    mode = O.flag' () ( O.long "fast"
                        <> O.help "Run without sizing: starts immediately, but nothing \
                                  \proves the program terminates" )
             *> (Fast <$> fuel)
       O.<|> O.flag' ICRuntime
             ( O.long "ic"
               <> O.help "Run on the interaction-combinator runtime, gated on the \
                         \program's EAL certificate and guided by its capture layouts" )
       O.<|> pure Sized
    fuel = fmap toCap . O.optional $ O.option O.auto
      ( O.long "fuel" <> O.metavar "N"
        <> O.help ("Cap on applications and unrollings per iteration under --fast \
                   \(default " <> show defaultFastFuel <> "; 0 for no cap)") )
    toCap = \case
      Nothing -> Just defaultFastFuel
      Just 0  -> Nothing
      Just n  -> Just n

-- | Recursively load only the modules reachable from the entry file.
getModulesFor :: String -> IO [(String, String)]
getModulesFor entryModule = go [entryModule] []
  where
    go [] loaded = return loaded
    go (m:queue) loaded
      | m `elem` fmap fst loaded = go queue loaded
      | otherwise = do
          let filePath = m <> ".tel"
          content <- readFile filePath
          let imports = extractImports m content
          go (queue <> imports) ((m, content) : loaded)

    -- The real module parser, so commented-out and multi-line imports are
    -- read the same way the compile step will read them. A module that does
    -- not parse has no imports to follow; the compile step reports the error.
    extractImports :: String -> String -> [String]
    extractImports moduleName content = case runParseModule moduleName content of
      Left _ -> []
      Right items ->
        [ locatedNameText (parsedImportModule decl) | ModuleImportItem decl <- items ]

main :: IO ()
main = do
  let opts = O.info (telomareOpts O.<**> O.helper)
        ( O.fullDesc
          <> O.progDesc "A simple but robust virtual machine" )
  topts <- O.execParser opts
  let file = telomareFile topts
      action = telomareAction topts
  if isArtifactPath file
    then runArtifact file action (telomareMode topts)
    else case telomareMode topts of
      Fast fuel -> runFast file action fuel
      mode      -> runSized (runtimeOf mode) file action

die :: String -> IO a
die message = hPutStrLn stderr message >> exitFailure

-- |Report a rendered meter on stderr, flushing the program's own output first
-- so the two never interleave.
reportMeter :: String -> IO ()
reportMeter rendered = do
  hFlush stdout
  hPutStr stderr rendered

-- |A program already compiled: nothing to parse, typecheck, resolve or size.
-- The runtime choice still applies, and costs nothing extra — the EAL
-- admission the IC runtime needs was decided at compile time and stored,
-- so `--ic` on an artifact is a field read, not an inference.
runArtifact :: FilePath -> Action -> Mode -> IO ()
runArtifact path action mode = do
  case mode of
    Fast _ ->
      hPutStrLn stderr "note: --fast does not apply to an already-compiled program"
    _sizedOrIC -> pure ()
  readArtifact path >>= \case
    Left err -> die $ path <> ": " <> err
    Right artifact -> do
      warnIfStale artifact
      let cp = CompiledProgram
            { cpSizing = artifactReport artifact
            , cpExpr = artifactExpr artifact
            , cpGuidance = artifactGuidance artifact
            , cpVerdict = artifactVerdict artifact
            }
      case action of
        Compile _   -> die $ path <> " is already compiled"
        Certificate -> putStr $ artifactCertificate artifact
        Run         -> runCompiled (runtimeOf mode) Run cp
        Meter       -> runCompiled (runtimeOf mode) Meter cp

-- |An artifact outlives the checkout it came from, so a hash mismatch is worth
-- saying and never worth refusing over.
warnIfStale :: Artifact -> IO ()
warnIfStale artifact = do
  let entry = artifactEntry artifact
  present <- doesFileExist (entry <> ".tel")
  when present $ do
    modules <- getModulesFor entry
    unless (sourcesHash modules == artifactSourceHash artifact) $
      hPutStrLn stderr
        "note: the sources have changed since this program was compiled; \
        \recompile it to pick the changes up"

-- |Gate a session on the carried verdict: a refusal is a user-facing
-- report, not a crash, and nothing runs on the net without admission.
withICPlan :: CompiledProgram -> (ICPlan -> IO a) -> IO a
withICPlan cp k = either die k (programPlan cp)

-- |Run (or run-and-meter) a compiled program on the chosen runtime; the
-- artifact and fresh-compile routes share this.
runCompiled :: Runtime -> Action -> CompiledProgram -> IO ()
runCompiled runtime action cp = case (action, runtime) of
  (Run, Reference) -> evalLoop (cpExpr cp)
  (Run, ICNet) -> withICPlan cp $ \plan -> void (evalLoopIC [] plan (cpExpr cp))
  (Meter, Reference) -> do
    measured <- evalLoopMetered [] (cpExpr cp)
    reportMeter $ renderMeter measured <> "\n"
  (Meter, ICNet) -> withICPlan cp $ \plan -> do
    measured <- evalLoopIC [] plan (cpExpr cp)
    reportMeter $ renderICMeter measured
  _notARun -> die "runCompiled: only Run and Meter reach here"

-- |The usual route. Sizing costs minutes on Prelude-heavy programs, so every
-- action here works from one compile.
runSized :: Runtime -> FilePath -> Action -> IO ()
runSized runtime file action = do
  let entryModule = takeBaseName file
  allModules <- getModulesFor entryModule
  case compileModules allModules entryModule of
    Left err -> die err
    Right cp -> case action of
      Run -> runCompiled runtime Run cp
      Certificate ->
        putStr $ staticReport Nothing (Just (cpSizing cp)) allModules entryModule
      Meter -> runCompiled runtime Meter cp
      Compile output -> do
        let path = fromMaybe (replaceExtension file telcExtension) output
            certificate =
              staticReport Nothing (Just (cpSizing cp)) allModules entryModule
            artifact = Artifact
              { artifactEntry = entryModule
              , artifactSourceHash = sourcesHash allModules
              , artifactReport = cpSizing cp
              , artifactCertificate = certificate
              , artifactExpr = cpExpr cp
              , artifactGuidance = cpGuidance cp
              , artifactVerdict = cpVerdict cp
              }
        writeArtifact path artifact
        hPutStrLn stderr $ "wrote " <> path
          <> " (" <> show (nodeCount (cpExpr cp))
          <> " nodes, sources " <> take 12 (sourcesHash allModules) <> ")"

-- |Without sizing. The program runs on demand under a fuel cap; no iteration
-- count exists, so the certificate reports structure only.
runFast :: FilePath -> Action -> Maybe Int -> IO ()
runFast file action fuel = do
  let entryModule = takeBaseName file
  allModules <- getModulesFor entryModule
  case action of
    Compile _ -> die "--compile sizes the program, so it cannot be combined with --fast"
    Certificate -> putStr $ staticReport Nothing Nothing allModules entryModule
    _ -> case compileFast allModules entryModule of
      Left err -> die err
      Right prog -> do
        measured <- runFastLoop fuel prog
        when (action == Meter) . reportMeter $ renderFastMeter measured

staticReport :: Maybe String -> Maybe SizingReport -> [(String, String)] -> String -> String
staticReport hash sizing allModules entryModule =
  renderStaticReport hash sizing (levelsInfo allModules entryModule)
