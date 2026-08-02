{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.Monad (unless, when)
import Data.Maybe (fromMaybe, mapMaybe)
import qualified Options.Applicative as O
import System.Directory (doesFileExist)
import System.Exit (exitFailure)
import System.FilePath (replaceExtension, takeBaseName)
import System.IO (hFlush, hPutStr, hPutStrLn, stderr, stdout)

import Telomare.Artifact (Artifact (..), isArtifactPath, nodeCount,
                          readArtifact, sourcesHash, telcExtension,
                          writeArtifact)
import Telomare.Certificate (renderStaticReport)
import Telomare.Eval (compileModules, evalLoop, evalLoopMetered)
import Telomare.Fast (compileFast, defaultFastFuel, renderFastMeter,
                      runFastLoop)
import Telomare.Levels (levelsInfo)
import Telomare.Meter (renderMeter)
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
  deriving (Eq, Show)

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
          let imports = extractImports content
          go (queue <> imports) ((m, content) : loaded)

    extractImports :: String -> [String]
    extractImports = mapMaybe parseImportLine . lines

    parseImportLine :: String -> Maybe String
    parseImportLine line = case words line of
      ("import":"qualified":name:_) -> Just name
      ("import":name:_)             -> Just name
      _                             -> Nothing

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
      Sized     -> runSized file action

die :: String -> IO a
die message = hPutStrLn stderr message >> exitFailure

-- |A program already compiled: nothing to parse, typecheck, resolve or size.
runArtifact :: FilePath -> Action -> Mode -> IO ()
runArtifact path action mode = do
  when (mode /= Sized) $
    hPutStrLn stderr "note: --fast does not apply to an already-compiled program"
  readArtifact path >>= \case
    Left err -> die $ path <> ": " <> err
    Right artifact -> do
      warnIfStale artifact
      case action of
        Compile _   -> die $ path <> " is already compiled"
        Certificate -> putStr $ artifactCertificate artifact
        Run         -> evalLoop (artifactExpr artifact)
        Meter       -> do
          measured <- evalLoopMetered [] (artifactExpr artifact)
          hFlush stdout
          hPutStr stderr $ renderMeter measured <> "\n"

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

-- |The usual route. Sizing costs minutes on Prelude-heavy programs, so every
-- action here works from one compile.
runSized :: FilePath -> Action -> IO ()
runSized file action = do
  let entryModule = takeBaseName file
  allModules <- getModulesFor entryModule
  case compileModules allModules entryModule of
    Left err -> die err
    Right (report, sized) -> case action of
      Run -> evalLoop sized
      Certificate -> putStr $ staticReport Nothing (Just report) allModules entryModule
      Meter -> do
        measured <- evalLoopMetered [] sized
        hFlush stdout
        hPutStr stderr $ renderMeter measured <> "\n"
      Compile output -> do
        let path = fromMaybe (replaceExtension file telcExtension) output
            certificate = staticReport Nothing (Just report) allModules entryModule
            artifact = Artifact
              { artifactEntry = entryModule
              , artifactSourceHash = sourcesHash allModules
              , artifactReport = report
              , artifactCertificate = certificate
              , artifactExpr = sized
              }
        writeArtifact path artifact
        hPutStrLn stderr $ "wrote " <> path <> " (" <> show (nodeCount sized)
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
        when (action == Meter) $ do
          hFlush stdout
          hPutStr stderr $ renderFastMeter measured

staticReport :: Maybe String -> Maybe SizingReport -> [(String, String)] -> String -> String
staticReport hash sizing allModules entryModule =
  renderStaticReport hash sizing (levelsInfo allModules entryModule)
