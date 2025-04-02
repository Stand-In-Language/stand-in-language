{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import qualified Options.Applicative as O
import qualified System.IO.Strict as Strict
import Telomare.Eval (runMain)
import System.Directory (listDirectory)
import System.FilePath (takeBaseName, takeExtension)

data TelomareOpts = TelomareOpts
  { telomareFile :: String
  -- , preludeFile  :: String
  } deriving Show

telomareOpts :: O.Parser TelomareOpts
telomareOpts = TelomareOpts
  <$> O.argument O.str (O.metavar "TELOMARE-FILE")
  -- <*> O.strOption
  --     ( O.long "prelude"
  --       <> O.metavar "PRELUDE-FILE"
  --       <> O.showDefault
  --       <> O.value "./Prelude.tel"
  --       <> O.short 'p'
  --       <> O.help "Telomare prelude file" )

getAllModules :: IO [(String, String)]
getAllModules = do
  allEntries <- listDirectory "."
  let telFiles = filter (\f -> takeExtension f == ".tel") allEntries
      readTelFile :: FilePath -> IO (String, String)
      readTelFile file = do
          content <- readFile file
          return (takeBaseName file, content)
  mapM readTelFile telFiles

main :: IO ()
main = do
  let opts = O.info (telomareOpts O.<**> O.helper)
        ( O.fullDesc
          <> O.progDesc "A simple but robust virtual machine" )
  topts <- O.execParser opts
  allModules :: [(String, String)] <- getAllModules
  -- putStrLn . show $ fst <$> allModules
  runMain allModules . takeBaseName . telomareFile $ topts
