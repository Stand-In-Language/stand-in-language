{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import qualified Options.Applicative as O
import System.Directory (listDirectory)
import System.FilePath (takeBaseName, takeExtension)
import qualified System.IO.Strict as Strict
import Telomare.Eval (runMain)

newtype TelomareOpts
  = TelomareOpts {telomareFile :: String}
  deriving Show

telomareOpts :: O.Parser TelomareOpts
telomareOpts = TelomareOpts
  <$> O.argument O.str (O.metavar "TELOMARE-FILE")

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
  runMain allModules . takeBaseName . telomareFile $ topts
