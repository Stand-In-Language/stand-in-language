{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Data.Maybe (mapMaybe)
import qualified Options.Applicative as O
import System.FilePath (takeBaseName)
import Telomare.Eval (runMain)

newtype TelomareOpts
  = TelomareOpts {telomareFile :: String}
  deriving Show

telomareOpts :: O.Parser TelomareOpts
telomareOpts = TelomareOpts
  <$> O.argument O.str (O.metavar "TELOMARE-FILE")

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
  let entryModule = takeBaseName (telomareFile topts)
  allModules <- getModulesFor entryModule
  runMain allModules entryModule
