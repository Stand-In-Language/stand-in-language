-- |Indentation helpers shared by the IR Show instances and the
-- 'Telomare.PrettyPrint' pretty-printer. A leaf module: everything above it
-- in the compiler may use these without pulling in any IR.
module Telomare.PrettyPrint.Indent where

import Control.Monad.State (State)
import qualified Control.Monad.State as State

-- |Helper function to indent. Usefull for indented Show instances.
indent :: Int -> String -> String
indent i str = replicate i ' ' <> str

indentWithOneChild' :: String -> State Int String -> State Int String
indentWithOneChild' str sx = do
  i <- State.get
  let sout = str <> " "
  State.put $ i + length sout
  x <- sx
  pure $ sout <> x

indentWithTwoChildren' :: String -> State Int String -> State Int String -> State Int String
indentWithTwoChildren' str sl sr = do
  i <- State.get
  let sout = str <> " "
      newl = i + length sout
  State.put newl
  l <- sl
  State.put newl
  r <- sr
  pure $ sout <> l <> "\n" <> indent newl r

indentWithChildren' :: String -> [State Int String] -> State Int String
indentWithChildren' str l = do
  i <- State.get
  let sout = str <> " "
      newl = i + length sout
  let doLine = fmap (<> "\n" <> indent newl "") . (State.put newl >>)
  foldl (\s c -> (<>) <$> s <*> c) (pure sout) $ fmap doLine l

indentation :: Int -> String
indentation 0 = []
indentation n = ' ' : ' ' : indentation (n - 1)

indentSansFirstLine :: Int -> String -> String
indentSansFirstLine i x = removeLastNewLine res where
  res = unlines $ indentTail (lines x)
  indentTail (s:ns) = s:((indentation i <>) <$> ns)
  indentTail []     = error "Telomare.PrettyPrint.Indent.indentSansFirstLine: unexpected empty list of lines"
  removeLastNewLine str =
    case reverse str of
      '\n' : rest -> reverse rest
      _           -> str
