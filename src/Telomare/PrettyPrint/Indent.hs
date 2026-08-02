-- |Indentation helpers shared by the IR Show instances and the
-- 'Telomare.PrettyPrint' pretty-printer. A leaf module: everything above it
-- in the compiler may use these without pulling in any IR.
module Telomare.PrettyPrint.Indent where

import Control.Monad.State (State)
import qualified Control.Monad.State as State

-- |Helper function to indent. Usefull for indented Show instances.
indent :: Int -> String -> String
indent i str = replicate i ' ' <> str

-- |Indentation with the State Monad.
sindent :: String -> State Int String
sindent str = State.get >>= (\i -> pure $ indent i str)

-- |One child indentation.
indentWithOneChild :: String -> State Int String -> State Int String
indentWithOneChild str sx = do
  i <- State.get
  State.put $ i + 2
  x <- sx
  pure $ indent i (str <> "\n") <> x

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

-- TODO replace with above version
-- |Two children indentation.
indentWithTwoChildren :: String -> State Int String -> State Int String -> State Int String
indentWithTwoChildren str sl sr = do
  i <- State.get
  State.put $ i + 2
  l <- sl
  State.put $ i + 2
  r <- sr
  pure $ indent i (str <> "\n") <> l <> "\n" <> r

-- TODO replace with other version
indentWithThreeChildren :: String -> State Int String -> State Int String -> State Int String -> State Int String
indentWithThreeChildren str sa sb sc = do
  i <- State.get
  State.put $ i + 2
  a <- sa
  State.put $ i + 2
  b <- sb
  State.put $ i + 2
  c <- sc
  pure $ indent i (str <> "\n") <> a <> "\n" <> b <> "\n" <> c

-- |`dropUntil p xs` drops leading elements until `p $ head xs` is satisfied.
dropUntil :: (a -> Bool) -> [a] -> [a]
dropUntil _ [] = []
dropUntil p x@(x1:_) =
  if p x1 then x else dropUntil p (drop 1 x)

indentation :: Int -> String
indentation 0 = []
indentation n = ' ' : ' ' : indentation (n - 1)

indentSansFirstLine :: Int -> String -> String
indentSansFirstLine i x = removeLastNewLine res where
  res = unlines $ (\(s:ns) -> s:((indentation i <>) <$> ns)) (lines x)
  removeLastNewLine str =
    case reverse str of
      '\n' : rest -> reverse rest
      x           -> str
