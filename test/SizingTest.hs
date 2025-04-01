module Main where

import Test.Hspec
import SizingTests

main :: IO ()
main = hspec $ do
  createMinimalSizingTest