module Main where

import SizingTests
import Test.Hspec

main :: IO ()
main = hspec $ do
  twoFailedApproaches
