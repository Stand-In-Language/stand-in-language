module Main where

import RunModeTests
import SizingTests
import Test.Hspec

main :: IO ()
main = hspec $ do
  twoFailedApproaches
  runModeSpec
