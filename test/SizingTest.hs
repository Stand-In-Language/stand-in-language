module Main where

import ConformanceTests
import RunModeTests
import SizingTests
import SpaceTests
import Test.Hspec

main :: IO ()
main = hspec $ do
  sizingSpec
  runModeSpec
  conformanceSpec
  spaceSpec
  boundSpec
  staticVsMeasuredSpec
