module Main where

import ConformanceTests
import RunModeTests
import SizingTests
import Test.Hspec

main :: IO ()
main = hspec $ do
  sizingSpec
  runModeSpec
  conformanceSpec
