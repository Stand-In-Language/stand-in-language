{-# LANGUAGE PatternSynonyms #-}

-- Compile only: no reduction or readback. Run with a depth and repeat count.
module Main where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import Control.Monad.Except (runExceptT)
import Control.Monad.State.Strict (runState)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map as Map
import System.CPUTime (getCPUTime)
import System.Environment (getArgs)
import Telomare.IC
import Telomare.IR.Base (pattern PairB, pattern ZeroB)
import Telomare.IR.Core (CompiledExpr)
import Telomare.Machine (deferB)
import Text.Printf (printf)

chain :: Int -> Int -> CompiledExpr
chain seed depth = foldr (\i t -> deferB (seed + i) (PairB ZeroB t))
  ZeroB [1 .. depth]

main :: IO ()
main = do
  [depthArg, repeatsArg] <- getArgs
  let depth = read depthArg
      repeats = read repeatsArg
  start <- getCPUTime
  forM_ [1 .. repeats] $ \seed -> do
    let (result, st) = runState (runExceptT (compileTerm (chain seed depth)))
          (emptyState Map.empty defaultFuel)
    case result of
      Left err -> fail (show err)
      Right _ -> do
        count <- evaluate (IntMap.size (icTemplates st))
        if count == depth then pure () else fail "unexpected template count"
  end <- getCPUTime
  printf "depth=%d repeats=%d cpu_ms=%.3f\n" depth repeats
    (fromIntegral (end - start) / 1e9 :: Double)
