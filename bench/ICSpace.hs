{-# LANGUAGE PatternSynonyms #-}
module Main where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import System.CPUTime (getCPUTime)
import System.Environment (getArgs)
import System.FilePath (takeBaseName)
import System.IO (BufferMode (LineBuffering), hSetBuffering, stdout)
import Telomare.Driver (CompileOutput (..), compileModules, evalLoopIC,
                        keepAccum, runMainWithInput)
import Telomare.EAL (ealCaptureLayouts)
import Telomare.IC
import Telomare.IC.Space
import Telomare.IR.Base (pattern EnvB)
import Telomare.Machine (appB)
import Text.Printf (printf)

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  args <- getArgs
  forM_ (if null args then ["simpleplus.tel", "tc_ultra_minimal.tel", "tictactoe.tel"] else args) $ \path -> do
    source <- readFile path
    prelude <- readFile "Prelude.tel"
    let name = takeBaseName path
        modules = [(name, source), ("Prelude", prelude)]
        inputs = case name of
          "simpleplus" -> ["3 4"]
          "tictactoe"  -> ["1", "4", "2", "5", "3"]
          _            -> []
    putStrLn ("Program: " <> path)
    start <- getCPUTime
    case compileModules modules name of
      Left err -> putStrLn ("Compilation failed: " <> err)
      Right out -> case prepareIC (ealCaptureLayouts (compileEAL out))
                        (appB (compileExpr out) EnvB) of
        Left err -> print err
        Right prog -> do
          _ <- evaluate (resourceAgents (staticStorage prog))
          prepared <- getCPUTime
          putStrLn ("Static: " <> show (staticStorage prog))
          let outcome = analyzeIC defaultAnalysisBudget prog
          _ <- evaluate (length (renderICSpace outcome))
          analyzed <- getCPUTime
          putStr (renderICSpace outcome)
          (stats, actual) <- evalLoopIC prog inputs keepAccum
          _ <- evaluate (length actual)
          executed <- getCPUTime
          expected <- runMainWithInput inputs modules name
          putStrLn ("Transcript equality: " <> show (actual == expected))
          putStrLn actual
          print stats
          printf "CPU seconds: prepare %.3f; analyze %.3f; execute %.3f\n"
            (seconds (prepared-start)) (seconds (analyzed-prepared)) (seconds (executed-analyzed))
  where
    seconds :: Integer -> Double
    seconds x = fromIntegral x / 1e12
