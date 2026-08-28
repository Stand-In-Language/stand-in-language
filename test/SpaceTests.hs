{-# LANGUAGE LambdaCase #-}

-- |Hand-computed live-heap peaks, on terms small enough to trace against the
-- machine by hand. Each figure here was derived on paper from the sweep
-- discipline in `Telomare.Eval.Space` before it was asserted; a change that
-- moves one of them is a change to what "live" means and deserves the same
-- scrutiny as a changed step count.
module SpaceTests where

import Control.Monad (unless)
import Data.Char (ord)
import Data.Functor.Foldable (cata, project)
import qualified Data.Map as Map
import Numeric.Natural (Natural)
import Test.Hspec

import ConformanceTests (corpus)
import SizingTests (loadWith)

import Telomare.Driver (compileModules)
import Telomare.Eval.Space (SpaceMeter (..), SweepPolicy (..), evalSpace)
import Telomare.IR.Base
import Telomare.IR.Core (CompiledExpr)
import Telomare.Machine (appB, deferB)
import Telomare.Size (SizingReport (..))
import Telomare.SpaceBound

measure :: SweepPolicy -> CompiledExpr -> SpaceMeter
measure policy = fst . evalSpace policy

-- |A unary number as data: 2n+1 cells.
unary :: Int -> CompiledExpr
unary 0 = ZeroB
unary n = PairB (unary (n - 1)) ZeroB

spaceSpec :: Spec
spaceSpec = describe "the live-heap peak" $ do
  it "counts a literal pair as its three cells" $ do
    let m = measure SweepEveryAlloc (PairB ZeroB ZeroB)
    spPeakLower m `shouldBe` 3
    spPeakUpper m `shouldBe` 3
    spSteps m `shouldBe` 3
    spBuilt m `shouldBe` 1

  it "counts a shared environment once, not once per reference" $ do
    -- \x -> (x, x) applied to a three-cell pair. A tree count of the result
    -- reads 7 nodes; the run's peak is 5 cells (the argument pair, its two
    -- zeros, the function cell, and the application pair), because both
    -- references resolve to the argument's one allocation.
    let f = deferB (toEnum 1) (PairB EnvB EnvB)
        arg = PairB ZeroB ZeroB
        m = measure SweepEveryAlloc (SetEnvB (PairB f arg))
    spPeakLower m `shouldBe` 5
    spPeakUpper m `shouldBe` 5

  it "sees a transient the result does not keep" $ do
    -- @right (n, 0)@ returns a single cell, but the run held the number
    -- while the projection waited: its 2n+1 cells, the zero, and the pair.
    -- The peak growing with n is what a size-of-the-result figure — or a
    -- retention-blind cost algebra — would have missed.
    let transientPeak n =
          spPeakLower (measure SweepEveryAlloc (RightB (PairB (unary n) ZeroB)))
    transientPeak 10 `shouldBe` 2 * 10 + 3
    transientPeak 200 - transientPeak 100 `shouldBe` 200

  it "the adaptive sweep brackets the exact peak" $ do
    let expr = RightB (PairB (unary 5000) ZeroB)
        exact = measure SweepEveryAlloc expr
        adaptive = measure SweepAdaptive expr
    -- Same run, different measuring cadence.
    spSteps adaptive `shouldBe` spSteps exact
    spBuilt adaptive `shouldBe` spBuilt exact
    spPeakLower adaptive `shouldSatisfy` (> 0)
    spPeakLower adaptive `shouldSatisfy` (<= spPeakLower exact)
    spPeakUpper adaptive `shouldSatisfy` (>= spPeakUpper exact)

boundSpec :: Spec
boundSpec = describe "the bound language" $ do
  it "adds cell counts and keeps the worse alternative" $ do
    let a = sbAdd (sbConst 3) (sbScale 2 (sbInput 0))
    renderSpaceBound a `shouldBe` "2·|input| + 3 cells"
    renderSpaceBound (sbMax a (sbConst 100)) `shouldBe`
      "max(100, 2·|input| + 3) cells"

  it "prunes an affine another one dominates" $ do
    -- 2·|input| + 3 stands above |input| + 1 everywhere, so the maximum
    -- forgets the smaller one.
    let big = sbAdd (sbScale 2 (sbInput 0)) (sbConst 3)
        small = sbAdd (sbInput 0) (sbConst 1)
    sbMax big small `shouldBe` big
    -- Incomparable affines both stay.
    let other = sbAdd (sbScale 3 (sbInput 1)) (sbConst 1)
    sbMax big other `shouldSatisfy` \b ->
      b /= big && b /= other && b == sbMax other big

  it "substitutes known input sizes and goes concrete" $ do
    let b = sbAdd (sbScale 3 (sbInput 1)) (sbConst 12)
    sbConcrete b `shouldBe` Nothing
    sbConcrete (sbSubstitute (Map.singleton 1 5) b) `shouldBe` Just 27

  it "widening stands above everything it replaced" $ do
    -- Widen a maximum of incomparable affines to width 1, then check the
    -- widened bound is at least each original at sample input sizes.
    let affs = [ sbAdd (sbScale c (sbInput p)) (sbConst k)
               | (c, p, k) <- [(2, 0, 3), (1, 1, 9), (5, 2, 0)] ]
        combined = foldr1 sbMax affs
        widened = sbWiden 1 combined
        sizes = Map.fromList [(0, 4), (1, 7), (2, 1)]
        at b = sbConcrete (sbSubstitute sizes b)
    at widened `shouldSatisfy` \w -> all (\a -> at a <= w) affs

  it "checks a measured figure against the bound" $ do
    let b = sbAdd (sbInput 0) (sbConst 2)
        sizes = Map.singleton 0 10
    sbAtLeast 12 sizes b `shouldBe` True
    sbAtLeast 13 sizes b `shouldBe` False
    -- The bound that says nothing bounds everything.
    sbAtLeast 1000000 sizes sbTop `shouldBe` True
    -- A bound still symbolic after substitution verifies nothing.
    sbAtLeast 0 Map.empty b `shouldBe` False

  it "renders paths as the words a reader would use" $ do
    renderSpaceBound (sbInput 0) `shouldBe` "|input| cells"
    renderSpaceBound (sbInput 5) `shouldBe` "|input.right.left| cells"
    renderSpaceBound sbTop `shouldBe` "unknown"

-- |The headline invariant: on every corpus program, the static bound with
-- the actual input sizes substituted stands at or above the exactly measured
-- live-heap peak. This is the empirical check of the simulation between the
-- abstract and the concrete machine.
--
-- The bound covers refinement-valid runs: the abstract input is shaped by
-- the same refinement-derived restrictions the sizing pass uses, so a run
-- whose input fails a check — which constructs and retains the aborted
-- message — is outside it. Such iterations are detected by `spAborts` and
-- not compared; at least one abort-free iteration must remain, or the test
-- would be vacuous.
staticVsMeasuredSpec :: Spec
staticVsMeasuredSpec = describe "the static bound stands above the measured peak" $
  mapM_ checkOn corpus

checkOn :: (FilePath, String, [String]) -> Spec
checkOn (path, name, inputs) = it name $ do
  modules <- loadWith path name
  case compileModules modules name of
    Left err -> expectationFailure $ "failed to compile:\n" <> err
    Right (report, sized) -> case sizingReportSpace report of
      Left why -> expectationFailure $ "no static bound: " <> why
      Right bound -> do
        checked <- loop sized bound ZeroB inputs 0
        checked `shouldSatisfy` (> 0)
  where
    loop :: CompiledExpr -> SpaceBound -> CompiledExpr -> [String] -> Int -> IO Int
    loop sized bound st inps checked = do
      let applied = appB sized st
          (m, r) = evalSpace SweepEveryAlloc applied
          sizes = Map.fromList [ (p, sizeAtPath st p) | p <- sbPaths bound ]
          validRun = spAborts m == 0
      unless (not validRun || sbAtLeast (spPeakUpper m) sizes bound)
        . expectationFailure $
          "measured " <> show (spPeakUpper m) <> " cells, bound only "
            <> renderSpaceBound (sbSubstitute sizes bound)
      let checked' = checked + fromEnum validRun
      case r of
        Left _ -> pure checked' -- an abort ended the session
        Right v -> case project v of
          BasicFW (PairSF _ newState) -> case (project newState, inps) of
            (BasicFW ZeroSF, _) -> pure checked'
            (_, [])             -> pure checked'
            (_, i : rest) -> loop sized bound (PairB (str2b i) newState) rest checked'
          _ -> expectationFailure "unexpected iteration result" >> pure checked'

-- |The input as the driver builds it, at the compiled type.
str2b :: String -> CompiledExpr
str2b = foldr (PairB . unary . ord) ZeroB

-- |Directions from the root, decoded from a path index.
pathSteps :: Integer -> [Bool]
pathSteps = go [] where
  go acc 0 = acc
  go acc p
    | odd p = go (True : acc) ((p - 1) `div` 2)
    | otherwise = go (False : acc) ((p - 2) `div` 2)

-- |How many cells the input part at a path holds. Projecting past a zero
-- stays zero, as the machine's projections do.
sizeAtPath :: CompiledExpr -> Integer -> Natural
sizeAtPath v p = cells (walk v (pathSteps p)) where
  walk :: CompiledExpr -> [Bool] -> CompiledExpr
  walk x [] = x
  walk x (s : rest) = case project x of
    BasicFW (PairSF a b) -> walk (if s then a else b) rest
    _                    -> x
  cells :: CompiledExpr -> Natural
  cells = cata $ \case
    BasicFW ZeroSF       -> 1
    BasicFW (PairSF a b) -> 1 + a + b
    _                    -> 1
