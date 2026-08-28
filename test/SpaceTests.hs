-- |Hand-computed live-heap peaks, on terms small enough to trace against the
-- machine by hand. Each figure here was derived on paper from the sweep
-- discipline in `Telomare.Eval.Space` before it was asserted; a change that
-- moves one of them is a change to what "live" means and deserves the same
-- scrutiny as a changed step count.
module SpaceTests where

import Test.Hspec

import Telomare.Eval.Space (SpaceMeter (..), SweepPolicy (..), evalSpace)
import Telomare.IR.Base
import Telomare.IR.Core (CompiledExpr)
import Telomare.Machine (deferB)

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
