-- | Construction of the shared approximant step, independent of the runtime.
module Telomare.IR.Recursion (approximantStep) where

-- | Meaning: @step recur input = if test input then recursive recur input
-- else base input@. Slots 0..4 are input, recur, test, recursive, base in
-- @(input, (recur, (test, (recursive, (base, 0)))))@.
-- The caller supplies application, conditional construction, and slot access.
-- This shares syntax only: evaluation demand and bounded-chain construction
-- remain the caller's responsibility.
approximantStep :: (a -> a -> a) -> (a -> a -> a -> a) -> (Int -> a) -> a
approximantStep app choose slot = choose (app (slot 2) input)
  (app (app (slot 3) (slot 1)) input)
  (app (slot 4) input)
  where input = slot 0
