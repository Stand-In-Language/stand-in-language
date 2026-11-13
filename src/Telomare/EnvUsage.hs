-- | Projection-path usage of one environment frame, independent of the IR.
-- Paths descend the value from the innermost projection outwards. Children
-- start fresh paths; transparent nodes retain them; closed nodes contribute
-- nothing. Merging sums counts and keeps the first occurrence's annotation.
-- Disjoint paths are linear. Repeated paths, or a path used alongside one
-- of its strict extensions, require contraction.
module Telomare.EnvUsage (UsageView (..), usage, envPath, contractions) where

import Data.List (isPrefixOf)
import Data.Map (Map)
import qualified Data.Map as Map

-- | What one node of a term means for the usage of the current env frame.
data UsageView step loc a
  = Occurrence loc       -- ^ the env itself
  | Projection step a    -- ^ a projection applied to the term below
  | Transparent a        -- ^ a wrapper the path passes through unchanged
  | Children [a]         -- ^ anything else that uses the frame
  | Closed               -- ^ a value with no use of this frame

usage :: Ord step => (a -> UsageView step loc a) -> a -> Map [step] (Int, loc)
usage view = go [] where
  go path term = case view term of
    Occurrence loc        -> Map.singleton path (1, loc)
    Projection step child -> go (step : path) child
    Transparent child     -> go path child
    Children children     -> foldr (merge . go []) Map.empty children
    Closed                -> Map.empty
  merge = Map.unionWith (\(n, loc) (m, _) -> (n + m, loc))

-- | Recognize exactly the chains counted as a single occurrence by 'usage'.
envPath :: (a -> UsageView step loc a) -> a -> Maybe [step]
envPath view = go [] where
  go path term = case view term of
    Occurrence _          -> Just path
    Projection step child -> go (step : path) child
    Transparent child     -> go path child
    _notAnOccurrence      -> Nothing

-- | Every path consumed more than once: two direct uses, or a direct use
-- plus a use of one of its strict extensions.
contractions :: Ord step => Map [step] (Int, loc) -> [([step], loc)]
contractions uses =
  [ (path, loc) | (path, (count, loc)) <- Map.toList uses, duplicated path count ]
  where
    duplicated path count = count >= 2 ||
      (count >= 1 && any (\other -> path /= other && path `isPrefixOf` other)
        (Map.keys uses))
