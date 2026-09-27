-- | Projection-path usage of one environment frame, independent of the IR.
-- Paths descend the value from the innermost projection outwards. Children
-- start fresh paths; transparent nodes retain them; closed nodes contribute
-- nothing. Merging sums counts and keeps the first occurrence's annotation.
-- Disjoint paths are linear. Repeated paths, or a path used alongside one
-- of its strict extensions, require contraction.
module Telomare.EnvUsage (UsageView (..), usage, envPath, contraction) where

import Data.List (find, isPrefixOf)
import Data.Map (Map)
import qualified Data.Map as Map

data UsageView step loc a
  = Occurrence loc
  | Projection step a
  | Transparent a
  | Children [a]
  | Closed

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
    _                     -> Nothing

contraction :: Ord step => Map [step] (Int, loc) -> Maybe ([step], loc)
contraction uses = (\(path, (_, loc)) -> (path, loc))
  <$> find duplicated (Map.toList uses)
  where
    duplicated (path, (count, _)) = count >= 2 ||
      (count >= 1 && any (\other -> path /= other && path `isPrefixOf` other)
        (Map.keys uses))
