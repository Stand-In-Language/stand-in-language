{-# LANGUAGE LambdaCase #-}

-- |The language a static space bound is stated in: a maximum over affine
-- expressions in input sizes, measured in cells (see `Telomare.Eval.Space`
-- for the cell). @3·|input.left| + 12@ is one affine; a program whose peak
-- depends on which branch runs gets the maximum of several.
--
-- The variables are input /paths/, indexed the way the sizing pass indexes
-- its symbolic input (`Telomare.Size.IR.IndexedInputF`): the whole input is
-- path 0, and a node at path n has its left part at 2n+1 and its right part
-- at 2n+2. @|p|@ stands for the size in cells of the input part at path p.
--
-- Everything here is an upper bound, so the operations are free to lose
-- precision but never to lose soundness: pruning only drops affines another
-- affine dominates pointwise, and widening replaces a set of affines with
-- their pointwise maximum, which bounds each of them. The one non-value is
-- `sbTop`, the bound that says nothing; it arises from widening or fuel
-- exhaustion in the static pass, never from a program being input-dependent —
-- input dependence stays symbolic.
module Telomare.SpaceBound where

import Data.List (intercalate, sort)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Numeric.Natural (Natural)

-- |One affine expression: Σ coeff_p · |p| + constant.
data Affine = Affine
  { affCoeffs :: Map Integer Natural
  -- ^Per-path coefficients; a path absent here has coefficient zero.
  , affConst  :: Natural
  }
  deriving (Eq, Ord, Show)

-- |A bound: the maximum of some affines, or `sbTop` when nothing is known.
-- The list is kept free of dominated entries and never empty.
newtype SpaceBound = SpaceBound (Maybe [Affine])
  deriving (Eq, Show)

-- |A known figure.
sbConst :: Natural -> SpaceBound
sbConst k = SpaceBound (Just [Affine Map.empty k])

-- |The size of the input part at a path.
sbInput :: Integer -> SpaceBound
sbInput p = SpaceBound (Just [Affine (Map.singleton p 1) 0])

-- |The bound that says nothing.
sbTop :: SpaceBound
sbTop = SpaceBound Nothing

-- |Force a bound all the way down. The static walk accumulates bounds over
-- millions of transitions; left lazy, each accumulation is a thunk retaining
-- the machine state it was made from, and the walk's memory grows with its
-- history instead of its live set.
sbForce :: SpaceBound -> SpaceBound
sbForce b@(SpaceBound Nothing)   = b
sbForce b@(SpaceBound (Just as)) = foldr forceAff b as
  where forceAff (Affine cs k) r = Map.foldr' seq (k `seq` r) cs

-- |Whether the second affine is everywhere at least the first.
dominates :: Affine -> Affine -> Bool
dominates (Affine cs k) (Affine cs' k') =
  k <= k' && Map.isSubmapOfBy (<=) cs cs'

-- |Drop every affine another one dominates. Ties keep one copy.
prune :: [Affine] -> [Affine]
prune xs = go xs [] where
  go [] kept = reverse kept
  go (a : rest) kept
    | any (dominates a) rest || any (dominates a) kept = go rest kept
    | otherwise = go rest (a : kept)

-- |How many affines a bound may hold before it is widened. Past this, the
-- pointwise maximum stands in for all of them — looser, still sound.
defaultWidth :: Int
defaultWidth = 16

-- |Collapse to the pointwise maximum once the affine set outgrows the cap.
sbWiden :: Int -> SpaceBound -> SpaceBound
sbWiden _ (SpaceBound Nothing) = sbTop
sbWiden cap b@(SpaceBound (Just affs))
  | length affs <= cap = b
  | otherwise = SpaceBound (Just [foldr1 pointwiseMax affs])
  where
    pointwiseMax (Affine cs k) (Affine cs' k') =
      Affine (Map.unionWith max cs cs') (max k k')

-- |Sorted so that equal bounds compare equal however they were put together.
norm :: [Affine] -> SpaceBound
norm = sbWiden defaultWidth . SpaceBound . Just . sort . prune

-- |Both at once: cells held by co-live values sum.
sbAdd :: SpaceBound -> SpaceBound -> SpaceBound
sbAdd (SpaceBound (Just as)) (SpaceBound (Just bs)) =
  norm [ Affine (Map.unionWith (+) cs cs') (k + k')
       | Affine cs k <- as, Affine cs' k' <- bs ]
sbAdd _ _ = sbTop

-- |Either alone: peaks of alternative runs take the worse one.
sbMax :: SpaceBound -> SpaceBound -> SpaceBound
sbMax (SpaceBound (Just as)) (SpaceBound (Just bs)) = norm (as <> bs)
sbMax _ _                                           = sbTop

-- |A bound taken a concrete number of times over.
sbScale :: Natural -> SpaceBound -> SpaceBound
sbScale _ (SpaceBound Nothing) = sbTop
sbScale n (SpaceBound (Just affs)) =
  norm [ Affine (fmap (n *) cs) (n * k) | Affine cs k <- affs ]

-- |Cells held together sum; the empty sum holds nothing.
instance Semigroup SpaceBound where
  (<>) = sbAdd

instance Monoid SpaceBound where
  mempty = sbConst 0

-- |Replace the paths whose sizes are known — refinement-pinned inputs, or a
-- test harness's actual input — by those sizes.
sbSubstitute :: Map Integer Natural -> SpaceBound -> SpaceBound
sbSubstitute _ (SpaceBound Nothing) = sbTop
sbSubstitute sizes (SpaceBound (Just affs)) = norm (fmap subst affs) where
  subst (Affine cs k) =
    let (known, unknown) = Map.partitionWithKey (\p _ -> Map.member p sizes) cs
        pinned = sum [ c * (sizes Map.! p) | (p, c) <- Map.toList known ]
    in Affine unknown (k + pinned)

-- |The figure, when no input size remains in it.
sbConcrete :: SpaceBound -> Maybe Natural
sbConcrete (SpaceBound Nothing) = Nothing
sbConcrete (SpaceBound (Just affs))
  | all (Map.null . affCoeffs) affs = Just (maximum (fmap affConst affs))
  | otherwise = Nothing

-- |Whether the bound, at the given input sizes, stands at or above a
-- measured figure. `sbTop` bounds everything; a bound still symbolic after
-- substitution verifies nothing.
sbAtLeast :: Natural -> Map Integer Natural -> SpaceBound -> Bool
sbAtLeast measured sizes bound = case sbSubstitute sizes bound of
  SpaceBound Nothing -> True
  b                  -> maybe False (>= measured) (sbConcrete b)

-- |Every input path the bound mentions; what a harness must size to check it.
sbPaths :: SpaceBound -> [Integer]
sbPaths (SpaceBound Nothing)     = []
sbPaths (SpaceBound (Just affs)) = Set.toList (foldMap (Map.keysSet . affCoeffs) affs)

-- |A path as the words a reader would use: @input@, @input.left.right@, …
renderPath :: Integer -> String
renderPath = intercalate "." . ("input" :) . go [] where
  go acc 0 = acc
  go acc p
    | odd p = go ("left" : acc) ((p - 1) `div` 2)
    | otherwise = go ("right" : acc) ((p - 2) `div` 2)

renderAffine :: Affine -> String
renderAffine (Affine cs k) = case terms of
  [] -> show k
  _  -> intercalate " + " (terms <> [show k | k /= 0])
  where
    terms = [ coeff c <> "|" <> renderPath p <> "|" | (p, c) <- Map.toAscList cs ]
    coeff 1 = ""
    coeff c = show c <> "·"

-- |What to print for a bound.
renderSpaceBound :: SpaceBound -> String
renderSpaceBound = \case
  SpaceBound Nothing -> "unknown"
  SpaceBound (Just [a]) -> renderAffine a <> " cells"
  SpaceBound (Just affs) ->
    "max(" <> intercalate ", " (fmap renderAffine affs) <> ") cells"

-- |`renderSpaceBound` for a report line: an affine over many input parts is
-- summarized rather than spelled out, deepest path and all.
renderSpaceBoundBrief :: SpaceBound -> String
renderSpaceBoundBrief = \case
  SpaceBound Nothing -> "unknown"
  SpaceBound (Just [a]) -> brief a <> " cells"
  SpaceBound (Just affs) ->
    "max(" <> intercalate ", " (fmap brief affs) <> ") cells"
  where
    brief a@(Affine cs k)
      | Map.size cs <= 4 = renderAffine a
      | otherwise =
          "sizes of " <> show (Map.size cs) <> " input parts ("
            <> show (sum (Map.elems cs)) <> " weighted) + " <> show k
