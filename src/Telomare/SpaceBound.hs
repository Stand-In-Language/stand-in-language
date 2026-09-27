-- |The language a static space bound is stated in: a maximum over affine
-- expressions in input sizes. @3·|input.left| + 12@ is one affine; a program
-- whose peak depends on which branch runs gets the maximum of several.
--
-- The variables are input /paths/, indexed the way the sizing pass indexes
-- its symbolic input (`Telomare.Size.IR.IndexedInputF`): the whole input is
-- path 0, and a node at path n has its left part at 2n+1 and its right part
-- at 2n+2. @|p|@ stands for the size in cells of the input part at path p.
--
-- Everything here is an upper bound, so the operations are free to lose
-- precision but never soundness: pruning only drops affines another affine
-- dominates pointwise, and widening replaces a set of affines with their
-- pointwise maximum, which bounds each of them.
--
-- Bounds are accumulated over millions of machine transitions, so they are
-- built strict all the way down; left lazy, each accumulation is a thunk
-- retaining the state it was made from.
module Telomare.SpaceBound where

import Data.List (group, intercalate, nub, sort)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Numeric.Natural (Natural)

-- |One affine expression: Σ coeff_p · |p| + constant. No path is stored
-- with coefficient zero.
data Affine = Affine
  { affCoeffs :: !(Map Integer Natural)
  , affConst  :: !Natural
  }
  deriving (Eq, Ord, Show)

-- |A bound: the maximum of some affines, kept free of dominated entries and
-- never empty.
newtype SpaceBound = SpaceBound [Affine]
  deriving (Eq, Show)

sbConst :: Natural -> SpaceBound
sbConst k = SpaceBound [Affine Map.empty k]

-- |The size of the input part at a path.
sbInput :: Integer -> SpaceBound
sbInput p = SpaceBound [Affine (Map.singleton p 1) 0]

-- |Whether the second affine is everywhere at least the first.
dominates :: Affine -> Affine -> Bool
dominates (Affine cs k) (Affine cs' k') = k <= k' && Map.isSubmapOfBy (<=) cs cs'

-- |Canonical form: zero coefficients dropped, dominated affines pruned, the
-- rest sorted so that equal bounds compare equal however they were put
-- together, and everything forced. The empty maximum holds nothing.
norm :: [Affine] -> SpaceBound
norm [] = sbConst 0
norm xs = foldr seq () affs `seq` SpaceBound affs
  where
    affs = sort (prune (fmap tidy xs))
    tidy (Affine cs k) = Affine (Map.filter (/= 0) cs) k
    prune = foldr keep []
    keep a kept | any (dominates a) kept = kept
                | otherwise = a : filter (not . (`dominates` a)) kept

-- |Cells held together sum.
instance Semigroup SpaceBound where
  SpaceBound as <> SpaceBound bs =
    norm [ Affine (Map.unionWith (+) cs cs') (k + k') | Affine cs k <- as, Affine cs' k' <- bs ]

instance Monoid SpaceBound where
  mempty = sbConst 0

-- |Either alone: peaks of alternative runs take the worse one.
sbMax :: SpaceBound -> SpaceBound -> SpaceBound
sbMax (SpaceBound as) (SpaceBound bs) = norm (as <> bs)

-- |A bound taken a concrete number of times over.
sbScale :: Natural -> SpaceBound -> SpaceBound
sbScale n (SpaceBound affs) = norm [ Affine (fmap (n *) cs) (n * k) | Affine cs k <- affs ]

-- |Collapse to the pointwise maximum once the affine set outgrows the cap:
-- looser, still sound.
sbWiden :: Int -> SpaceBound -> SpaceBound
sbWiden cap b@(SpaceBound affs)
  | length affs <= cap = b
  | otherwise = SpaceBound [foldr1 pointwiseMax affs]
  where
    pointwiseMax (Affine cs k) (Affine cs' k') = Affine (Map.unionWith max cs cs') (max k k')

-- |The figure at a valuation of the input sizes. Pointwise: @(<>)@ adds,
-- 'sbMax' takes the maximum, 'norm' is exact and 'sbWiden' is at least.
sbEvaluate :: (Integer -> Natural) -> SpaceBound -> Natural
sbEvaluate valuation (SpaceBound affs) =
  maximum [ k + sum [ c * valuation p | (p, c) <- Map.toList cs ] | Affine cs k <- affs ]

-- |A path as the words a reader would use: @input@, @input.left.right@, …
-- A run of four or more equal steps is folded (@input.left×63@), since deep
-- recursion positions otherwise render as hundreds of characters.
renderPath :: Integer -> String
renderPath path = intercalate "." ("input" : fmap fold (group (go [] path))) where
  go acc 0 = acc
  go acc p
    | odd p = go ("left" : acc) ((p - 1) `div` 2)
    | otherwise = go ("right" : acc) ((p - 2) `div` 2)
  fold run@(step : _)
    | length run >= 4 = step <> "×" <> show (length run)
    | otherwise = intercalate "." run
  fold [] = ""

-- |A figure a reader can take in at a glance: exact up to six digits, and
-- rounded /up/ to three significant figures above that — every rendered
-- figure is at least the true one, so an upper bound stays an upper bound.
renderNatUp :: Natural -> String
renderNatUp n
  | not (natRounds n) = show n
  | rounded == 1000 = "1.00×10^" <> show (length digits)
  | otherwise = case show rounded of
      (d : rest) -> d : '.' : rest <> "×10^" <> show (length digits - 1)
      []         -> show n
  where
    digits = show n
    lead = read (take 3 digits) :: Natural
    rounded = if all (== '0') (drop 3 digits) then lead else lead + 1

-- |Whether 'renderNatUp' shows this figure rounded rather than exactly.
natRounds :: Natural -> Bool
natRounds n = n > 999999

-- |Whether any figure in the bound renders rounded.
sbRounds :: SpaceBound -> Bool
sbRounds (SpaceBound affs) =
  any (\(Affine cs k) -> any natRounds (k : Map.elems cs)) affs

-- |The bound collapsed to a single affine in the whole input: every input
-- part is a subtree of the input, so @|p| ≤ |input|@ for every path, and
-- @Σ c_p·|p| + k ≤ (Σ c_p)·|input| + k@; alternatives collapse by pointwise
-- maximum. Sound, and at a glance.
sbHeadline :: SpaceBound -> Affine
sbHeadline (SpaceBound affs) = Affine (Map.filter (/= 0) (Map.singleton 0 c)) k
  where
    (c, k) = foldr1 pointwise
      [ (sum (Map.elems cs), k') | Affine cs k' <- affs ]
    pointwise (a, b) (a', b') = (max a a', max b b')

-- |Whether the headline already says everything: one affine, over nothing
-- finer than the whole input.
sbIsHeadline :: SpaceBound -> Bool
sbIsHeadline (SpaceBound [Affine cs _]) = Map.null (Map.delete 0 cs)
sbIsHeadline _                          = False

-- |The alternatives of a bound, one rendered affine each.
sbCases :: SpaceBound -> [String]
sbCases (SpaceBound affs) = nub (fmap affine affs)

-- |An affine over many input parts is summarized rather than spelled out.
renderSpaceBound :: SpaceBound -> String
renderSpaceBound (SpaceBound [a]) = affine a
renderSpaceBound (SpaceBound affs) = "max(" <> intercalate ", " (nub (fmap affine affs)) <> ")"

affine :: Affine -> String
affine (Affine cs k)
  | Map.size cs > 4 = "(a sum over " <> show (Map.size cs)
      <> " input parts, coefficients totalling " <> renderNatUp (sum (Map.elems cs))
      <> ") + " <> renderNatUp k
  | null terms = renderNatUp k
  | otherwise = intercalate " + " (terms <> [renderNatUp k | k /= 0])
  where
    terms = [ coeff c <> "|" <> renderPath p <> "|" | (p, c) <- Map.toAscList cs ]
    coeff 1 = ""
    coeff c = renderNatUp c <> "·"
