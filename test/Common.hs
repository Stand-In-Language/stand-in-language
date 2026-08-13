{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Common where

import Control.Comonad.Cofree (Cofree ((:<)))
import Telomare.Error
import Telomare.IR.Base
import Telomare.IR.Core
import Telomare.IR.Loc
import Telomare.Resolve
import Test.QuickCheck

instance Arbitrary Term1 where
  arbitrary = sized (genTree []) where
    leaves :: [String] -> Gen Term1
    leaves varList =
      oneof $
          (if not (null varList) then (((UnknownLoc :<) . ParserTermL . VarF <$> elements varList) :) else id)
          [ pure $ UnknownLoc :< ParserTermB ZeroSF
          ]
    lambdaTerms = ["w", "x", "y", "z"]
    genTree :: [String] -> Int -> Gen Term1
    genTree varList i = let half = div i 2
                            third = div i 3
                            recur = genTree varList
                        in case i of
                                 0 -> leaves varList
                                 _x -> oneof
                                   [ leaves varList
                                   , (UnknownLoc :<) . ParserTermH . HashF <$> recur (i - 1)
                                   , (UnknownLoc :<) . ParserTermH . HLeftF <$> recur (i - 1)
                                   , (UnknownLoc :<) . ParserTermH . HRightF <$> recur (i - 1)
                                   , (UnknownLoc :<) . ParserTermH . HTraceF <$> recur (i - 1)
                                   , elements lambdaTerms >>= \var -> (UnknownLoc :<) . ParserTermL . LamF (Open var) <$> genTree (var : varList) (i - 1)
                                   , (\a b c -> UnknownLoc :< ParserTermH (ITEF a b c)) <$> recur third <*> recur third <*> recur third
                                   , (\a b c -> UnknownLoc :< ParserTermH (RecursionF a b c)) <$> recur third <*> recur third <*> recur third
                                   , (\a b -> UnknownLoc :< ParserTermB (PairSF a b)) <$> recur half <*> recur half
                                   , (\a b -> UnknownLoc :< ParserTermL (AppF a b)) <$> recur half <*> recur half
                                   ]
  shrink = \case
    _ :< ParserTermB ZeroSF -> []
    anno :< ParserTermH (RecursionF t r b) -> t : r : b : [anno :< ParserTermH (RecursionF nt nr nb) | (nt, nr, nb) <- shrink (t,r,b)]
    _ :< ParserTermL (VarF _) -> []
    anno :< ParserTermH (HashF x) -> x : fmap ((anno :<) . ParserTermH . HashF) (shrink x)
    anno :< ParserTermH (HLeftF x) -> x : fmap ((anno :<) . ParserTermH . HLeftF) (shrink x)
    anno :< ParserTermH (HRightF x) -> x : fmap ((anno :<) . ParserTermH . HRightF) (shrink x)
    anno :< ParserTermH (HTraceF x) -> x : fmap ((anno :<) . ParserTermH . HTraceF) (shrink x)
    anno :< ParserTermL (LamF v x) -> x : fmap ((anno :<) . ParserTermL . LamF v) (shrink x)
    anno :< ParserTermH (ITEF i t e) -> i : t : e : [anno :< ParserTermH (ITEF ni nt ne) | (ni, nt, ne) <- shrink (i,t,e)]
    anno :< ParserTermB (PairSF a b) -> a : b : [anno :< ParserTermB (PairSF na nb) | (na, nb) <- shrink (a,b)]
    anno :< ParserTermL (AppF f i) -> f : i : [anno :< ParserTermL (AppF nf ni) | (nf, ni) <- shrink (f,i)]
    _ -> error "Common.shrink: unexpected Term1 constructor"

instance Arbitrary Term2 where
  arbitrary = do
    term1 <- arbitrary :: Gen Term1
    let term2 = case debruijinize term1 of
                  Left str -> error $ "Non valid `Term1` generated from `arbitrarry :: Gen Term1`: "
                                        <> show term1
                                        <> " With error message: "
                                        <> shre str
                  Right t2 -> t2
        shre :: ResolverError -> String
        shre = show
    pure term2
  shrink = \case
    _ :< ParserTermB ZeroSF -> []
    anno :< ParserTermH (RecursionF t r b) -> t : r : b : [anno :< ParserTermH (RecursionF nt nr nb) | (nt, nr, nb) <- shrink (t,r,b)]
    _ :< ParserTermL (VarF _) -> []
    anno :< ParserTermH (HashF x) -> x : fmap ((anno :<) . ParserTermH . HashF) (shrink x)
    anno :< ParserTermH (HLeftF x) -> x : fmap ((anno :<) . ParserTermH . HLeftF) (shrink x)
    anno :< ParserTermH (HRightF x) -> x : fmap ((anno :<) . ParserTermH . HRightF) (shrink x)
    anno :< ParserTermH (HTraceF x) -> x : fmap ((anno :<) . ParserTermH . HTraceF) (shrink x)
    anno :< ParserTermL (LamF v x) -> x : fmap ((anno :<) . ParserTermL . LamF v) (shrink x)
    anno :< ParserTermH (ITEF i t e) -> i : t : e : [anno :< ParserTermH (ITEF ni nt ne) | (ni, nt, ne) <- shrink (i,t,e)]
    anno :< ParserTermB (PairSF a b) -> a : b : [anno :< ParserTermB (PairSF na nb) | (na, nb) <- shrink (a,b)]
    anno :< ParserTermL (AppF f i) -> f : i : [anno :< ParserTermL (AppF nf ni) | (nf, ni) <- shrink (f,i)]
    _ -> error "Common.shrink: unexpected Term2 constructor"
