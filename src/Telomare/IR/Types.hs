{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE LambdaCase        #-}

-- |The type language the type checker works over: concrete 'DataType's and
-- 'PartialType's with unification variables.
module Telomare.IR.Types where

import Control.Lens.Combinators (Plated (..), transform)
import Data.Fix (Fix (..))
import Data.Functor.Classes (Eq1 (..), Ord1, Show1 (..))
import Data.Functor.Foldable (Corecursive (embed), Recursive (cata))
import Data.GenValidity (GenValid)
import Data.Validity (Validity)
import GHC.Generics (Generic, Generic1, Generically1 (..))
import Telomare.IR.Loc (LocTag)

data DataType
  = ZeroType
  | ArrType DataType DataType
  | PairType DataType DataType -- only used when at least one side of a pair is not ZeroType
  deriving (Eq, Show, Ord, Generic)

instance Validity DataType
instance GenValid DataType

instance Plated DataType where
  plate f = \case
    ArrType i o  -> ArrType <$> f i <*> f o
    PairType a b -> PairType <$> f a <*> f b
    x            -> pure x

data PartialTypeF f
  = ZeroTypeP
  | AnyType
  | TypeVariable LocTag Int
  | ArrTypeP f f
  | PairTypeP f f
  deriving (Eq, Ord, Show, Generic1, Functor, Foldable, Traversable)
  deriving Eq1 via (Generically1 PartialTypeF)
  deriving Ord1 via (Generically1 PartialTypeF)
instance Show1 PartialTypeF where
  liftShowsPrec showsPrecFunc _showList _d = \case
    ZeroTypeP -> showString "ZeroTypeP"
    AnyType -> showString "AnyType"
    TypeVariable l i -> showString "TypeVariable " . shows l . showString " " . shows i
    ArrTypeP i o -> showString "ArrTypeP (" . showsPrecFunc 0 i . showString " -> " . showsPrecFunc 0 o . showString ")"
    PairTypeP _a b -> showString "PairTypeP (" . showsPrecFunc 0 b . showString ", " . showsPrecFunc 0 b . showString ")"

type PartialType = Fix PartialTypeF

toPartialType :: DataType -> PartialType
toPartialType = \case
  ZeroType -> embed ZeroTypeP
  ArrType i o -> embed $ ArrTypeP (toPartialType i) (toPartialType o)
  PairType a b -> embed $ PairTypeP (toPartialType a) (toPartialType b)

mergePairType :: DataType -> DataType
mergePairType = transform f where
  f (PairType ZeroType ZeroType) = ZeroType
  f x                            = x

mergePairTypeP :: PartialType -> PartialType
mergePairTypeP = cata f where
  f = \case
    (PairTypeP (Fix ZeroTypeP) (Fix ZeroTypeP)) -> embed ZeroTypeP
    x -> embed x

containsFunction :: PartialType -> Bool
containsFunction = cata f where
  f = \case
    ArrTypeP _ _ -> True
    x -> or x

cleanType :: PartialType -> Bool
cleanType = cata f where
  f = \case
    ZeroTypeP -> True
    PairTypeP a b -> a && b
    _ -> False
