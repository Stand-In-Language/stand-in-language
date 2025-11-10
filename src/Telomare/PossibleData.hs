{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ViewPatterns               #-}

module Telomare.PossibleData where

import Control.Applicative
import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Monad (liftM2, (<=<))
import Control.Monad.Except
import Control.Monad.State.Strict (State, StateT)
import qualified Control.Monad.State.Strict as State
import Data.Fix (Fix (..))
import Data.Functor.Classes (Eq1 (..), Show1 (liftShowsPrec))
import Data.Functor.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Validity (Validity (..), declare, trivialValidation)
import Debug.Trace
import GHC.Generics (Generic)

import Data.Bifunctor (first)
import PrettyPrint
import Telomare (IExpr (..), LocTag (..), PartialType (..), TelomareLike (..),
                 UnsizedRecursionToken (..), convertAbortMessage,
                 indentWithChildren', indentWithOneChild',
                 indentWithTwoChildren')

debug' :: Bool
debug' = True

debugTrace' :: String -> a -> a
debugTrace' s x = if debug' then trace s x else x

type TCallStack a = [(FunctionIndex, a)]

class HasTCallStack c where
  type CallStackT c
  getCallStack :: c -> TCallStack (CallStackT c)

class BasicBase g where
  embedB :: PartExprF x -> g x
  extractB :: g x -> Maybe (PartExprF x)

class StuckBase g where
  embedS :: StuckF x -> g x
  extractS :: g x -> Maybe (StuckF x)

class SuperBase g where
  embedP :: SuperPositionF x -> g x
  extractP :: g x -> Maybe (SuperPositionF x)

class FuzzyBase g where
  embedF :: FuzzyInputF x -> g x
  extractF :: g x -> Maybe (FuzzyInputF x)

class AbortBase g where
  embedA :: AbortableF x -> g x
  extractA :: g x -> Maybe (AbortableF x)

class UnsizedBase g where
  embedU :: UnsizedRecursionF x -> g x
  extractU :: g x -> Maybe (UnsizedRecursionF x)

class IndexedInputBase g where
  embedI :: IndexedInputF x -> g x
  extractI :: g x -> Maybe (IndexedInputF x)

class DeferredEvalBase g where
  embedD :: DeferredEvalF x -> g x
  extractD :: g x -> Maybe (DeferredEvalF x)

pattern BasicFW :: BasicBase g => PartExprF x -> g x
pattern BasicFW x <- (extractB -> Just x)
pattern BasicEE :: (Base g ~ f, BasicBase f, Recursive g) => PartExprF g -> g
pattern BasicEE x <- (project -> BasicFW x)
pattern StuckFW :: (StuckBase g) => StuckF x -> g x
pattern StuckFW x <- (extractS -> Just x)
pattern StuckEE :: (Base g ~ f, StuckBase f, Recursive g) => StuckF g -> g
pattern StuckEE x <- (project -> StuckFW x)
pattern SuperFW :: SuperBase g => SuperPositionF x -> g x
pattern SuperFW x <- (extractP -> Just x)
pattern SuperEE :: (Base g ~ f, SuperBase f, Recursive g) => SuperPositionF g -> g
pattern SuperEE x <- (project -> (SuperFW x))
pattern FuzzyFW :: FuzzyBase g => FuzzyInputF x -> g x
pattern FuzzyFW x <- (extractF -> Just x)
pattern FuzzyEE :: (Base g ~ f, FuzzyBase f, Recursive g) => FuzzyInputF g -> g
pattern FuzzyEE x <- (project -> (FuzzyFW x))
pattern AbortFW :: AbortBase g => AbortableF x -> g x
pattern AbortFW x <- (extractA -> Just x)
pattern AbortEE :: (Base g ~ f, AbortBase f, Recursive g) => AbortableF g -> g
pattern AbortEE x <- (project -> (AbortFW x))
pattern UnsizedFW :: UnsizedBase g => UnsizedRecursionF x -> g x
pattern UnsizedFW x <- (extractU -> Just x)
pattern UnsizedEE :: (Base g ~ f, UnsizedBase f, Recursive g) => UnsizedRecursionF g -> g
pattern UnsizedEE x <- (project -> (UnsizedFW x))
pattern IndexedFW :: IndexedInputBase g => IndexedInputF x -> g x
pattern IndexedFW x <- (extractI -> Just x)
pattern IndexedEE :: (Base g ~ f, IndexedInputBase f, Recursive g) => IndexedInputF g -> g
pattern IndexedEE x <- (project -> (IndexedFW x))
pattern DeferredFW :: DeferredEvalBase g => DeferredEvalF x -> g x
pattern DeferredFW x <- (extractD -> Just x)
pattern DeferredEE :: (Base g ~ f, DeferredEvalBase f, Recursive g) => DeferredEvalF g -> g
pattern DeferredEE x <- (project -> (DeferredFW x))
basicEE :: (Base g ~ f, BasicBase f, Corecursive g) => PartExprF g -> g
basicEE = embed . embedB
stuckEE :: (Base g ~ f, StuckBase f, Corecursive g) => StuckF g -> g
stuckEE = embed . embedS
superEE :: (Base g ~ f, SuperBase f, Corecursive g) => SuperPositionF g -> g
superEE = embed . embedP
fuzzyEE :: (Base g ~ f, FuzzyBase f, Corecursive g) => FuzzyInputF g -> g
fuzzyEE = embed . embedF
abortEE :: (Base g ~ f, AbortBase f, Corecursive g) => AbortableF g -> g
abortEE = embed . embedA
unsizedEE :: (Base g ~ f, UnsizedBase f, Corecursive g) => UnsizedRecursionF g -> g
unsizedEE = embed . embedU
indexedEE :: (Base g ~ f, IndexedInputBase f, Corecursive g) => IndexedInputF g -> g
indexedEE = embed . embedI
deferredEE :: (Base g ~ f, DeferredEvalBase f, Corecursive g) => DeferredEvalF g -> g
deferredEE = embed . embedD
zeroB :: (Base g ~ f, BasicBase f, Corecursive g) => g
zeroB = basicEE ZeroSF
pairB :: (Base g ~ f, BasicBase f, Corecursive g) => g -> g -> g
pairB a b = basicEE $ PairSF a b
envB :: (Base g ~ f, BasicBase f, Corecursive g) => g
envB = basicEE EnvSF
setEnvB :: (Base g ~ f, BasicBase f, Corecursive g) => g -> g
setEnvB = basicEE . SetEnvSF
gateB :: (Base g ~ f, BasicBase f, Corecursive g) => g -> g -> g
gateB l r = basicEE $ GateSF l r
leftB :: (Base g ~ f, BasicBase f, Corecursive g) => g -> g
leftB = basicEE . LeftSF
rightB :: (Base g ~ f, BasicBase f, Corecursive g) => g -> g
rightB = basicEE . RightSF

pattern FillFunction :: (Base g ~ f, BasicBase f, Recursive g) => g -> g -> f g
pattern FillFunction c e <- BasicFW (SetEnvSF (BasicEE (PairSF c e)))
pattern GateSwitch :: (Base g ~ f, BasicBase f, Recursive g) => g -> g -> g -> f g
pattern GateSwitch l r s <- FillFunction (BasicEE (GateSF l r)) s
pattern AppEE :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g) => g -> g -> g
pattern AppEE c i <- BasicEE (SetEnvSF (BasicEE (SetEnvSF (BasicEE (PairSF (StuckEE (DeferSF _ (BasicEE (PairSF (BasicEE (LeftSF (BasicEE (RightSF (BasicEE EnvSF))))) (BasicEE (PairSF (BasicEE (LeftSF (BasicEE EnvSF))) (BasicEE (RightSF (BasicEE (RightSF (BasicEE EnvSF))))))))))) (BasicEE (PairSF i c)))))))
fillFunction :: (Base g ~ f, BasicBase f, Corecursive g) => g -> g -> g
fillFunction c e = setEnvB (pairB c e)
gateSwitch :: (Base g ~ f, BasicBase f, Corecursive g) => g -> g -> g -> g
gateSwitch l r = fillFunction (gateB l r)

data PartExprF f
  = ZeroSF
  | PairSF f f
  | EnvSF
  | SetEnvSF f
  | GateSF f f
  | LeftSF f
  | RightSF f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Eq1 PartExprF where
  liftEq test a b = case (a,b) of
    (ZeroSF, ZeroSF)         -> True
    (EnvSF, EnvSF)           -> True
    (PairSF a b, PairSF c d) -> test a c && test b d
    (SetEnvSF x, SetEnvSF y) -> test x y
    (GateSF a b, GateSF c d) -> test a c && test b d
    (LeftSF x, LeftSF y)     -> test x y
    (RightSF x, RightSF y)   -> test x y
    _                        -> False

instance Show1 PartExprF where
  liftShowsPrec showsPrec' showList prec = \case
    ZeroSF -> shows "ZeroSF"
    PairSF a b -> shows "PairSF (" . showsPrec' 0 a . shows ", " . showsPrec' 0 b . shows ")"
    EnvSF -> shows "EnvSF"
    SetEnvSF x -> shows "SetEnvSF (" . showsPrec' 0 x . shows ")"
    GateSF l r -> shows "GateSF (" . showsPrec' 0 l . shows ", " . showsPrec' 0 r . shows ")"
    LeftSF x -> shows "LeftSF (" . showsPrec' 0 x . shows ")"
    RightSF x -> shows "RightSF (" . showsPrec' 0 x . shows ")"

newtype FunctionIndex = FunctionIndex { unFunctionIndex :: Int } deriving (Eq, Ord, Enum, Show, Generic)

instance Validity FunctionIndex

instance PrettyPrintable FunctionIndex where
  showP = pure . ("F" <>) . show . fromEnum

showFI :: FunctionIndex -> String
showFI = ("F" <>) . show . fromEnum

data GateResult a
  = GateResult
  { leftBranch  :: Bool
  , rightBranch :: Bool
  , noBranch    :: Maybe a
  } deriving (Eq, Ord)

instance PrettyPrintable a => Show (GateResult a) where
  -- show (GateResult lb rb nb) = "GateResult " <> show lb <> " " <> show rb <> " " <> prettyPrint nb
  show (GateResult lb rb nb) = "GateResult " <> show lb <> " " <> show rb <> " " <> pnb where
    pnb = case nb of
      Just nb' -> prettyPrint nb'
      _        -> "Nothing"

data StuckF f
  = DeferSF FunctionIndex f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Show1 StuckF where
  liftShowsPrec showsPrec' showList prec = \case
    DeferSF fi x -> shows "DeferSF " . shows fi . shows " (" . showsPrec' 0 x . shows ")"
instance PrettyPrintable1 StuckF where
  showP1 = \case
    DeferSF ind x -> indentWithOneChild' (showFI ind) $ showP x
instance Eq1 StuckF where
  liftEq test a b = case (a,b) of
    (DeferSF ix _, DeferSF iy _) | ix == iy -> True -- test a b
    _                                       -> False

newtype SizedRecursion = SizedRecursion { unSizedRecursion :: Map UnsizedRecursionToken (Maybe Int)}
  deriving (Eq, Ord, Show, Generic)

instance Semigroup SizedRecursion where
  (<>) (SizedRecursion a) (SizedRecursion b) = SizedRecursion . tr $ Map.unionWith (liftM2 max) a b where
    tr x = if null a || null b
      then x
      else debugTrace' ("sizedrecursion merge result: " <> show (first fromEnum <$> Map.toAscList x)) x

instance Monoid SizedRecursion where
  mempty = SizedRecursion Map.empty

instance PrettyPrintable1 ((,) SizedRecursion) where
  showP1 (_,x) = showP x

instance Validity SizedRecursion where
  validate = trivialValidation

data StrictAccum a x = StrictAccum
  { getAccum :: !a
  , getX     :: x
  }
  deriving Functor

instance Monoid a => Applicative (StrictAccum a) where
  pure = StrictAccum mempty
  StrictAccum u f <*> StrictAccum v x = StrictAccum (u <> v) $ f x
  liftA2 f (StrictAccum u x) (StrictAccum v y) = StrictAccum (u <> v) $ f x y

instance Monoid a => Monad (StrictAccum a) where
  StrictAccum u x >>= f = case f x of StrictAccum v y -> StrictAccum (u <> v) y

instance PrettyPrintable1 (StrictAccum SizedRecursion) where
  showP1 (StrictAccum _ x) = showP x

data VoidF f
  deriving (Functor, Foldable, Traversable)

instance Show (VoidF a) where
  show = undefined

instance Eq (VoidF a) where
  (==) = undefined

data SuperPositionF f
  = EitherPF (Maybe Integer) !f !f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Eq1 SuperPositionF where
  liftEq test a b = case (a,b) of
    (EitherPF x a b, EitherPF y c d) -> x == y && test a c && test b d
    _                                -> False

instance Show1 SuperPositionF where
  liftShowsPrec showsPrec' showList prec = \case
    EitherPF x a b -> shows "EitherPF " . shows x . shows " (" . showsPrec' 0 a . shows ", " . showsPrec' 0 b . shows ")"

data FuzzyInputF f
  = MaybePairF f f
  | SomeInputF
  | FunctionListF [f]
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Eq1 FuzzyInputF where
  liftEq test a b = case (a,b) of
    (SomeInputF, SomeInputF) -> True
    (MaybePairF a b, MaybePairF c d) -> test a c && test b d
    (FunctionListF x, FunctionListF y) -> length x == length y && and (zipWith test x y)
    _ -> False

instance Show1 FuzzyInputF where
  liftShowsPrec showsPrec' showList prec = \case
    SomeInputF -> shows "SomeInputF"
    MaybePairF a b -> shows "MaybePairF (" . showsPrec' 0 a . shows ", " . showsPrec' 0 b . shows ")"
    FunctionListF x -> shows "FunctionListF " . showList x

-- TODO we can simplify abort semantics to (defer env), and then could do gate x (abort [message] x) for conditional abort
data AbortableF f
  = AbortF
  | AbortedF IExpr
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Eq1 AbortableF  where
  liftEq test a b = case (a,b) of
    (AbortF, AbortF)                  -> True
    (AbortedF a, AbortedF b) | a == b -> True
    _                                 -> False

instance Show1 AbortableF where
  liftShowsPrec showsPrec showList prec = \case
    AbortF     -> shows "AbortF"
    AbortedF x -> shows "(AbortedF " . shows x . shows ")"

class ShallowEq a where
  shallowEq :: a -> a -> Bool
class ShallowEq1 f where
  shallowEq1 :: f a -> f b -> Bool
instance ShallowEq1 PartExprF where
  shallowEq1 a b = case (a,b) of
    (ZeroSF, ZeroSF) -> True
    _                -> False
instance ShallowEq1 StuckF where
  shallowEq1 a b = case (a,b) of
    (DeferSF fida _, DeferSF fidb _) -> fida == fidb
    _                                -> False
instance ShallowEq1 AbortableF where
  shallowEq1 a b = case (a,b) of
    (AbortedF a', AbortedF b') -> a' == b'
    (AbortF, AbortF)           -> True
    _                          -> False

data UnsizedRecursionF f
  = RecursionTestF UnsizedRecursionToken f
  | UnsizedStubF UnsizedRecursionToken f
  | SizingWrapperF LocTag UnsizedRecursionToken f
  | SizeStageF SizedRecursion f
  | RefinementWrapperF LocTag f f
  | SizeStepStubF UnsizedRecursionToken Int f
  | TraceF String f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Eq1 UnsizedRecursionF where
  liftEq test a b = case (a, b) of
    (RecursionTestF ta a, RecursionTestF tb b) -> ta == tb && test a b
    _                                          -> False

instance Show1 UnsizedRecursionF where
  liftShowsPrec showsPrec' showList prec x = case x of
    RecursionTestF be x -> shows "RecursionTestF (" . shows be . shows " " . showsPrec' 0 x . shows ")"
    SizeStageF sm x -> shows "SizeStageF " . shows sm
      . shows " (" . showsPrec' 0 x . shows ")"
    SizeStepStubF _ _ x -> shows "SizeStepStubF (" . showsPrec' 0 x . shows ")"

instance PrettyPrintable1 PartExprF where
  showP1 = \case
    ZeroSF     -> pure "Z"
    PairSF a b -> indentWithTwoChildren' "P" (showP a) (showP b)
    EnvSF      -> pure "E"
    SetEnvSF x -> indentWithOneChild' "S" $ showP x
    GateSF l r -> indentWithTwoChildren' "G" (showP l) (showP r)
    LeftSF x   -> indentWithOneChild' "L" $ showP x
    RightSF x  -> indentWithOneChild' "R" $ showP x

instance PrettyPrintable1 SuperPositionF where
  showP1 = \case
    EitherPF x a b -> indentWithTwoChildren' ("%" <> show x) (showP a) (showP b)

instance PrettyPrintable1 FuzzyInputF where
  showP1 = \case
    SomeInputF -> pure "A"
    MaybePairF a b -> indentWithTwoChildren' "%" (showP a) (showP b)
    FunctionListF l -> indentWithChildren' "^" $ fmap showP l

instance PrettyPrintable1 AbortableF where
  showP1 = \case
    AbortF      -> pure "!"
    AbortedF am -> pure $ "(aborted - " <> convertAbortMessage am <> ")"

instance PrettyPrintable1 UnsizedRecursionF where
  showP1 = \case
    RecursionTestF (UnsizedRecursionToken ind) x -> indentWithOneChild' ("T(" <> show ind <> ")") $ showP x
    SizingWrapperF loc (UnsizedRecursionToken ind) x -> indentWithOneChild' ("&(" <> show loc <> " " <> show ind <> ")") $ showP x
    UnsizedStubF (UnsizedRecursionToken ind) x -> indentWithOneChild' ("#" <> show ind) $ showP x
    SizeStageF _ x -> indentWithOneChild' "^" $ showP x
    RefinementWrapperF l tc x -> indentWithTwoChildren' (":" <> show l) (showP tc) (showP x)
    SizeStepStubF _ _ x -> indentWithOneChild' "@" $ showP x
    TraceF _ x -> indentWithOneChild' "_" $ showP x

instance PrettyPrintable1 VoidF where
  showP1 _ = error "VoidF should never be inhabited, so should not be PrettyPrintable1"

data IndexedInputF f
  = IVarF Integer
  | AnyF
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Eq1 IndexedInputF where
  liftEq test a b = case (a, b) of
    (IVarF x, IVarF y) -> x == y
    (AnyF, AnyF)       -> True
    _                  -> False

instance Show1 IndexedInputF where
  liftShowsPrec showsPrec showList prec x = case x of
    IVarF n -> shows $ "IVarF " <> show n
    AnyF    -> shows "IgnoreThis"

instance PrettyPrintable1 IndexedInputF where
  showP1 = \case
    IVarF n -> pure $ "I" <> show n
    AnyF -> pure "-"

data DeferredEvalF f
  = BarrierF f
  | ManyLefts Integer f
  | ManyRights Integer f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Eq1 DeferredEvalF where
  liftEq test a b = case (a, b) of
    (BarrierF x, BarrierF y)             -> test x y
    (ManyLefts na va, ManyLefts nb vb)   -> na == nb && test va vb
    (ManyRights na va, ManyRights nb vb) -> na == nb && test va vb
    _                                    -> False

instance Show1 DeferredEvalF where
  liftShowsPrec showsPrec' showList prec x = case x of
    BarrierF x -> shows "BarrierF (" . showsPrec' 0 x . shows ")"
    ManyLefts n x -> shows ("ManyLefts " <> show n) . shows " (" . showsPrec' 0 x . shows ")"
    ManyRights n x -> shows ("ManyRights " <> show n) . shows " (" . showsPrec' 0 x . shows ")"

instance PrettyPrintable1 DeferredEvalF where
  showP1 = \case
    BarrierF x -> indentWithOneChild' "|" $ showP x
    ManyLefts n x -> indentWithOneChild' ("L" <> show n) $ showP x
    ManyRights n x -> indentWithOneChild' ("R" <> show n) $ showP x

instance PrettyPrintable PartialType where
  showP x = pure $ f x where
    f = \case
      ZeroTypeP -> "Z"
      AnyType -> "A"
      TypeVariable _ n -> "V" <> show (fromEnum n)
      ArrTypeP a b -> case a of
        ArrTypeP _ _ -> "(" <> f a <> ") -> " <> f b
        _            -> f a <> " -> " <> f b
      PairTypeP a b -> "(" <> f a <> "," <> f b <> ")"

instance (Functor f, PrettyPrintable1 f) => PrettyPrintable (Fix f) where
  showP = showP1 . project

instance {-# OVERLAPPING #-} (PrettyPrintable a, PrettyPrintable1 f) => PrettyPrintable (Cofree f a) where
  showP (a :< x) = (<>) <$> showP a <*> showP1 x

data StuckExprF f
  = StuckExprB (PartExprF f)
  | StuckExprS (StuckF f)
  deriving (Functor, Foldable, Traversable)
instance BasicBase StuckExprF where
  embedB = StuckExprB
  extractB = \case
    StuckExprB x -> Just x
    _            -> Nothing
instance StuckBase StuckExprF where
  embedS = StuckExprS
  extractS = \case
    StuckExprS x -> Just x
    _            -> Nothing
instance PrettyPrintable1 StuckExprF where
  showP1 = \case
    StuckExprB x -> showP1 x
    StuckExprS x -> showP1 x

type StuckExpr = Fix StuckExprF

data DeferredExprF f
  = DeferredExprB (PartExprF f)
  | DeferredExprS (StuckF f)
  | DeferredExprD (DeferredEvalF f)
  deriving (Functor, Foldable, Traversable)
instance BasicBase DeferredExprF where
  embedB = DeferredExprB
  extractB = \case
    DeferredExprB x -> Just x
    _ -> Nothing
instance StuckBase DeferredExprF where
  embedS = DeferredExprS
  extractS = \case
    DeferredExprS x -> Just x
    _ -> Nothing
instance DeferredEvalBase DeferredExprF where
  embedD = DeferredExprD
  extractD = \case
    DeferredExprD x -> Just x
    _ -> Nothing
instance PrettyPrintable1 DeferredExprF where
  showP1 = \case
    DeferredExprB x -> showP1 x
    DeferredExprS x -> showP1 x
    DeferredExprD x -> showP1 x

type DeferredExpr = Fix DeferredExprF

data StaticCheckExprF f
  = StaticCheckExprB (PartExprF f)
  | StaticCheckExprS (StuckF f)
  | StaticCheckExprA (AbortableF f)
  | StaticCheckExprD (DeferredEvalF f)
  deriving (Functor, Foldable, Traversable)
instance BasicBase StaticCheckExprF where
  embedB = StaticCheckExprB
  extractB = \case
    StaticCheckExprB x -> Just x
    _ -> Nothing
instance StuckBase StaticCheckExprF where
  embedS = StaticCheckExprS
  extractS = \case
    StaticCheckExprS x -> Just x
    _ -> Nothing
instance AbortBase StaticCheckExprF where
  embedA = StaticCheckExprA
  extractA = \case
    StaticCheckExprA x -> Just x
    _ -> Nothing
instance DeferredEvalBase StaticCheckExprF where
  embedD = StaticCheckExprD
  extractD = \case
    StaticCheckExprD x -> Just x
    _ -> Nothing
instance PrettyPrintable1 StaticCheckExprF where
  showP1 = \case
    StaticCheckExprB x -> showP1 x
    StaticCheckExprS x -> showP1 x
    StaticCheckExprA x -> showP1 x
    StaticCheckExprD x -> showP1 x

type StaticCheckExpr = Fix StaticCheckExprF

data CompiledExprF f
  = CompiledExprB (PartExprF f)
  | CompiledExprS (StuckF f)
  | CompiledExprA (AbortableF f)
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic)
instance BasicBase CompiledExprF where
  embedB = CompiledExprB
  extractB = \case
    CompiledExprB x -> Just x
    _              -> Nothing
instance StuckBase CompiledExprF where
  embedS = CompiledExprS
  extractS = \case
    CompiledExprS x -> Just x
    _ -> Nothing
instance AbortBase CompiledExprF where
  embedA = CompiledExprA
  extractA = \case
    CompiledExprA x -> Just x
    _ -> Nothing
instance Eq1 CompiledExprF where
  liftEq test a b = case (a,b) of
    (CompiledExprB x, CompiledExprB y) -> liftEq test x y
    (CompiledExprS x, CompiledExprS y) -> liftEq test x y
    (CompiledExprA x, CompiledExprA y) -> liftEq test x y
    _                                  -> False
instance Show1 CompiledExprF where
  liftShowsPrec showsPrec showList prec = \case
    CompiledExprB x -> liftShowsPrec showsPrec showList prec x
    CompiledExprS x -> liftShowsPrec showsPrec showList prec x
    CompiledExprA x -> liftShowsPrec showsPrec showList prec x
instance PrettyPrintable1 CompiledExprF where
  showP1 = \case
    CompiledExprB x -> showP1 x
    CompiledExprS x -> showP1 x
    CompiledExprA x -> showP1 x

type CompiledExpr = Fix CompiledExprF

instance TelomareLike CompiledExpr where
  fromTelomare = flip State.evalState (toEnum 0) . f where
    f = \case
      Zero -> pure zeroB
      Pair a b -> pairB <$> f a <*> f b
      Env -> pure envB
      SetEnv x -> setEnvB <$> f x
      Defer x -> do
        fid <- State.get
        State.put $ succ fid
        stuckEE . DeferSF fid <$> f x
      Gate l r -> basicEE <$> (GateSF <$> f l <*> f r)
      PLeft x -> leftB <$> f x
      PRight x -> rightB <$> f x
      Trace -> do
        fid <- State.get
        State.put $ succ fid
        pure . stuckEE $ DeferSF fid envB
  {-
  fromTelomare = flip State.evalState (toEnum 0) . ana f where
    f = \case
      Zero ->  embedB $ pure ZeroSF
      Pair a b -> embedB $ PairSF (pure a) (pure b)
      Env -> embedB $ pure EnvSF
      SetEnv x -> embedB . SetEnvSF $ pure x
      Defer x -> do
        fid <- State.get
        State.put $ succ fid
        pure . embedS $ DeferSF fid x
-}
  toTelomare = cata f where
    f = \case
      BasicFW ZeroSF -> pure Zero
      BasicFW (PairSF a b) -> Pair <$> a <*> b
      BasicFW EnvSF -> pure Env
      BasicFW (SetEnvSF x) -> SetEnv <$> x
      StuckFW (DeferSF _ x) -> Defer <$> x
      BasicFW (GateSF l r) -> Gate <$> l <*> r
      BasicFW (LeftSF x) -> PLeft <$> x
      BasicFW (RightSF x) -> PRight <$> x
      AbortFW _ -> Nothing

data UnsizedExprF f
  = UnsizedExprB (PartExprF f)
  | UnsizedExprS (StuckF f)
  | UnsizedExprP (SuperPositionF f)
--  | UnsizedExprZ (FuzzyInputF f)
  | UnsizedExprA (AbortableF f)
  | UnsizedExprU (UnsizedRecursionF f)
  | UnsizedExprI (IndexedInputF f)
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic)
instance BasicBase UnsizedExprF where
  embedB = UnsizedExprB
  extractB = \case
    UnsizedExprB x -> Just x
    _              -> Nothing
instance StuckBase UnsizedExprF where
  embedS = UnsizedExprS
  extractS = \case
    UnsizedExprS x -> Just x
    _ -> Nothing
instance Show1 UnsizedExprF where
  liftShowsPrec showsPrec showList prec = \case
    UnsizedExprB x -> liftShowsPrec showsPrec showList prec x
    UnsizedExprS x -> liftShowsPrec showsPrec showList prec x
    UnsizedExprP x -> liftShowsPrec showsPrec showList prec x
    UnsizedExprA x -> liftShowsPrec showsPrec showList prec x
    UnsizedExprU x -> liftShowsPrec showsPrec showList prec x
    UnsizedExprI x -> liftShowsPrec showsPrec showList prec x
instance SuperBase UnsizedExprF where
  embedP = UnsizedExprP
  extractP = \case
    UnsizedExprP x -> Just x
    _              -> Nothing
{-
instance FuzzyBase UnsizedExprF where
  embedF = UnsizedExprZ
  extractF = \case
    UnsizedExprZ x -> Just x
    _ -> Nothing
-}
instance AbortBase UnsizedExprF where
  embedA = UnsizedExprA
  extractA = \case
    UnsizedExprA x -> Just x
    _              -> Nothing
instance IndexedInputBase UnsizedExprF where
  embedI = UnsizedExprI
  extractI = \case
    UnsizedExprI x -> Just x
    _              -> Nothing
instance UnsizedBase UnsizedExprF where
  embedU = UnsizedExprU
  extractU = \case
    UnsizedExprU x -> Just x
    _              -> Nothing
instance Eq1 UnsizedExprF where
  liftEq test a b = case (a,b) of
    (UnsizedExprB x, UnsizedExprB y) -> liftEq test x y
    (UnsizedExprS x, UnsizedExprS y) -> liftEq test x y
    (UnsizedExprP x, UnsizedExprP y) -> liftEq test x y
--    (UnsizedExprZ x, UnsizedExprZ y) -> liftEq test x y
    (UnsizedExprA x, UnsizedExprA y) -> liftEq test x y
    (UnsizedExprU x, UnsizedExprU y) -> liftEq test x y
    (UnsizedExprI x, UnsizedExprI y) -> liftEq test x y
    _                                -> False
instance ShallowEq1 UnsizedExprF where
  shallowEq1 a b = case (a,b) of
    (UnsizedExprB x, UnsizedExprB y) -> shallowEq1 x y
    (UnsizedExprS x, UnsizedExprS y) -> shallowEq1 x y
    (UnsizedExprA x, UnsizedExprA y) -> shallowEq1 x y
    _                                -> False

instance PrettyPrintable1 UnsizedExprF where
  showP1 = \case
    UnsizedExprB x -> showP1 x
    UnsizedExprS x -> showP1 x
    UnsizedExprP x -> showP1 x
--    UnsizedExprZ x -> showP1 x
    UnsizedExprA x -> showP1 x
    UnsizedExprU x -> showP1 x
    UnsizedExprI x -> showP1 x

type UnsizedExpr = Fix UnsizedExprF

data AllExprF f
  = AllExprB (PartExprF f)
  | AllExprS (StuckF f)
  | AllExprA (AbortableF f)
  | AllExprP (SuperPositionF f)
  | AllExprI (IndexedInputF f)
  | AllExprZ (FuzzyInputF f)
  | AllExprU (UnsizedRecursionF f)

data AbortExprF f
  = AbortExprB (PartExprF f)
  | AbortExprS (StuckF f)
  | AbortExprA (AbortableF f)
  deriving (Eq, Functor, Foldable, Traversable)
instance BasicBase AbortExprF where
  embedB = AbortExprB
  extractB = \case
    AbortExprB x -> Just x
    _            -> Nothing
instance StuckBase AbortExprF where
  embedS = AbortExprS
  extractS = \case
    AbortExprS x -> Just x
    _            -> Nothing
instance AbortBase AbortExprF where
  embedA = AbortExprA
  extractA = \case
    AbortExprA x -> Just x
    _            -> Nothing
instance Eq1 AbortExprF where
  liftEq test a b = case (a,b) of
    (AbortExprB x, AbortExprB y) -> liftEq test x y
    (AbortExprS x, AbortExprS y) -> liftEq test x y
    (AbortExprA x, AbortExprA y) -> liftEq test x y
    _                            -> False
instance PrettyPrintable1 AbortExprF where
  showP1 = \case
    AbortExprB x -> showP1 x
    AbortExprS x -> showP1 x
    AbortExprA x -> showP1 x

type AbortExpr = Fix AbortExprF

data InputSizingExprF f
  = InputSizingB (PartExprF f)
  | InputSizingS (StuckF f)
  | InputSizingA (AbortableF f)
  | InputSizingU (UnsizedRecursionF f)
  | InputSizingD (DeferredEvalF f)
  | InputSizingI (IndexedInputF f)
  deriving (Eq, Functor, Foldable, Traversable)
instance BasicBase InputSizingExprF where
  embedB = InputSizingB
  extractB = \case
    InputSizingB x -> Just x
    _            -> Nothing
instance StuckBase InputSizingExprF where
  embedS = InputSizingS
  extractS = \case
    InputSizingS x -> Just x
    _            -> Nothing
instance AbortBase InputSizingExprF where
  embedA = InputSizingA
  extractA = \case
    InputSizingA x -> Just x
    _            -> Nothing
instance UnsizedBase InputSizingExprF where
  embedU = InputSizingU
  extractU = \case
    InputSizingU x -> Just x
    _ -> Nothing
instance DeferredEvalBase InputSizingExprF where
  embedD = InputSizingD
  extractD = \case
    InputSizingD x -> Just x
    _ -> Nothing
instance IndexedInputBase InputSizingExprF where
  embedI = InputSizingI
  extractI = \case
    InputSizingI x -> Just x
    _ -> Nothing
instance Eq1 InputSizingExprF where
  liftEq test a b = case (a,b) of
    (InputSizingB x, InputSizingB y) -> liftEq test x y
    (InputSizingS x, InputSizingS y) -> liftEq test x y
    (InputSizingA x, InputSizingA y) -> liftEq test x y
    (InputSizingU x, InputSizingU y) -> liftEq test x y
    (InputSizingD x, InputSizingD y) -> liftEq test x y
    (InputSizingI x, InputSizingI y) -> liftEq test x y
    _                                -> False
instance PrettyPrintable1 InputSizingExprF where
  showP1 = \case
    InputSizingB x -> showP1 x
    InputSizingS x -> showP1 x
    InputSizingA x -> showP1 x
    InputSizingU x -> showP1 x
    InputSizingD x -> showP1 x
    InputSizingI x -> showP1 x
type InputSizingExpr = Fix InputSizingExprF

instance PrettyPrintable Char where
  showP = pure . (:[])

convertBasic :: (BasicBase g, BasicBase h, Base x ~ h, Corecursive x) => (g x -> x) -> g x -> x
convertBasic convertOther = \case
  BasicFW x -> basicEE x
  x -> convertOther x
convertStuck :: (StuckBase g, StuckBase h, Base x ~ h, Corecursive x) => (g x -> x) -> g x -> x
convertStuck convertOther = \case
  StuckFW x -> stuckEE x
  x -> convertOther x
convertSuper :: (SuperBase g, SuperBase h, Base x ~ h, Corecursive x) => (g x -> x) -> g x -> x
convertSuper convertOther = \case
  SuperFW x -> superEE x
  x -> convertOther x
convertFuzzy :: (FuzzyBase g, FuzzyBase h, Base x ~ h, Corecursive x) => (g x -> x) -> g x -> x
convertFuzzy convertOther = \case
  FuzzyFW x -> fuzzyEE x
  x -> convertOther x
convertAbort :: (AbortBase g, AbortBase h, Base x ~ h, Corecursive x) => (g x -> x) -> g x -> x
convertAbort convertOther = \case
  AbortFW x -> abortEE x
  x -> convertOther x
convertUnsized :: (UnsizedBase g, UnsizedBase h, Base x ~ h, Corecursive x) => (g x -> x) -> g x -> x
convertUnsized convertOther = \case
  UnsizedFW x -> unsizedEE x
  x -> convertOther x
convertIndexed :: (IndexedInputBase g, IndexedInputBase h, Base x ~ h, Corecursive x) => (g x -> x) -> g x -> x
convertIndexed convertOther = \case
  IndexedFW x -> indexedEE x
  x -> convertOther x
convertDeferred :: (DeferredEvalBase g, DeferredEvalBase h, Base x ~ h, Corecursive x) => (g x -> x) -> g x -> x
convertDeferred convertOther = \case
  DeferredFW x -> deferredEE x
  x -> convertOther x

data SizedResult = AbortedSR | UnsizableSR UnsizedRecursionToken
  deriving (Eq, Ord, Show)

instance Semigroup SizedResult where
  (<>) a b = case (a,b) of
    (u@(UnsizableSR _), _) -> u
    (_, u@(UnsizableSR _)) -> u
    _                      -> a

newtype MonoidList a = MonoidList { unMonoidList :: [a] }

instance Semigroup a => Semigroup (MonoidList a) where
  (<>) (MonoidList a) (MonoidList b) = MonoidList $ zipWith (<>) a b

instance Semigroup a => Monoid (MonoidList a) where
  mempty = MonoidList []

anaM' :: (Monad m, Corecursive t, x ~ Base t, Traversable x) => (a -> m (Base t a)) -> a -> m t
anaM' f = c where c = (fmap embed . mapM c) <=< f

convertToF :: (Base g ~ f, BasicBase f, StuckBase f, Traversable f, Corecursive g) => IExpr -> g
convertToF = flip State.evalState (toEnum 0) . anaM' f where
  f = \case
    Zero     -> pure $ embedB ZeroSF
    Pair a b -> pure . embedB $ PairSF a b
    Env      -> pure $ embedB EnvSF
    SetEnv x -> pure . embedB $ SetEnvSF x
    Defer x  -> embedS <$> (DeferSF <$> nextVar <*> pure x)
    Gate l r -> pure . embedB $ GateSF l r
    PLeft x  -> pure . embedB $ LeftSF x
    PRight x -> pure . embedB $ RightSF x
    Trace    -> error "EnhancedExpr trace"
  nextVar :: State FunctionIndex FunctionIndex
  nextVar = do
    i <- State.get
    State.put $ succ i
    pure i

convertFromF :: (Base g ~ f, TelomareLike g, BasicBase f, StuckBase f, Traversable f, Recursive g) => g -> Maybe IExpr
convertFromF = \case
  BasicEE x -> case x of
    ZeroSF     -> pure Zero
    PairSF a b -> Pair <$> toTelomare a <*> toTelomare b
    EnvSF      -> pure Env
    SetEnvSF p -> SetEnv <$> toTelomare p
    GateSF l r -> Gate <$> toTelomare l <*> toTelomare r
    LeftSF x   -> PLeft <$> toTelomare x
    RightSF x  -> PRight <$> toTelomare x
  StuckEE (DeferSF _ x) -> Defer <$> toTelomare x
  _ -> Nothing

instance TelomareLike StuckExpr where
  fromTelomare = convertToF
  toTelomare = convertFromF

instance TelomareLike UnsizedExpr where
  fromTelomare = convertToF
  toTelomare = convertFromF

instance TelomareLike DeferredExpr where
  fromTelomare = convertToF
  toTelomare = convertFromF

data TypeCheckError
  = UnboundType Int
  | InconsistentTypes PartialType PartialType
  | RecursiveType Int
  deriving (Eq, Ord, Show)

newPartialType :: AnnotateState PartialType
newPartialType = do
  (env, typeMap, v) <- State.get
  State.put (TypeVariable DummyLoc v, typeMap, v + 1)
  pure $ TypeVariable DummyLoc v

makeAssociations :: PartialType -> PartialType -> Either TypeCheckError (Set TypeAssociation)
makeAssociations ta tb = case (ta, tb) of
  (x, y) | x == y -> pure mempty
  (AnyType, _) -> pure mempty
  (_, AnyType) -> pure mempty
  (TypeVariable _ i, _) -> pure . Set.singleton $ TypeAssociation i tb
  (_, TypeVariable _ i) -> pure . Set.singleton $ TypeAssociation i ta
  (ArrTypeP a b, ArrTypeP c d) -> Set.union <$> makeAssociations a c <*> makeAssociations b d
  (PairTypeP a b, PairTypeP c d) -> Set.union <$> makeAssociations a c <*> makeAssociations b d
  (PairTypeP a b, ZeroTypeP) -> Set.union <$> makeAssociations a ZeroTypeP <*> makeAssociations b ZeroTypeP
  (ZeroTypeP, PairTypeP a b) -> Set.union <$> makeAssociations a ZeroTypeP <*> makeAssociations b ZeroTypeP
  _ -> Left $ InconsistentTypes ta tb

associateVar :: PartialType -> PartialType -> AnnotateState ()
associateVar a b = liftEither (makeAssociations a b) >>= \set -> State.modify (changeState set) where
  changeState set (curVar, oldSet, v) = (curVar, oldSet <> set, v)


data TypeAssociation = TypeAssociation Int PartialType
  deriving (Eq, Ord, Show)

type AnnotateState = ExceptT TypeCheckError (State (PartialType, Set TypeAssociation, Int))

class Annotatable a where
  anno :: a -> AnnotateState PartialType

class Annotatable1 f where
  liftAnno :: (a -> AnnotateState PartialType) -> f a -> AnnotateState PartialType

instance Annotatable1 PartExprF where
  liftAnno anno = \case
     ZeroSF -> pure ZeroTypeP
     PairSF a b -> PairTypeP <$> anno a <*> anno b
     EnvSF -> State.gets (\(t, _, _) -> t)
     SetEnvSF x -> do
       xt <- anno x
       it <- newPartialType
       ot <- newPartialType
       associateVar (PairTypeP (ArrTypeP it ot) it) xt
       pure ot
     GateSF l r -> do
       lt <- anno l
       rt <- anno l
       associateVar lt rt
       pure $ ArrTypeP ZeroTypeP lt
     LeftSF x -> do
       xt <- anno x
       la <- newPartialType
       associateVar (PairTypeP la AnyType) xt
       pure la
     RightSF x -> do
       xt <- anno x
       ra <- newPartialType
       associateVar (PairTypeP AnyType ra) xt
       pure ra

withNewEnv :: AnnotateState a -> AnnotateState (PartialType, a)
withNewEnv action = do
  (env, typeMap, v) <- State.get
  State.put (TypeVariable DummyLoc v, typeMap, v + 1)
  result <- action
  State.modify $ \(_, typeMap, v) -> (env, typeMap, v)
  pure (TypeVariable DummyLoc v, result)

instance Annotatable1 StuckF where
  liftAnno anno = \case
    DeferSF ind x -> do
      (it, ot) <- withNewEnv $ anno x
      pure $ ArrTypeP it ot

instance Annotatable1 SuperPositionF where
  liftAnno anno = \case
    EitherPF _ a b -> do
      at <- anno a
      bt <- anno b
      associateVar at bt
      pure at

instance Annotatable1 AbortableF where
  liftAnno anno = \case
    AbortF -> do
      it <- newPartialType
      pure $ ArrTypeP ZeroTypeP (ArrTypeP it it)
    AbortedF _ -> newPartialType

instance Annotatable1 UnsizedRecursionF where
  liftAnno anno = \case
    RecursionTestF _ x -> do
      xt <- anno x
      associateVar xt ZeroTypeP
      pure xt
    SizingWrapperF _ _ x -> anno x -- not bothering on checking for pair structure for now
    SizeStageF _ x -> anno x
    UnsizedStubF _ x -> anno x -- not bothering on checking internal structure (is it even possible?)
    RefinementWrapperF _ c x -> anno x -- not bothering on checking c

instance Annotatable1 IndexedInputF where
  liftAnno anno = \case
    AnyF -> pure ZeroTypeP
    IVarF _ -> pure ZeroTypeP

instance Annotatable1 UnsizedExprF where
  liftAnno anno = \case
    UnsizedExprB x -> liftAnno anno x
    UnsizedExprS x -> liftAnno anno x
    UnsizedExprP x -> liftAnno anno x
    UnsizedExprA x -> liftAnno anno x
    UnsizedExprU x -> liftAnno anno x
    UnsizedExprI x -> liftAnno anno x

instance (Functor f, Annotatable1 f) => Annotatable (Fix f) where
  anno = liftAnno anno . project

instance Annotatable (Cofree g PartialType) where
  anno (a :< _) = pure a

anno1 :: (Annotatable1 f, Annotatable g) => f g -> AnnotateState PartialType
anno1 = liftAnno anno
