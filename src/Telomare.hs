{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ViewPatterns               #-}

module Telomare where

import Control.Applicative (Applicative (liftA2), liftA, liftA3)
import Control.Comonad.Cofree (Cofree ((:<)))
import qualified Control.Comonad.Trans.Cofree as CofreeT (CofreeF (..))
import Control.DeepSeq (NFData (..))
import Control.Lens.Combinators (Plated (..), makePrisms, transform)
import Control.Monad.Except (ExceptT)
import Control.Monad.State (State)
import qualified Control.Monad.State as State
import Data.Bifunctor (Bifunctor (..))
import Data.Bool (bool)
import Data.Char (chr, ord)
import Data.Eq.Deriving (deriveEq1)
import Data.Fix (Fix (..))
import Data.Functor.Classes (Eq1 (..), Eq2 (..), Show1 (..), Show2 (..), eq1,
                             showsUnary1)
import Data.Functor.Foldable (Base, Corecursive (embed),
                              Recursive (cata, project))
import Data.Functor.Foldable.TH (MakeBaseFunctor (makeBaseFunctor))
import Data.GenValidity (GenValid)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ord.Deriving (deriveOrd1)
import qualified Data.Set as Set
import Data.Validity (Validity)
import Data.Void (Void)
import Debug.Trace (trace, traceShow, traceShowId)
import GHC.Generics (Generic, Generic1, Generically1 (..))
import Text.Show.Deriving (deriveShow1)

{- top level TODO list
 - change AbortFrag form to something more convenient
 - extract abort logic from arbitrary expressions (like, make quick dynamic check the way we have static check)
 - make sure recur calls in unsized recursion combinator are structurally smaller ... although, we can fail sizing and report that to user
-}


class BasicBase g where
  embedB :: BasicExprF x -> g x
  extractB :: g x -> Maybe (BasicExprF x)

class StuckBase g where
  embedS :: StuckF x -> g x
  extractS :: g x -> Maybe (StuckF x)

class AbortBase g where
  embedA :: AbortableF x -> g x
  extractA :: g x -> Maybe (AbortableF x)

pattern BasicFW :: BasicBase g => BasicExprF x -> g x
pattern BasicFW x <- (extractB -> Just x)
pattern BasicEE :: (Base g ~ f, BasicBase f, Recursive g) => BasicExprF g -> g
pattern BasicEE x <- (project -> BasicFW x)
pattern StuckFW :: (StuckBase g) => StuckF x -> g x
pattern StuckFW x <- (extractS -> Just x)
pattern StuckEE :: (Base g ~ f, StuckBase f, Recursive g) => StuckF g -> g
pattern StuckEE x <- (project -> StuckFW x)
pattern AbortFW :: AbortBase g => AbortableF x -> g x
pattern AbortFW x <- (extractA -> Just x)
pattern AbortEE :: (Base g ~ f, AbortBase f, Recursive g) => AbortableF g -> g
pattern AbortEE x <- (project -> (AbortFW x))

pattern ZeroB :: (Base g ~ f, BasicBase f, Recursive g) => g
pattern ZeroB <- BasicEE ZeroSF
pattern PairB :: (Base g ~ f, BasicBase f, Recursive g) => g -> g -> g
pattern PairB a b <- BasicEE (PairSF a b)
pattern FillFunction :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g) => g -> g -> f g
pattern FillFunction c e <- StuckFW (SetEnvSF (BasicEE (PairSF c e)))
pattern GateSwitch :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g) => g -> g -> g -> f g
pattern GateSwitch l r s <- FillFunction (StuckEE (GateSF l r)) s
pattern AppEE :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g) => g -> g -> g
pattern AppEE c i <- StuckEE (SetEnvSF (StuckEE (SetEnvSF (BasicEE (PairSF (StuckEE (DeferSF _ (BasicEE (PairSF (StuckEE (LeftSF (StuckEE (RightSF (StuckEE EnvSF))))) (BasicEE (PairSF (StuckEE (LeftSF (StuckEE EnvSF))) (StuckEE (RightSF (StuckEE (RightSF (StuckEE EnvSF))))))))))) (BasicEE (PairSF i c)))))))

basicEE :: (Base g ~ f, BasicBase f, Corecursive g) => BasicExprF g -> g
basicEE = embed . embedB
stuckEE :: (Base g ~ f, StuckBase f, Corecursive g) => StuckF g -> g
stuckEE = embed . embedS
abortEE :: (Base g ~ f, AbortBase f, Corecursive g) => AbortableF g -> g
abortEE = embed . embedA

zeroB :: (Base g ~ f, BasicBase f, Corecursive g) => g
zeroB = basicEE ZeroSF
pairB :: (Base g ~ f, BasicBase f, Corecursive g) => g -> g -> g
pairB a b = basicEE $ PairSF a b
envB :: (Base g ~ f, StuckBase f, Corecursive g) => g
envB = stuckEE EnvSF
setEnvB :: (Base g ~ f, StuckBase f, Corecursive g) => g -> g
setEnvB = stuckEE . SetEnvSF
gateB :: (Base g ~ f, StuckBase f, Corecursive g) => g -> g -> g
gateB l r = stuckEE $ GateSF l r
leftB :: (Base g ~ f, StuckBase f, Corecursive g) => g -> g
leftB = stuckEE . LeftSF
rightB :: (Base g ~ f, StuckBase f, Corecursive g) => g -> g
rightB = stuckEE . RightSF

fillFunction :: (Base g ~ f, BasicBase f, StuckBase f, Corecursive g) => g -> g -> g
fillFunction c e = setEnvB (pairB c e)
gateSwitch :: (Base g ~ f, BasicBase f, StuckBase f, Corecursive g) => g -> g -> g -> g
gateSwitch l r = fillFunction (gateB l r)

abortB :: (Base g ~ f, AbortBase f, Corecursive g) => g
abortB = abortEE AbortF

-- TODO: remove in favor of varB
firstArgB :: (Base g ~ f, BasicBase f, StuckBase f, Corecursive g) => g
firstArgB = leftB envB
secondArgB :: (Base g ~ f, BasicBase f, StuckBase f, Corecursive g) => g
secondArgB = leftB $ rightB envB
thirdArgB :: (Base g ~ f, BasicBase f, StuckBase f, Corecursive g) => g
thirdArgB = leftB . rightB $ rightB envB
fourthArgB :: (Base g ~ f, BasicBase f, StuckBase f, Corecursive g) => g
fourthArgB = leftB . rightB . rightB $ rightB envB
fifthArgB :: (Base g ~ f, BasicBase f, StuckBase f, Corecursive g) => g
fifthArgB = leftB . rightB . rightB . rightB $ rightB envB

varB :: (Base g ~ f, BasicBase f, StuckBase f, Corecursive g) => Int -> g
varB n = if n < 0
  then error $ "varB invalid debruijin index " <> show n
  else leftB (iterate rightB envB !! n)

i2B :: (Base g ~ f, BasicBase f, Corecursive g) => Int -> g
i2B = \case
  0 -> zeroB
  n -> pairB (i2B $ n - 1) zeroB

b2i :: (Base g ~ f, BasicBase f, Recursive g) => g -> Maybe Int
b2i = cata f where
  f = \case
    BasicFW ZeroSF -> Just 0
    BasicFW (PairSF n (Just 0)) -> succ <$> n
    _ -> Nothing

b2s :: forall g f. (Base g ~ f, BasicBase f, Recursive g) => g -> Maybe String
b2s = fmap (fmap chr) . f where
  f = \case
    PairB x xs -> (:) <$> b2i x <*> f xs
    ZeroB -> pure []
    _ -> Nothing

s2b :: forall g f. (Base g ~ f, BasicBase f, Corecursive g) => String -> g
s2b = foldr (pairB . i2B . ord) zeroB

-- note that this doesn't incorporate laziness necessary for things like sizing recursion
iteB_ :: (Base g ~ f, BasicBase f, StuckBase f, Corecursive g) => g -> g -> g -> g
iteB_ i t e = setEnvB $ pairB (gateB e t) i

data BasicExprF f
  = ZeroSF
  | PairSF f f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Eq1 BasicExprF where
  liftEq test a b = case (a,b) of
    (ZeroSF, ZeroSF)         -> True
    (PairSF a b, PairSF c d) -> test a c && test b d
    _                        -> False

instance Show1 BasicExprF where
  liftShowsPrec showsPrec' showList prec = \case
    ZeroSF -> shows "ZeroSF"
    PairSF a b -> shows "PairSF (" . showsPrec' 0 a . shows ", " . showsPrec' 0 b . shows ")"

instance BasicBase BasicExprF where
  embedB = id
  extractB = pure

type BasicExpr = Fix BasicExprF

data StuckF f
  = DeferSF FunctionIndex f
  | EnvSF
  | SetEnvSF f
  | GateSF f f
  | LeftSF f
  | RightSF f
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Show1 StuckF where
  liftShowsPrec showsPrec' showList prec = \case
    DeferSF fi x -> shows "DeferSF " . shows fi . shows " (" . showsPrec' 0 x . shows ")"
    EnvSF -> shows "EnvSF"
    SetEnvSF x -> shows "SetEnvSF (" . showsPrec' 0 x . shows ")"
    GateSF l r -> shows "GateSF (" . showsPrec' 0 l . shows ", " . showsPrec' 0 r . shows ")"
    LeftSF x -> shows "LeftSF (" . showsPrec' 0 x . shows ")"
    RightSF x -> shows "RightSF (" . showsPrec' 0 x . shows ")"
instance Eq1 StuckF where
  liftEq test a b = case (a,b) of
    (DeferSF ix _, DeferSF iy _) | ix == iy -> True -- test a b
    (EnvSF, EnvSF)                          -> True
    (SetEnvSF x, SetEnvSF y)                -> test x y
    (GateSF a b, GateSF c d)                -> test a c && test b d
    (LeftSF x, LeftSF y)                    -> test x y
    (RightSF x, RightSF y)                  -> test x y
    _                                       -> False

newtype FunctionIndex = FunctionIndex { unFunctionIndex :: Int } deriving (Eq, Ord, Enum, Show, Generic)

instance Validity FunctionIndex

-- TODO we can simplify abort semantics to (defer env), and then could do gate x (abort [message] x) for conditional abort
data AbortableF f
  = AbortF
  | AbortedF BasicExpr
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic)

instance Eq1 AbortableF  where
  liftEq test a b = case (a,b) of
    (AbortF, AbortF)                  -> True
    (AbortedF a, AbortedF b) | a == b -> True
    _                                 -> False

instance Show1 AbortableF where
  liftShowsPrec showsPrec showList prec = \case
    AbortF     -> shows "AbortF"
    AbortedF x -> shows "(AbortedF " . shows x . shows ")"

data StuckExprF f
  = StuckExprB (BasicExprF f)
  | StuckExprS (StuckF f)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
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
instance Eq1 StuckExprF where
  liftEq test a b = case (a,b) of
    (StuckExprB x, StuckExprB y) -> liftEq test x y
    (StuckExprS x, StuckExprS y) -> liftEq test x y
    _                            -> False
instance Show1 StuckExprF where
  liftShowsPrec showsPrec showList prec = \case
    StuckExprB x -> liftShowsPrec showsPrec showList prec x
    StuckExprS x -> liftShowsPrec showsPrec showList prec x

type StuckExpr = Fix StuckExprF

data CompiledExprF f
  = CompiledExprB (BasicExprF f)
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

type CompiledExpr = Fix CompiledExprF

newtype UnsizedRecursionToken = UnsizedRecursionToken { unUnsizedRecursionToken :: Int } deriving (Eq, Ord, Show, Enum, NFData, Generic)

instance Validity UnsizedRecursionToken

data SourcePosition = SourcePosition
  { sourcePositionLine   :: Int
  , sourcePositionColumn :: Int
  , sourcePositionOffset :: Int
  }
  deriving (Eq, Show, Ord, Generic, NFData)

instance Validity SourcePosition
instance GenValid SourcePosition

data SourceSpan = SourceSpan
  { sourceSpanFile  :: Maybe FilePath
  , sourceSpanStart :: SourcePosition
  , sourceSpanEnd   :: SourcePosition
  }
  deriving (Eq, Show, Ord, Generic, NFData)

instance Validity SourceSpan
instance GenValid SourceSpan

data LocTag
  = SourceLoc SourceSpan
  | GeneratedLoc String (Maybe LocTag)
  | BuiltinLoc String
  | RuntimeLoc
  | DecompiledLoc
  | UnknownLoc
  deriving (Eq, Show, Ord, Generic, NFData)

instance Validity LocTag
instance GenValid LocTag

data Term3F f
  = Term3B (BasicExprF f)
  | Term3S (StuckF f)
  | Term3A (AbortableF f)
  | Term3Unsized UnsizedRecursionToken
  | Term3CheckingWrapper LocTag f f
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic)
instance BasicBase Term3F where
  embedB = Term3B
  extractB = \case
    Term3B x -> Just x
    _              -> Nothing
instance StuckBase Term3F where
  embedS = Term3S
  extractS = \case
    Term3S x -> Just x
    _ -> Nothing
instance AbortBase Term3F where
  embedA = Term3A
  extractA = \case
    Term3A x -> Just x
    _ -> Nothing
instance Show1 Term3F where
  liftShowsPrec showsPrec' showList prec = \case
    Term3B x -> liftShowsPrec showsPrec' showList prec x
    Term3S x -> liftShowsPrec showsPrec' showList prec x
    Term3A x -> liftShowsPrec showsPrec' showList prec x
    Term3Unsized urt -> shows $ "Term3Unsized" <> show urt
    Term3CheckingWrapper loc cf c -> shows "Term3CheckingWrapper(" . shows loc . shows ", " . showsPrec' 0 cf . shows ", " . showsPrec' 0 c . shows ")"

instance Show o => Show1 (PatternF o) where
  liftShowsPrec showsPrec' showList prec = \case
    PatternVarF s -> showString "PatternVar " . shows s
    PatternAnnotatedF p x -> showString "PatternAnnotated " . showsPrec' 0 p . showChar ' ' . shows x
    PatternIntF x -> showString "PatternInt " . shows x
    PatternStringF s -> showString "PatternString " . shows s
    PatternIgnoreF -> showString "PatternIgnore"
    PatternPairF a b -> showString "PatternPair " . showsPrec' 0 a . showChar ' ' . showsPrec' 0 b

instance Show p => Show1 (UnprocessedParsedTermF p) where
  liftShowsPrec showsPrecFunc showList d term = case term of
    ImportQualifiedUPF s1 s2 -> showString "ImportQualifedUPF " . shows s1 . showString " " . shows s2
    ImportUPF s -> showString "ImportUPF " . shows s
    VarUPF s -> showString "VarUPF " . shows s
    ITEUPF c t e -> showString "ITEUPF " . showsPrecFunc 11 c . showChar ' '
                    . showsPrecFunc 11 t . showChar ' ' . showsPrecFunc 11 e
    LetUPF bindings body ->
      let showBinding (str, x) = showChar '(' . shows (locatedNameText str) . showString ", "
                                 . showsPrecFunc 11 x . showChar ')'
          showBindings bs = showChar '[' . foldr1 (\a b -> a . showString ", " . b)
                           (fmap showBinding bs) . showChar ']'
      in showString "LetUPF " . showBindings bindings . showChar ' ' . showsPrecFunc 11 body
    ListUPF terms -> showString "ListUPF [" .
                     foldr1 (\a b -> a . showString ", " . b)
                           (fmap (showsPrecFunc 11) terms) .
                     showChar ']'
    IntUPF n -> showString "IntUPF " . shows n
    StringUPF s -> showString "StringUPF " . shows s
    PairUPF a b -> showString "PairUPF " . showsPrecFunc 11 a . showChar ' '
                   . showsPrecFunc 11 b
    AppUPF f x -> showString "AppUPF " . showsPrecFunc 11 f . showChar ' '
                  . showsPrecFunc 11 x
    LamUPF var body -> showString "LamUPF " . shows (locatedNameText var) . showChar ' '
                       . showsPrecFunc 11 body
    ChurchUPF n -> showString "ChurchUPF " . shows n
    UnsizedRecursionUPF a b c -> showString "UnsizedRecursionUPF "
                                 . showsPrecFunc 11 a . showChar ' '
                                 . showsPrecFunc 11 b . showChar ' '
                                 . showsPrecFunc 11 c
    LeftUPF x -> showString "LeftUPF " . showsPrecFunc 11 x
    RightUPF x -> showString "RightUPF " . showsPrecFunc 11 x
    TraceUPF x -> showString "TraceUPF " . showsPrecFunc 11 x
    CheckUPF a b -> showString "CheckUPF " . showsPrecFunc 11 a . showChar ' '
                    . showsPrecFunc 11 b
    HashUPF x -> showString "HashUPF " . showsPrecFunc 11 x
    UDTUPF ss x -> showString "UDTUPF " . shows ss . showChar ' ' . showsPrecFunc 11 x
    CaseUPF scrutinee patterns ->
      let showPattern (pat, x) = showChar '(' . shows pat . showString ", "
                                . showsPrecFunc 11 x . showChar ')'
          showPatterns ps = showChar '[' . foldr1 (\a b -> a . showString ", " . b)
                           (fmap showPattern patterns) . showChar ']'
      in showString "CaseUPF " . showsPrecFunc 11 scrutinee . showChar ' '
         . showPatterns patterns

-- |AST for patterns in `case` expressions
data PatternF t f
  = PatternVarF String
  | PatternAnnotatedF f t
  | PatternIntF Int
  | PatternStringF String
  | PatternIgnoreF
  | PatternPairF f f
  deriving (Show, Eq, Functor, Foldable, Traversable, Generic1)
  deriving Eq1 via (Generically1 (PatternF t))

-- |Firstly parsed AST sans location annotations
data UnprocessedParsedTermF p f
  = VarUPF String
  | ITEUPF f f f
  | LetUPF [(LocatedName, f)] f
  | ListUPF [f]
  | IntUPF Int
  | StringUPF String
  | PairUPF f f
  | AppUPF f f
  | LamUPF LocatedName f
  | ChurchUPF Int
  | UnsizedRecursionUPF f f f
  | LeftUPF f
  | RightUPF f
  | TraceUPF f
  | CheckUPF f f
  | HashUPF f -- ^ On ad hoc user defined types, this term will be substitued to a unique Int.
  | UDTUPF [String] f
  | CaseUPF f [(p, f)]
  -- TODO: check if adding this doesn't create partial functions
  | ImportQualifiedUPF String String
  | ImportUPF String
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic1)
  deriving Eq1 via (Generically1 (UnprocessedParsedTermF p))

type Pattern = Fix (PatternF UnprocessedParsedTerm)
newtype UnprocessedParsedTerm = UnprocessedParsedTerm { unUnprocessedParsedTerm :: Fix (UnprocessedParsedTermF Pattern)}

-- | Lambdas can be closed if it's expresion does not depend on any
--   outer binding.
data LamType l
  = Open l
  | Closed l
  | LetBinding Int l
  deriving (Eq, Show, Ord)



-- | Parser AST
data ParserTermF l v f
  = ParserTermB (BasicExprF f)
  | TVarF v
  | TAppF f f
  | TCheckF f f
  | TITEF f f f
  | TLeftF f
  | TRightF f
  | TTraceF f
  | THashF f
  | TChurchF Int
  | TLamF (LamType l) f
  | TLimitedRecursionF f f f
  | TUnsizedRepeaterF
  deriving (Functor, Foldable, Traversable)
deriving instance (Show l, Show v, Show a) => Show (ParserTermF l v a)
deriving instance (Show l, Show v) => Show1 (ParserTermF l v)
instance BasicBase (ParserTermF l v) where
  embedB = ParserTermB
  extractB = \case
    ParserTermB x -> Just x
    _              -> Nothing
instance Show l => Show2 (ParserTermF l) where
  liftShowsPrec2 showsPrecA showListA showsPrecB showListB prec = \case
    TVarF v -> shows "TVarF " . showsPrecA 0 v
    ParserTermB x -> shows "ParserTermB (" . liftShowsPrec showsPrecB showListB 0 x . shows ")"
    TAppF c i -> shows "TAppF (" . showsPrecB 0 c . shows " " . showsPrecB 0 i . shows ")"
    TCheckF cf c -> shows "TCheckF( " . showsPrecB 0 cf . shows ": " . showsPrecB 0 c . shows ")"
    TITEF i t e -> shows "( " . showsPrecB 0 i . shows " ? " . showsPrecB 0 t . shows " : " . showsPrecB 0 e . shows " )"
    TLeftF x -> shows "TLeftF (" . showsPrecB 0 x . shows ")"
    TRightF x -> shows "TRightF (" . showsPrecB 0 x . shows ")"
    TTraceF x -> shows "TTraceF (" . showsPrecB 0 x . shows ")"
    THashF x -> shows "THashF (" . showsPrecB 0 x . shows ")"
    TChurchF n -> shows "TChurchF " . shows n
    TLamF t x -> shows "TLamF " . shows t . shows " (" . showsPrecB 0 x . shows ")"
    TLimitedRecursionF t r b -> shows "{" . showsPrecB 0 t . shows ", " . showsPrecB 0 r . shows ", " . showsPrecB 0 b . shows "}"
    TUnsizedRepeaterF -> shows "TUnsizedRepeaterF"

deriving instance (Eq l, Eq v, Eq a) => Eq (ParserTermF l v a)
instance Eq l => Eq2 (ParserTermF l) where
  liftEq2 eqv eqa (BasicFW ZeroSF) (BasicFW ZeroSF) = True
  liftEq2 eqv eqa (BasicFW (PairSF x1 y1)) (BasicFW (PairSF x2 y2)) = eqa x1 x2 && eqa y1 y2
  liftEq2 eqv eqa (TVarF v1) (TVarF v2) = eqv v1 v2
  liftEq2 eqv eqa (TAppF x1 y1) (TAppF x2 y2) = eqa x1 x2 && eqa y1 y2
  liftEq2 eqv eqa (TCheckF x1 y1) (TCheckF x2 y2) = eqa x1 x2 && eqa y1 y2
  liftEq2 eqv eqa (TITEF c1 t1 e1) (TITEF c2 t2 e2) = eqa c1 c2 && eqa t1 t2 && eqa e1 e2
  liftEq2 eqv eqa (TLeftF x1) (TLeftF x2) = eqa x1 x2
  liftEq2 eqv eqa (TRightF x1) (TRightF x2) = eqa x1 x2
  liftEq2 eqv eqa (TTraceF x1) (TTraceF x2) = eqa x1 x2
  liftEq2 eqv eqa (THashF x1) (THashF x2) = eqa x1 x2
  liftEq2 eqv eqa (TChurchF n1) (TChurchF n2) = n1 == n2
  liftEq2 eqv eqa (TLamF l1 x1) (TLamF l2 x2) = l1 == l2 && eqa x1 x2
  liftEq2 eqv eqa (TLimitedRecursionF a1 b1 c1) (TLimitedRecursionF a2 b2 c2) =
    eqa a1 a2 && eqa b1 b2 && eqa c1 c2
  liftEq2 _ _ TUnsizedRepeaterF TUnsizedRepeaterF = True
  liftEq2 _ _ _ _ = False
deriving instance (Eq l, Eq v) => Eq1 (ParserTermF l v)
deriving instance (Ord l, Ord v, Ord a) => Ord (ParserTermF l v a)


-- |Helper function to indent. Usefull for indented Show instances.
indent :: Int -> String -> String
indent i str = replicate i ' ' <> str

-- |Indentation with the State Monad.
sindent :: String -> State Int String
sindent str = State.get >>= (\i -> pure $ indent i str)

-- |One child indentation.
indentWithOneChild :: String -> State Int String -> State Int String
indentWithOneChild str sx = do
  i <- State.get
  State.put $ i + 2
  x <- sx
  pure $ indent i (str <> "\n") <> x

indentWithOneChild' :: String -> State Int String -> State Int String
indentWithOneChild' str sx = do
  i <- State.get
  let sout = str <> " "
  State.put $ i + length sout
  x <- sx
  pure $ sout <> x

indentWithTwoChildren' :: String -> State Int String -> State Int String -> State Int String
indentWithTwoChildren' str sl sr = do
  i <- State.get
  let sout = str <> " "
      newl = i + length sout
  State.put newl
  l <- sl
  State.put newl
  r <- sr
  pure $ sout <> l <> "\n" <> indent newl r

indentWithChildren' :: String -> [State Int String] -> State Int String
indentWithChildren' str l = do
  i <- State.get
  let sout = str <> " "
      newl = i + length sout
  let doLine = fmap (<> "\n" <> indent newl "") . (State.put newl >>)
  foldl (\s c -> (<>) <$> s <*> c) (pure sout) $ fmap doLine l

-- TODO replace with above version
-- |Two children indentation.
indentWithTwoChildren :: String -> State Int String -> State Int String -> State Int String
indentWithTwoChildren str sl sr = do
  i <- State.get
  State.put $ i + 2
  l <- sl
  State.put $ i + 2
  r <- sr
  pure $ indent i (str <> "\n") <> l <> "\n" <> r

-- TODO replace with other version
indentWithThreeChildren :: String -> State Int String -> State Int String -> State Int String -> State Int String
indentWithThreeChildren str sa sb sc = do
  i <- State.get
  State.put $ i + 2
  a <- sa
  State.put $ i + 2
  b <- sb
  State.put $ i + 2
  c <- sc
  pure $ indent i (str <> "\n") <> a <> "\n" <> b <> "\n" <> c

-- |`dropUntil p xs` drops leading elements until `p $ head xs` is satisfied.
dropUntil :: (a -> Bool) -> [a] -> [a]
dropUntil _ [] = []
dropUntil p x@(x1:_) =
  if p x1 then x else dropUntil p (drop 1 x)

locStartLineColumn :: LocTag -> Maybe (Int, Int)
locStartLineColumn = \case
  SourceLoc span ->
    let start = sourceSpanStart span
    in Just (sourcePositionLine start, sourcePositionColumn start)
  GeneratedLoc _ parent -> parent >>= locStartLineColumn
  _ -> Nothing

renderLocTag :: LocTag -> Maybe String
renderLocTag loc = case locStartLineColumn loc of
  Just (line, column) -> Just $ "line " <> show line <> ", column " <> show column
  Nothing             -> Nothing

renderLocTagVerbose :: LocTag -> String
renderLocTagVerbose loc = case (loc, renderLocTag loc) of
  (GeneratedLoc reason _, Just rendered) -> rendered <> " (generated by " <> reason <> ")"
  (GeneratedLoc reason Nothing, _)       -> "generated by " <> reason
  (BuiltinLoc name, _)                   -> "builtin " <> show name
  (RuntimeLoc, _)                        -> "runtime value"
  (DecompiledLoc, _)                     -> "decompiled value"
  (UnknownLoc, _)                        -> "unknown location"
  (_, Just rendered)                     -> rendered
  (_, Nothing)                           -> "unknown location"

type Term1 = Cofree (ParserTermF String String) LocTag
type Term2 = Cofree (ParserTermF () Int) LocTag
type Term3 = Cofree Term3F LocTag

data TypeCheckError
  = UnboundType Int
  | InconsistentTypes PartialType PartialType
  | RecursiveType Int
  deriving (Eq, Ord, Show)

data ResolverError
  = NoMainFunction String
  | ModuleNotFound String
  | DefinitionCycle [String]
  | MissingDefinitions [String]
  | MissingDefinitionAt LocTag String
  | ParseError String
  deriving (Eq, Ord)

instance Show ResolverError where
  showsPrec d err = showParen (d > 10) $ showString (renderResolverError err)

renderResolverError :: ResolverError -> String
renderResolverError = \case
  NoMainFunction moduleName -> "NoMainFunction " <> show moduleName
  ModuleNotFound moduleName -> "ModuleNotFound " <> show moduleName
  DefinitionCycle names -> "DefinitionCycle " <> show names
  MissingDefinitions names -> "MissingDefinitions " <> show names
  MissingDefinitionAt loc name ->
    "missing definition " <> show name <> " at " <> renderLocTagVerbose loc
  ParseError err -> "ParseError " <> show err

data EvalError = RTE RunTimeError
    | TCE TypeCheckError
    | RE ResolverError
    | StaticCheckError String
    | CompileConversionError
    | RecursionLimitError UnsizedRecursionToken
    deriving (Eq, Show)

data RunTimeError
  = AbortRunTime BasicExpr
  | GenericRunTimeError String CompiledExpr
  | ResultConversionError String
  deriving (Eq)

instance Show RunTimeError where
  show (AbortRunTime a) = "Aborted, " <> convertAbortMessage a
  show (GenericRunTimeError s i) = "Generic Runtime Error: " <> s <> " -- " <> show i
  show (ResultConversionError s) = "Couldn't convert runtime result to IExpr: " <> s

-- type RunResult = ExceptT RunTimeError IO

class TelomareLike a where
  fromTelomare :: StuckExpr -> a
  toTelomare :: a -> Maybe StuckExpr

class TelomareLike a => AbstractRunTime a where
  eval :: a -> Either RunTimeError a

instance TelomareLike StuckExpr where
  fromTelomare = id
  toTelomare = pure

instance BasicBase f => BasicBase (CofreeT.CofreeF f LocTag) where
  embedB = (GeneratedLoc "BasicBase Cofree instance" Nothing CofreeT.:<) . embedB
  extractB = extractB . (\(_ CofreeT.:< x) -> x)

instance StuckBase f => StuckBase (CofreeT.CofreeF f LocTag) where
  embedS = (GeneratedLoc "StuckBase Cofree instance" Nothing CofreeT.:<) . embedS
  extractS = extractS . (\(_ CofreeT.:< x) -> x)

instance AbortBase f => AbortBase (CofreeT.CofreeF f LocTag) where
  embedA = (GeneratedLoc "AbortBase Cofree instance" Nothing CofreeT.:<) . embedA
  extractA = extractA . (\(_ CofreeT.:< x) -> x)

type Term3Builder = State (FunctionIndex, UnsizedRecursionToken)

buildTerm :: (Corecursive g) => Term3Builder g -> g
buildTerm = flip State.evalState (toEnum 0, toEnum 0)

deferS :: (Base g ~ f, StuckBase f, Corecursive g) => g -> Term3Builder g
deferS x = do
  fi <- State.gets fst
  State.modify (\(_, urt) -> (succ fi, urt))
  pure . stuckEE $ DeferSF fi x

pairS :: (Base g ~ CofreeT.CofreeF f a, BasicBase f, Recursive g, Corecursive g, Monad m) => m g -> m g -> m g
pairS a b = do
  a' <- a
  b' <- b
  let l CofreeT.:< _ = project a'
  pure . embed $ l CofreeT.:< embedB (PairSF a' b')

clamS :: forall g f. (Base g ~ CofreeT.CofreeF f LocTag, StuckBase f, BasicBase f, Recursive g, Corecursive g)
  => Term3Builder g -> Term3Builder g
clamS x = pairS (x >>= deferS) $ pure zeroB

lamS :: forall g f. (Base g ~ CofreeT.CofreeF f LocTag, StuckBase f, BasicBase f, Recursive g, Corecursive g)
  => Term3Builder g -> Term3Builder g
lamS x = pairS (x >>= deferS) $ pure envB

twiddleS :: forall g f. (Base g ~ CofreeT.CofreeF f LocTag, StuckBase f, BasicBase f, Corecursive g) => Term3Builder g
twiddleS = deferS . pairB (leftB $ rightB envB) . pairB (leftB envB) $ rightB (rightB envB)

appS :: forall g f. (Base g ~ CofreeT.CofreeF f LocTag, StuckBase f, BasicBase f, Recursive g, Corecursive g)
  => Term3Builder g -> Term3Builder g -> Term3Builder g
appS c i = setEnvB . setEnvB <$> pairS twiddleS (pairS i c)

-- inside three lambdas (\r f x -> ...)
-- r is the repeater function
-- creates and iterates on a function "frame" (rf, (rf, (f', (x, env'))))
-- rf is the function to pull arguments out of the frame, run f', and construct the next frame
-- (f',env') is f (since f may contain a saved environment/closure env we want to use for each iteration)
repeatFunctionS :: LocTag -> Term3Builder Term3
repeatFunctionS l =
  let applyF = setEnvB $ rightB envB
      env' = rightB . rightB $ rightB envB
      -- takes (rf, (f', (x, env'))), executes f' with (x, env') and creates a new frame
      rf = deferS $ pairB (leftB envB)
                          (pairB (leftB envB)
                                 (pairB (leftB (rightB envB))
                                        (pairB applyF env')))
      r = leftB . leftB . rightB $ rightB envB
      x = leftB envB
      f' = leftB . leftB $ rightB envB
      fenv = rightB . leftB $ rightB envB
      -- (r, (x, ((f', fenv), 0))) -> (rf, (rf, (f', (x, fenv))))
      frameSetup = pairS rf (pairS rf (pure $ pairB f' (pairB x fenv)))
  in clamS . lamS . lamS $ setEnvB <$> pairS (pure r) frameSetup

unsizedRepeater :: LocTag -> UnsizedRecursionToken -> Term3Builder Term3
unsizedRepeater l tok = clamS . pure . leftB . rightB . rightB . rightB . embed $ l CofreeT.:< Term3Unsized tok

repeaterAndAbort :: LocTag -> UnsizedRecursionToken -> Term3Builder Term3
repeaterAndAbort l tok = pairS (unsizedRepeater l tok) abrt where
  -- args are (i, (b, ...)) since trb is on the stack
  abrt = (>>= deferS) $ setEnvB . pairB (setEnvB $ pairB abortB abortToken) <$> appS (pure secondArgB) (pure firstArgB)
  abortToken = pairB zeroB . i2B $ fromEnum tok

-- to construct a church numeral (\f x -> f ... (f x))
-- the core is nested setenvs around an env, where the number of setenvs is magnitude of church numeral
i2CB :: LocTag -> Int -> Term3Builder Term3
i2CB l n = appS (repeatFunctionS l) . clamS . pure . leftB . rightB . rightB . rightB $ iterate setEnvB envB !! n

-- function is called with (r,a), where r is the repeating function, and a is the abort function
unsizedRecursionWrapper :: LocTag -> Term3Builder Term3 -> Term3Builder Term3 -> Term3Builder Term3 -> Term3Builder Term3
unsizedRecursionWrapper loc t r b =
  let repeater = leftB $ leftB envB
      abrt = pairB (rightB $ leftB envB) envB
      -- drop first arg (repeater)
      nsLamS :: Term3Builder Term3 -> Term3Builder Term3
      nsLamS x = pairS (x >>= deferS) (pure $ rightB envB)
      -- \t r b r' i -> if t i then r r' i else b i -- t r b are already on the stack when this is evaluated
      rWrap = nsLamS . lamS $ iteB_ <$> appS (pure fifthArgB) (pure firstArgB)
                                    <*> appS (appS (pure fourthArgB) (pure secondArgB)) (pure firstArgB)
                                    <*> appS (pure thirdArgB) (pure firstArgB)
      -- hack to make sure recursion test wrapper can be put in a definite place when sizing
      tWrap = pairS ((>>= deferS) (appS (pure secondArgB) (pure firstArgB))) (pairS t $ pure zeroB)
      trb = pairS b . pairS r . pairS tWrap $ pure zeroB
  in pairS (appS (appS (appS (repeatFunctionS loc) (pure repeater)) rWrap) (pure abrt) >>= deferS) trb

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

data PartialType
  = ZeroTypeP
  | AnyType
  | TypeVariable LocTag Int
  | ArrTypeP PartialType PartialType
  | PairTypeP PartialType PartialType
  deriving (Show, Eq, Ord, Generic)

instance Plated PartialType where
  plate f = \case
    ArrTypeP i o  -> ArrTypeP <$> f i <*> f o
    PairTypeP a b -> PairTypeP <$> f a <*> f b
    x             -> pure x

instance Validity PartialType
instance GenValid PartialType

toPartialType :: DataType -> PartialType
toPartialType = \case
  ZeroType -> ZeroTypeP
  ArrType i o -> ArrTypeP (toPartialType i) (toPartialType o)
  PairType a b -> PairTypeP (toPartialType a) (toPartialType b)

mergePairType :: DataType -> DataType
mergePairType = transform f where
  f (PairType ZeroType ZeroType) = ZeroType
  f x                            = x

mergePairTypeP :: PartialType -> PartialType
mergePairTypeP = transform f where
  f (PairTypeP ZeroTypeP ZeroTypeP) = ZeroTypeP
  f x                               = x

containsFunction :: PartialType -> Bool
containsFunction = \case
  ArrTypeP _ _  -> True
  PairTypeP a b -> containsFunction a || containsFunction b
  _             -> False

cleanType :: PartialType -> Bool
cleanType = \case
  ZeroTypeP     -> True
  PairTypeP a b -> cleanType a && cleanType b
  _             -> False

forget :: Corecursive a => Cofree (Base a) anno -> a
forget = cata (\(_ CofreeT.:< z) -> embed z)

tag :: Recursive a => anno -> a -> Cofree (Base a) anno
tag anno x = anno :< (tag anno <$> project x)


convertBasic :: (BasicBase g, BasicBase h, Base x ~ h, Corecursive x, Monad m) => (g (m x) -> m x) -> g (m x) -> m x
convertBasic convertOther = \case
  BasicFW x -> basicEE <$> sequence x
  x -> convertOther x
convertStuck :: (StuckBase g, StuckBase h, Base x ~ h, Corecursive x, Monad m) => (g (m x) -> m x) -> g (m x) -> m x
convertStuck convertOther = \case
  StuckFW x -> stuckEE <$> sequence x
  x -> convertOther x
convertAbort :: (AbortBase g, AbortBase h, Base x ~ h, Corecursive x, Monad m) => (g (m x) -> m x) -> g (m x) -> m x
convertAbort convertOther = \case
  AbortFW x -> abortEE <$> sequence x
  x -> convertOther x

instance TelomareLike Term3 where
  fromTelomare = verify . cata (convertBasic (convertStuck (\z -> Left "failed converting to Term3"))) where
    verify = \case
      Right x -> x
      Left e -> error e
  toTelomare = cata f . forget' where
    forget' :: Term3 -> Fix Term3F
    forget' = forget
    f = \case
      Term3Unsized _ -> Nothing
      Term3CheckingWrapper _ _ _ -> Nothing
      Term3A _ -> Nothing
      Term3B b -> embed . StuckExprB <$> sequence b
      Term3S s -> embed . StuckExprS <$> sequence s

-- general utility functions

insertAndGetKey :: (Ord e, Enum e) => a -> State (Map e a) e
insertAndGetKey v = do
  m <- State.get
  let nextKey = case Set.lookupMax $ Map.keysSet m of
        Nothing -> toEnum 0
        Just n  -> succ n
  State.put $ Map.insert nextKey v m
  pure nextKey

pattern AbortRecursion :: (Base g ~ f, BasicBase f, Recursive g) => g -> g
pattern AbortRecursion t <- PairB ZeroB t
pattern AbortUser :: (Base g ~ f, BasicBase f, Recursive g) => g -> g
pattern AbortUser m  <- PairB (PairB ZeroB ZeroB) m
pattern AbortAny :: (Base g ~ f, BasicBase f, Recursive g) => g
pattern AbortAny <- PairB (PairB (PairB ZeroB ZeroB) ZeroB) ZeroB
pattern AbortUnsizeable :: (Base g ~ f, BasicBase f, Recursive g) => g -> g
pattern AbortUnsizeable t <- PairB (PairB (PairB (PairB ZeroB ZeroB) ZeroB) ZeroB) t

abortRecursion :: (Base g ~ f, BasicBase f, Corecursive g) => g -> g
abortRecursion = pairB zeroB
abortUser :: (Base g ~ f, BasicBase f, Corecursive g) => g -> g
abortUser = pairB (pairB zeroB zeroB)
abortAny :: (Base g ~ f, BasicBase f, Corecursive g) => g
abortAny = pairB (pairB (pairB zeroB zeroB) zeroB) zeroB
abortUnsizeable :: (Base g ~ f, BasicBase f, Corecursive g) => g -> g
abortUnsizeable = pairB (pairB (pairB (pairB zeroB zeroB) zeroB) zeroB)

convertAbortMessage :: (Base g ~ f, BasicBase f, Recursive g, Show g) => g -> String
convertAbortMessage = \case
  AbortRecursion t -> "recursion overflow (should be caught by other means) for rt: " <> show (b2i t)
  AbortUser s -> case b2s s of
    Nothing -> "user abort invalid data: " <> show s
    Just m  -> "user abort: " <> m
  AbortAny -> "user abort of all possible abort reasons (non-deterministic input)"
  x -> "unexpected abort: " <> show x

newtype LocatedName = LocatedName (LocTag, String)
  deriving (Eq, Ord, Show)

locatedNameLoc :: LocatedName -> LocTag
locatedNameLoc (LocatedName (loc, _)) = loc

locatedNameText :: LocatedName -> String
locatedNameText (LocatedName (_, name)) = name

locatedName :: LocTag -> String -> LocatedName
locatedName loc name = LocatedName (loc, name)

letBindingName :: (LocatedName, a) -> String
letBindingName (name, _) = locatedNameText name

letBindingValue :: (LocatedName, a) -> a
letBindingValue (_, value) = value

letBindingLoc :: (LocatedName, a) -> LocTag
letBindingLoc (name, _) = locatedNameLoc name

pattern AppUP :: UnprocessedParsedTerm -> UnprocessedParsedTerm -> UnprocessedParsedTerm
pattern AppUP f i <- UnprocessedParsedTerm (Fix (AppUPF (UnprocessedParsedTerm -> f) (UnprocessedParsedTerm -> i))) where
  AppUP f i = UnprocessedParsedTerm (Fix (AppUPF (unUnprocessedParsedTerm f) (unUnprocessedParsedTerm i)))
pattern ITEUP :: UnprocessedParsedTerm -> UnprocessedParsedTerm -> UnprocessedParsedTerm -> UnprocessedParsedTerm
pattern ITEUP i t e <- UnprocessedParsedTerm (Fix (ITEUPF (UnprocessedParsedTerm -> i) (UnprocessedParsedTerm -> t) (UnprocessedParsedTerm -> e))) where
  ITEUP i t e = UnprocessedParsedTerm (Fix (ITEUPF (unUnprocessedParsedTerm i) (unUnprocessedParsedTerm t) (unUnprocessedParsedTerm e)))
pattern VarUP :: String -> UnprocessedParsedTerm
pattern VarUP s <- UnprocessedParsedTerm (Fix (VarUPF s)) where
  VarUP s = UnprocessedParsedTerm (Fix (VarUPF s))
pattern LetUP :: [(LocatedName, UnprocessedParsedTerm)] -> UnprocessedParsedTerm -> UnprocessedParsedTerm
pattern LetUP binds body <- UnprocessedParsedTerm (Fix (LetUPF (fmap (second UnprocessedParsedTerm) -> binds) (UnprocessedParsedTerm -> body))) where
  LetUP binds body = UnprocessedParsedTerm (Fix (LetUPF (fmap (second unUnprocessedParsedTerm) binds) (unUnprocessedParsedTerm body)))
pattern ListUP :: [UnprocessedParsedTerm] -> UnprocessedParsedTerm
pattern ListUP items <- UnprocessedParsedTerm (Fix (ListUPF (fmap UnprocessedParsedTerm -> items))) where
  ListUP items = UnprocessedParsedTerm (Fix (ListUPF (fmap unUnprocessedParsedTerm items)))
pattern IntUP :: Int -> UnprocessedParsedTerm
pattern IntUP n <- UnprocessedParsedTerm (Fix (IntUPF n)) where
  IntUP n = UnprocessedParsedTerm (Fix (IntUPF n))
pattern StringUP :: String -> UnprocessedParsedTerm
pattern StringUP s <- UnprocessedParsedTerm (Fix (StringUPF s)) where
  StringUP s = UnprocessedParsedTerm (Fix (StringUPF s))
pattern PairUP :: UnprocessedParsedTerm -> UnprocessedParsedTerm -> UnprocessedParsedTerm
pattern PairUP a b <- UnprocessedParsedTerm (Fix (PairUPF (UnprocessedParsedTerm -> a) (UnprocessedParsedTerm -> b))) where
  PairUP a b = UnprocessedParsedTerm (Fix (PairUPF (unUnprocessedParsedTerm a) (unUnprocessedParsedTerm b)))
pattern LamUP :: LocatedName -> UnprocessedParsedTerm -> UnprocessedParsedTerm
pattern LamUP v body <- UnprocessedParsedTerm (Fix (LamUPF v (UnprocessedParsedTerm -> body))) where
  LamUP v body = UnprocessedParsedTerm (Fix (LamUPF v (unUnprocessedParsedTerm body)))
pattern ChurchUP :: Int -> UnprocessedParsedTerm
pattern ChurchUP n <- UnprocessedParsedTerm (Fix (ChurchUPF n)) where
  ChurchUP n = UnprocessedParsedTerm (Fix (ChurchUPF n))
pattern UnsizedRecursionUP :: UnprocessedParsedTerm -> UnprocessedParsedTerm -> UnprocessedParsedTerm -> UnprocessedParsedTerm
pattern UnsizedRecursionUP t r b <- UnprocessedParsedTerm (Fix (UnsizedRecursionUPF (UnprocessedParsedTerm -> t) (UnprocessedParsedTerm -> r) (UnprocessedParsedTerm -> b))) where
  UnsizedRecursionUP t r b = UnprocessedParsedTerm (Fix (UnsizedRecursionUPF (unUnprocessedParsedTerm t) (unUnprocessedParsedTerm r) (unUnprocessedParsedTerm b)))
pattern LeftUP :: UnprocessedParsedTerm -> UnprocessedParsedTerm
pattern LeftUP x <- UnprocessedParsedTerm (Fix (LeftUPF (UnprocessedParsedTerm -> x))) where
  LeftUP x = UnprocessedParsedTerm (Fix (LeftUPF (unUnprocessedParsedTerm x)))
pattern RightUP :: UnprocessedParsedTerm -> UnprocessedParsedTerm
pattern RightUP x <- UnprocessedParsedTerm (Fix (RightUPF (UnprocessedParsedTerm -> x))) where
  RightUP x = UnprocessedParsedTerm (Fix (RightUPF (unUnprocessedParsedTerm x)))
pattern TraceUP :: UnprocessedParsedTerm -> UnprocessedParsedTerm
pattern TraceUP x <- UnprocessedParsedTerm (Fix (TraceUPF (UnprocessedParsedTerm -> x))) where
  TraceUP x = UnprocessedParsedTerm (Fix (TraceUPF (unUnprocessedParsedTerm x)))
pattern HashUP :: UnprocessedParsedTerm -> UnprocessedParsedTerm
pattern HashUP x <- UnprocessedParsedTerm (Fix (HashUPF (UnprocessedParsedTerm -> x))) where
  HashUP x = UnprocessedParsedTerm (Fix (HashUPF (unUnprocessedParsedTerm x)))
pattern CaseUP :: UnprocessedParsedTerm -> [(Fix (PatternF UnprocessedParsedTerm), UnprocessedParsedTerm)] -> UnprocessedParsedTerm
pattern CaseUP scrutinee alts <- UnprocessedParsedTerm (Fix (CaseUPF (UnprocessedParsedTerm -> scrutinee) (fmap (second UnprocessedParsedTerm) -> alts))) where
  CaseUP scrutinee alts = UnprocessedParsedTerm (Fix (CaseUPF (unUnprocessedParsedTerm scrutinee) (fmap (second unUnprocessedParsedTerm) alts)))
pattern ImportUP :: String -> UnprocessedParsedTerm
pattern ImportUP s <- UnprocessedParsedTerm (Fix (ImportUPF s)) where
  ImportUP s = UnprocessedParsedTerm (Fix (ImportUPF s))
pattern ImportQualifiedUP :: String -> String -> UnprocessedParsedTerm
pattern ImportQualifiedUP m a <- UnprocessedParsedTerm (Fix (ImportQualifiedUPF m a)) where
  ImportQualifiedUP m a = UnprocessedParsedTerm (Fix (ImportQualifiedUPF m a))
