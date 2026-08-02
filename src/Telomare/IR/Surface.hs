{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TypeFamilies      #-}

-- |The surface AST: what the parser produces. 'UnprocessedParsedTermF'
-- composes the shared base functors with the surface-only forms (let, list,
-- case, imports, UDT declarations). 'AUPT' is the location-annotated
-- variant every later stage consumes.
module Telomare.IR.Surface where

import Control.Comonad.Cofree (Cofree ((:<)))
import qualified Control.Comonad.Trans.Cofree as CofreeT (CofreeF (..))
import Data.Fix (Fix (..))
import Data.Functor.Classes (Eq1 (..), Show1 (..))
import GHC.Generics (Generic1, Generically1 (..))
import Telomare.IR.Base (BasicBase (..), BasicExprF (..), CarryAnno (..),
                         HighBase (..), HighTermF (..), LamBase (..),
                         LamTermF (..))
import Telomare.IR.Loc (LocTag, LocatedName, locatedNameText)

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

instance Show o => Show1 (PatternF o) where
  liftShowsPrec showsPrec' showList prec = \case
    PatternVarF s -> showString "PatternVar " . shows s
    PatternAnnotatedF p x -> showString "PatternAnnotated " . showsPrec' 0 p . showChar ' ' . shows x
    PatternIntF x -> showString "PatternInt " . shows x
    PatternStringF s -> showString "PatternString " . shows s
    PatternIgnoreF -> showString "PatternIgnore"
    PatternPairF a b -> showString "PatternPair " . showsPrec' 0 a . showChar ' ' . showsPrec' 0 b

-- |Firstly parsed AST
data UnprocessedParsedTermF p f
  = UnprocessedParsedTermH (HighTermF f)
  | UnprocessedParsedTermL (LamTermF LocatedName String f)
  | UnprocessedParsedTermB (BasicExprF f)
  | LetUPF [(LocatedName, f)] f
  | ListUPF [f]
  | IntUPF Int
  | StringUPF String
  | UDTUPF [String] f
  | CaseUPF f [(p, f)]
  -- TODO: check if adding this doesn't create partial functions
  | ImportQualifiedUPF String String
  | ImportUPF String
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic1)
  deriving Eq1 via (Generically1 (UnprocessedParsedTermF p))
instance HighBase (UnprocessedParsedTermF p) where
  embedH = UnprocessedParsedTermH
  extractH = \case
    UnprocessedParsedTermH x -> Just x
    _                        -> Nothing
instance BasicBase (UnprocessedParsedTermF p) where
  embedB = UnprocessedParsedTermB
  extractB = \case
    UnprocessedParsedTermB x -> Just x
    _                        -> Nothing
instance LamBase (UnprocessedParsedTermF p) where
  type LamVar (UnprocessedParsedTermF p) = String
  type LamT (UnprocessedParsedTermF p) = LocatedName

  embedL = UnprocessedParsedTermL
  extractL = \case
    UnprocessedParsedTermL x -> Just x
    _                        -> Nothing

instance (Show p) => Show1 (UnprocessedParsedTermF p) where
  liftShowsPrec showsPrecFunc showList d term = case term of

    UnprocessedParsedTermB x -> liftShowsPrec showsPrecFunc showList d x
    UnprocessedParsedTermH x -> liftShowsPrec showsPrecFunc showList d x
    UnprocessedParsedTermL x -> liftShowsPrec showsPrecFunc showList d x
    ImportQualifiedUPF s1 s2 -> showString "ImportQualifedUPF " . shows s1 . showString " " . shows s2
    ImportUPF s -> showString "ImportUPF " . shows s
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
    UDTUPF ss x -> showString "UDTUPF " . shows ss . showChar ' ' . showsPrecFunc 11 x
    CaseUPF scrutinee patterns ->
      let showPattern (pat, x) = showChar '(' . shows pat . showString ", "
                                . showsPrecFunc 11 x . showChar ')'
          showPatterns ps = showChar '[' . foldr1 (\a b -> a . showString ", " . b)
                           (fmap showPattern patterns) . showChar ']'
      in showString "CaseUPF " . showsPrecFunc 11 scrutinee . showChar ' '
         . showPatterns patterns

type Pattern = Fix (PatternF UnprocessedParsedTerm)
newtype UnprocessedParsedTerm = UnprocessedParsedTerm { unUnprocessedParsedTerm :: UPT}
type UPT = Fix (UnprocessedParsedTermF Pattern)

newtype AnnotatedUPT = AnnotatedUPT { unAnnotatedUPT :: AUPT }
  deriving (Eq, Show)
type AUPT = Cofree (UnprocessedParsedTermF PatternA) LocTag
type PatternA = Fix (PatternF AnnotatedUPT)

instance CarryAnno (Fix (UnprocessedParsedTermF PatternA)) where
  type CarryWrap (Fix (UnprocessedParsedTermF PatternA)) = UnprocessedParsedTermF PatternA

  getEmbed _ = Fix
instance CarryAnno AUPT where
  type CarryWrap AUPT = UnprocessedParsedTermF PatternA

  getEmbed (a :< _) = (a :<)

instance CarryAnno UPT where
  type CarryWrap UPT = UnprocessedParsedTermF Pattern

  getEmbed _ = Fix
