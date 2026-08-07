{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE TypeFamilies      #-}

-- |The surface AST. Each surface phase has its own term type composed of
-- fragment functors: the parser produces 'PAUPT', whose base functor
-- 'ParsedTermF' is 'UnprocessedParsedTermF' (the shared base functors plus
-- the surface-only forms: let, list, case, and imports) extended with the
-- sugar-only fragment 'SugarTermF'. 'Telomare.Sugar' removes that fragment,
-- returning 'AUPT' — so a desugared tree structurally cannot contain raw
-- sugar forms.
module Telomare.IR.Surface where

import Control.Comonad.Cofree (Cofree ((:<)))
import qualified Control.Comonad.Trans.Cofree as CofreeT (CofreeF (..))
import Data.Fix (Fix (..))
import Data.Functor.Classes (Eq1 (..), Show1 (..))
import Data.List (intersperse)
import GHC.Generics (Generic1, Generically1 (..))
import Telomare.IR.Base (BasicBase (..), BasicExprF (..), CarryAnno (..),
                         HighBase (..), HighTermF (..), LamBase (..),
                         LamTermF (..))
import Telomare.IR.Loc (LocTag, LocatedName, locatedNameText)

-- |AST for patterns in `case` expressions
data PatternF t f
  = PatternVarF LocatedName
  | PatternAnnotatedF f t
  | PatternIntF Int
  | PatternStringF String
  | PatternIgnoreF
  | PatternPairF f f
  deriving (Show, Eq, Functor, Foldable, Traversable, Generic1)
  deriving Eq1 via (Generically1 (PatternF t))

instance Show o => Show1 (PatternF o) where
  liftShowsPrec showsPrec' showList prec = \case
    PatternVarF s -> showString "PatternVar " . shows (locatedNameText s)
    PatternAnnotatedF p x -> showString "PatternAnnotated " . showsPrec' 0 p . showChar ' ' . shows x
    PatternIntF x -> showString "PatternInt " . shows x
    PatternStringF s -> showString "PatternString " . shows s
    PatternIgnoreF -> showString "PatternIgnore"
    PatternPairF a b -> showString "PatternPair " . showsPrec' 0 a . showChar ' ' . showsPrec' 0 b

-- |One top-level or let-level definition exactly as written in the source,
-- before desugaring. @SingleDefF name annotation body@ is
-- @name (: check)? = body@, where the annotation's 'LocTag' is captured at
-- the @:@. @ListDefF loc names body@ is @[n1, n2, ...] = body@ (a plain
-- list assignment or a UDT declaration; 'Telomare.Sugar' decides which).
data DefinitionF f
  = SingleDefF LocatedName (Maybe (LocTag, f)) f
  | ListDefF LocTag [LocatedName] f
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic1)
  deriving Eq1 via (Generically1 DefinitionF)

definitionNames :: DefinitionF f -> [LocatedName]
definitionNames = \case
  SingleDefF name _ _  -> [name]
  ListDefF _ names _   -> names

-- |An import declaration exactly as written in a module.
data ImportDecl = ImportDecl
  { parsedImportLoc       :: LocTag
  , parsedImportModule    :: LocatedName
  , parsedImportQualifier :: Maybe LocatedName
  }
  deriving (Eq, Show)

-- |One source-level module item.
data ModuleItem f
  = ModuleImportItem ImportDecl
  | ModuleDefinitionItem (DefinitionF f)
  deriving (Eq, Show, Functor, Foldable, Traversable)

-- |The desugared surface AST base functor: the shared fragments plus the
-- surface-only forms every later stage consumes. The parser's raw sugar
-- forms live in 'SugarTermF', which 'ParsedTermF' adds on top of this.
data UnprocessedParsedTermF p f
  = UnprocessedParsedTermH (HighTermF f)
  | UnprocessedParsedTermL (LamTermF LocatedName String f)
  | UnprocessedParsedTermB (BasicExprF f)
  | LetUPF [(LocatedName, f)] f
  | ListUPF [f]
  | IntUPF Int
  | StringUPF String
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
          showBindings bs = showChar '['
                          . foldr (.) id (intersperse (showString ", ") (fmap showBinding bs))
                          . showChar ']'
      in showString "LetUPF " . showBindings bindings . showChar ' ' . showsPrecFunc 11 body
    ListUPF terms -> showString "ListUPF ["
                   . foldr (.) id (intersperse (showString ", ") (fmap (showsPrecFunc 11) terms))
                   . showChar ']'
    IntUPF n -> showString "IntUPF " . shows n
    StringUPF s -> showString "StringUPF " . shows s
    CaseUPF scrutinee patterns ->
      let showPattern (pat, x) = showChar '(' . shows pat . showString ", "
                                . showsPrecFunc 11 x . showChar ')'
          showPatterns ps = showChar '['
                          . foldr (.) id (intersperse (showString ", ") (fmap showPattern ps))
                          . showChar ']'
      in showString "CaseUPF " . showsPrecFunc 11 scrutinee . showChar ' '
         . showPatterns patterns

-- |The sugar-only surface forms: present in 'ParsedTermF', eliminated by
-- 'Telomare.Sugar' (rewritten into plain 'UnprocessedParsedTermL' lambdas
-- and 'LetUPF' bindings).
data SugarTermF p f
  = LamPatF [(LocTag, p)] f
  | LetSugarF [DefinitionF f] f
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic1)
  deriving Eq1 via (Generically1 (SugarTermF p))

instance (Show p) => Show1 (SugarTermF p) where
  liftShowsPrec showsPrecFunc _ _ = \case
    LamPatF pats body ->
      showString "LamPatF " . shows pats . showChar ' ' . showsPrecFunc 11 body
    LetSugarF defs body ->
      let showAnnot = \case
            Nothing       -> showString "Nothing"
            Just (loc, t) -> showString "(Just (" . shows loc . showString ", "
                             . showsPrecFunc 0 t . showString "))"
          showDef = \case
            SingleDefF name annot value ->
              showString "(SingleDefF " . shows name . showChar ' ' . showAnnot annot
              . showChar ' ' . showsPrecFunc 11 value . showChar ')'
            ListDefF loc names value ->
              showString "(ListDefF " . shows loc . showChar ' ' . shows names
              . showChar ' ' . showsPrecFunc 11 value . showChar ')'
          showDefs ds = showChar '['
                        . foldr (.) id (intersperse (showString ", ") (fmap showDef ds))
                        . showChar ']'
      in showString "LetSugarF " . showDefs defs . showChar ' ' . showsPrecFunc 11 body

-- |The parsed-phase base functor: everything in 'UnprocessedParsedTermF'
-- plus the sugar fragment. 'Telomare.Sugar' is the stage that removes
-- 'ParsedTermSugar', producing plain 'AUPT' trees.
data ParsedTermF p f
  = ParsedTermUP (UnprocessedParsedTermF p f)
  | ParsedTermSugar (SugarTermF p f)
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic1)
  deriving Eq1 via (Generically1 (ParsedTermF p))

instance HighBase (ParsedTermF p) where
  embedH = ParsedTermUP . embedH
  extractH = \case
    ParsedTermUP x -> extractH x
    _              -> Nothing
instance BasicBase (ParsedTermF p) where
  embedB = ParsedTermUP . embedB
  extractB = \case
    ParsedTermUP x -> extractB x
    _              -> Nothing
instance LamBase (ParsedTermF p) where
  type LamVar (ParsedTermF p) = String
  type LamT (ParsedTermF p) = LocatedName

  embedL = ParsedTermUP . embedL
  extractL = \case
    ParsedTermUP x -> extractL x
    _              -> Nothing

instance (Show p) => Show1 (ParsedTermF p) where
  liftShowsPrec showsPrecFunc showList d = \case
    ParsedTermUP x    -> liftShowsPrec showsPrecFunc showList d x
    ParsedTermSugar x -> liftShowsPrec showsPrecFunc showList d x

-- |Convert the pattern type inside one layer ('CaseUPF' is the only
-- constructor mentioning it). Used by 'Telomare.Sugar' to desugar the
-- terms embedded in pattern annotations.
traverseUPTPatterns :: Applicative m
                    => (p -> m q)
                    -> UnprocessedParsedTermF p f
                    -> m (UnprocessedParsedTermF q f)
traverseUPTPatterns f = \case
  CaseUPF scrutinee alternatives ->
    CaseUPF scrutinee <$> traverse (\(p, b) -> (, b) <$> f p) alternatives
  UnprocessedParsedTermH x -> pure $ UnprocessedParsedTermH x
  UnprocessedParsedTermL x -> pure $ UnprocessedParsedTermL x
  UnprocessedParsedTermB x -> pure $ UnprocessedParsedTermB x
  LetUPF bindings body     -> pure $ LetUPF bindings body
  ListUPF terms            -> pure $ ListUPF terms
  IntUPF n                 -> pure $ IntUPF n
  StringUPF s              -> pure $ StringUPF s
  ImportQualifiedUPF a b   -> pure $ ImportQualifiedUPF a b
  ImportUPF s              -> pure $ ImportUPF s

type Pattern = Fix (PatternF UnprocessedParsedTerm)
newtype UnprocessedParsedTerm = UnprocessedParsedTerm { unUnprocessedParsedTerm :: UPT}
type UPT = Fix (UnprocessedParsedTermF Pattern)

newtype AnnotatedUPT = AnnotatedUPT { unAnnotatedUPT :: AUPT }
  deriving (Eq, Show)
type AUPT = Cofree (UnprocessedParsedTermF PatternA) LocTag
type PatternA = Fix (PatternF AnnotatedUPT)

-- |The parsed-phase family, mirroring the 'AUPT' one. Only the parser and
-- 'Telomare.Sugar' traffic in these.
newtype AnnotatedPUPT = AnnotatedPUPT { unAnnotatedPUPT :: PAUPT }
  deriving (Eq, Show)
type PAUPT = Cofree (ParsedTermF PatternP) LocTag
type PatternP = Fix (PatternF AnnotatedPUPT)

instance CarryAnno (Fix (UnprocessedParsedTermF PatternA)) where
  type CarryWrap (Fix (UnprocessedParsedTermF PatternA)) = UnprocessedParsedTermF PatternA

  getEmbed _ = Fix
instance CarryAnno AUPT where
  type CarryWrap AUPT = UnprocessedParsedTermF PatternA

  getEmbed (a :< _) = (a :<)

instance CarryAnno PAUPT where
  type CarryWrap PAUPT = ParsedTermF PatternP

  getEmbed (a :< _) = (a :<)

instance CarryAnno UPT where
  type CarryWrap UPT = UnprocessedParsedTermF Pattern

  getEmbed _ = Fix
