{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE PatternSynonyms   #-}

module PrettyPrint where

import Control.Monad.State (State)
import Data.Map (Map)
import Telomare (DataType (..), LamType (..), LocTag, PartExprF (..),
                 StuckF (..), AbortableF (..), StuckExprF (..),
                 CompiledExprF (..), Term3F (..), FunctionIndex,
                 ParserTermF (..), PartialType (..), Pattern (..),
                 Term1, Term3 (..),
                 UnprocessedParsedTerm (..), UnprocessedParsedTermF (..),
                 forget, indentWithChildren', convertAbortMessage,
                 indentWithOneChild', indentWithTwoChildren', StuckExpr, pattern BasicEE, b2i, locatedNameText, CompiledExpr)

import qualified Control.Comonad.Trans.Cofree as CofreeT (CofreeF (..))
import qualified Control.Monad.State as State
import qualified Data.Map as Map

import Control.Comonad.Cofree
import Data.Fix (Fix)
import Data.Functor.Foldable
import Data.List (elemIndex)
import Text.Read (readMaybe)
-- import Data.SBV (sFPHalf)


class PrettyPrintable p where
  showP :: p -> State Int String

class PrettyPrintable1 p where
  showP1 :: PrettyPrintable a => p a -> State Int String

instance (PrettyPrintable1 f, PrettyPrintable x) => PrettyPrintable (f x) where
  showP = showP1

-- instance (Base r ~ PrettyPrintable1 f, Recursive r) => PrettyPrintable r where

prettyPrint :: PrettyPrintable p => p -> String
prettyPrint x = State.evalState (showP x) 0

indentation :: Int -> String
indentation 0 = []
indentation n = ' ' : ' ' : indentation (n - 1)

-- termMap, function->type lookup, root frag type
-- data TypeDebugInfo = TypeDebugInfo Term3 (FragIndex -> PartialType) PartialType

instance {-# OVERLAPPING #-} PrettyPrintable Term1 where
  showP = cata fa where
    fa (_ CofreeT.:< x) = case x of
      TZeroF                   -> pure "0"
      TPairF a b               -> indentWithTwoChildren' "(" a b
      TVarF v                  -> pure v
      TAppF c i                -> indentWithTwoChildren' "($)" c i
      TCheckF cf i             -> indentWithTwoChildren' ":" cf i
      TITEF i t e              -> indentWithChildren' "ITE" [i,t,e]
      TLeftF x                 -> indentWithOneChild' "L" x
      TRightF x                -> indentWithOneChild' "R" x
      TTraceF x                -> indentWithOneChild' "T" x
      THashF x                 -> indentWithOneChild' "#" x
      TChurchF n               -> pure $ "$" <> show n
      TLamF (Open v) x         -> indentWithOneChild' ("\\" <> v) x
      TLamF (Closed v) x       -> indentWithOneChild' ("[\\" <> v) x
      TLamF (LetBinding c v) x -> indentWithOneChild' ("{\\(" <> show c <> ") " <> v) x
      TLimitedRecursionF t r b -> indentWithChildren' "TRB" [t,r,b]
      TUnsizedRepeaterF        -> pure "*"

instance {-# OVERLAPPING #-} (Show l, Show v) => PrettyPrintable (Fix (ParserTermF l v)) where
  showP = cata f where
    f = \case
      TZeroF                   -> pure "0"
      TPairF a b               -> indentWithTwoChildren' "(" a b
      TVarF v                  -> pure $ show v
      TAppF c i                -> indentWithTwoChildren' "($)" c i
      TCheckF cf i             -> indentWithTwoChildren' ":" cf i
      TITEF i t e              -> indentWithChildren' "ITE" [i,t,e]
      TLeftF x                 -> indentWithOneChild' "L" x
      TRightF x                -> indentWithOneChild' "R" x
      TTraceF x                -> indentWithOneChild' "T" x
      THashF x                 -> indentWithOneChild' "#" x
      TChurchF n               -> pure $ "$" <> show n
      TLamF (Open v) x         -> indentWithOneChild' ("\\" <> show v) x
      TLamF (Closed v) x       -> indentWithOneChild' ("[\\" <> show v) x
      TLamF (LetBinding c v) x -> indentWithOneChild' ("{\\(" <> show c <> ") " <> show v) x
      TLimitedRecursionF t r b -> indentWithChildren' "TRB" [t,r,b]
      TUnsizedRepeaterF        -> pure "*"

indentSansFirstLine :: Int -> String -> String
indentSansFirstLine i x = removeLastNewLine res where
  res = unlines $ (\(s:ns) -> s:((indentation i <>) <$> ns)) (lines x)
  removeLastNewLine str =
    case reverse str of
      '\n' : rest -> reverse rest
      x           -> str

newtype PrettyDataType = PrettyDataType DataType

showInternal :: DataType -> String
showInternal at@(ArrType _ _) = concat ["(", show $ PrettyDataType at, ")"]
showInternal t                = show . PrettyDataType $ t

instance Show PrettyDataType where
  show (PrettyDataType dt) = case dt of
    ZeroType -> "D"
    (ArrType a b) -> concat [showInternal a, " -> ", showInternal b]
    (PairType a b) ->
      concat ["(", show $ PrettyDataType a, ",", show $ PrettyDataType b, ")"]

newtype PrettyPartialType = PrettyPartialType PartialType

showInternalP :: PartialType -> String
showInternalP at@(ArrTypeP _ _) = concat ["(", show $ PrettyPartialType at, ")"]
showInternalP t                 = show . PrettyPartialType $ t

instance Show PrettyPartialType where
  show (PrettyPartialType dt) = case dt of
    ZeroTypeP -> "Z"
    AnyType -> "A"
    (ArrTypeP a b) -> concat [showInternalP a, " -> ", showInternalP b]
    (PairTypeP a b) ->
      concat ["(", show $ PrettyPartialType a, ",", show $ PrettyPartialType b, ")"]
    (TypeVariable _ (-1)) -> "badType"
    (TypeVariable _ x) -> 'v' : show x

newtype PrettyPattern = PrettyPattern Pattern

instance Show PrettyPattern where
  show = \case
    (PrettyPattern (PatternInt x)) -> show x
    (PrettyPattern (PatternVar x)) -> x
    (PrettyPattern (PatternString x)) ->  show x
    (PrettyPattern (PatternPair x y)) -> "(" <> (show . PrettyPattern $ x) <> ", " <> (show . PrettyPattern $ y) <> ")"
    (PrettyPattern PatternIgnore) -> "_"

newtype MultiLineShowUPT = MultiLineShowUPT UnprocessedParsedTerm
instance Show MultiLineShowUPT where
  show (MultiLineShowUPT upt) = cata alg upt where
    alg :: Base UnprocessedParsedTerm String -> String
    ind = indentSansFirstLine 2
    alg = \case
      IntUPF i -> "IntUP " <> show i
      VarUPF str -> "VarUP " <> str
      StringUPF str -> "StringUP " <> show str
      PairUPF x y -> "PairUP\n" <>
                        "  " <> ind x <> "\n" <>
                        "  " <> ind y
      (ITEUPF x y z) -> "ITEUP\n" <>
                        "  " <> ind x <> "\n" <>
                        "  " <> ind y <> "\n" <>
                        "  " <> ind z
      (AppUPF x y) -> "AppUP\n" <>
                        "  " <> ind x <> "\n" <>
                        "  " <> ind y
      (LamUPF str y) -> "LamUP " <> locatedNameText str <> "\n" <>
                        "  " <> ind y
      (ChurchUPF x) -> "ChurchUP " <> show x
      (LeftUPF x) -> "LeftUP\n" <>
                       "  " <> ind x
      (RightUPF x) -> "RightUP\n" <>
                        "  " <> ind x
      (TraceUPF x) -> "TraceUP\n" <>
                        "  " <> ind x
      (UnsizedRecursionUPF x y z) -> "UnsizedRecursionUP\n" <>
                        "  " <> ind x <> "\n" <>
                        "  " <> ind y <> "\n" <>
                        "  " <> ind z
      (HashUPF x) -> "HashUP\n" <>
                       "  " <> ind x
      (CheckUPF x y) -> "CheckUP\n" <>
                        "  " <> ind x <> "\n" <>
                        "  " <> ind y
      (ListUPF []) -> "ListUP []"
      (ListUPF [x]) -> "ListUP [" <> x <> "]"
      (ListUPF ls) -> "ListUP\n" <>
                        concatMap (\x -> "  , " <> ind x <> "\n") ls <>
                        "  ]"
      (LetUPF ls x) -> "LetUP\n" <>
                         concatMap (\(n,v) -> "  , (" <> locatedNameText n <> ", " <> ind v <> ")\n") ls <>
                         "  ]\n" <>
                         "  " <> ind x
      (CaseUPF x ls) -> "CaseUP\n" <>
                          "  " <> ind x <> "\n" <>
                          concatMap (\(p,v) -> "  , (" <> show p <> ",\n    " <> ind v <> ")\n") ls <>
                          "  ]"
      (UDTUPF ss x) -> "UDTUP " <> show ss <> "\n" <>
                        "  " <> ind x
      (ImportUPF s) -> "ImportUP " <> show s
      (ImportQualifiedUPF s1 s2) -> "ImportQualifiedUP " <> show s1 <> " " <> show s2

newtype PrettyUPT = PrettyUPT UnprocessedParsedTerm

instance Show PrettyUPT where
  show (PrettyUPT upt) = cata alg upt where
    alg :: Base UnprocessedParsedTerm String -> String
    alg = \case
      IntUPF i -> show i
      VarUPF str -> str
      StringUPF str -> show str
      PairUPF x y -> if length (lines (x <> y)) > 1
                       then "( " <> indentSansFirstLine 2 x <> "\n" <>
                            ", " <> indentSansFirstLine 2 y <> "\n" <>
                            ")"
                       else "(" <> x <> ", " <> y <>")"
      (ITEUPF x y z) -> "if " <> indentSansFirstLine 3 x <> "\n" <>
                          "  then " <> indentSansFirstLine 7 y <> "\n" <>
                          "  else " <> indentSansFirstLine 7 z
      (LetUPF ls x) ->
        "let " <> indentSansFirstLine 4 (unlines (assignList <$> ls)) <> "\n" <>
        "in " <> indentSansFirstLine 3 x
          where
            assignList (name, upt) = locatedNameText name <> " = " <> indentSansFirstLine (3 + length (locatedNameText name)) upt
      (ListUPF []) -> "[]"
      (ListUPF [x]) -> "[" <> x <> "]"
      (ListUPF ls) ->
        "[" <> removeFirstComma (unlines (indentSansFirstLine 2 . (", " <>) <$> ls)) <>
        "]"
          where
            removeFirstComma = \case
              (',':str) -> str
              _         -> error "removeFirstComma: input does not start with a comma"
      (AppUPF x y) -> (if (length . words $ x) == 1 then x else "(" <> x <> ")") <> " " <>
                      if (length . words $ y) == 1 then y else "(" <> y <> ")"
      (LamUPF str y) -> "\\ " <> locatedNameText str <> " -> " <> indentSansFirstLine (6 + length (locatedNameText str)) y
      (ChurchUPF x) -> "$" <> show x
      (LeftUPF x) -> "left (" <> indentSansFirstLine 6 x <> ")"
      (RightUPF x) -> "right (" <> indentSansFirstLine 7 x <> ")"
      (TraceUPF x) -> "trace (" <> indentSansFirstLine 7 x <> ")"
      (UnsizedRecursionUPF x y z) -> "{ " <> indentSansFirstLine 2 x <>
                                     ", " <> indentSansFirstLine 2 y <>
                                     ", " <> indentSansFirstLine 2 z <>
                                     "}"
      (HashUPF x) -> "# " <> indentSansFirstLine 2 x
      (CaseUPF x ls) -> "case " <> x <> " of\n" <>
                        "  " <> indentSansFirstLine 2 (unlines ((\(p, r) -> indentSansFirstLine 2 (show (PrettyPattern p) <> " -> " <> r)) <$> ls))
      (CheckUPF x y) -> if length (lines (x <> y)) > 1
                          then "(" <> indentSansFirstLine 2 y <> " : " <> "\n" <>
                               "    " <> indentSansFirstLine 4 y <> ")"
                          else "(" <> y <> " : " <> x <> ")"

instance PrettyPrintable LocTag where
  showP = const $ pure ""

showFI :: FunctionIndex -> String
showFI = ("F" <>) . show . fromEnum

instance PrettyPrintable1 StuckF where
  showP1 = \case
    DeferSF ind x -> indentWithOneChild' (showFI ind) $ showP x

instance PrettyPrintable1 PartExprF where
  showP1 = \case
    ZeroSF     -> pure "Z"
    PairSF a b -> indentWithTwoChildren' "P" (showP a) (showP b)
    EnvSF      -> pure "E"
    SetEnvSF x -> indentWithOneChild' "S" $ showP x
    GateSF l r -> indentWithTwoChildren' "G" (showP l) (showP r)
    LeftSF x   -> indentWithOneChild' "L" $ showP x
    RightSF x  -> indentWithOneChild' "R" $ showP x

instance PrettyPrintable1 AbortableF where
  showP1 = \case
    AbortF      -> pure "!"
    AbortedF am -> pure $ "(aborted - " <> convertAbortMessage am <> ")"

instance PrettyPrintable1 StuckExprF where
  showP1 = \case
    StuckExprB x -> showP1 x
    StuckExprS x -> showP1 x

instance PrettyPrintable1 CompiledExprF where
  showP1 = \case
    CompiledExprB x -> showP1 x
    CompiledExprS x -> showP1 x
    CompiledExprA x -> showP1 x

instance PrettyPrintable1 Term3F where
  showP1 = \case
    Term3B x -> showP1 x
    Term3S x -> showP1 x
    Term3A x -> showP1 x
    Term3Unsized urt -> pure $ "#" <> show urt
    Term3CheckingWrapper _ t c -> indentWithTwoChildren' ":" (showP t) (showP c)

instance {-# OVERLAPPING #-} (PrettyPrintable a, PrettyPrintable1 f) => PrettyPrintable (Cofree f a) where
  showP (a :< x) = (<>) <$> showP a <*> showP1 x

newtype PrettyStuckExpr = PrettyStuckExpr StuckExpr

instance Show PrettyStuckExpr where
  show (PrettyStuckExpr x) = f x where
    f :: StuckExpr -> String
    f x = case b2i x of
      Just n -> show n
      _ -> case x of
        BasicEE (PairSF a b) -> "(" <> f a <> "," <> f b <> ")"
        z -> show z

newtype PrettyCompiledExpr = PrettyCompiledExpr CompiledExpr

instance Show PrettyCompiledExpr where
  show (PrettyCompiledExpr x) = f x where
    f :: CompiledExpr -> String
    f x = case b2i x of
      Just n -> show n
      _ -> case x of
        BasicEE (PairSF a b) -> "(" <> f a <> "," <> f b <> ")"
        z -> show z
