{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}

module PrettyPrint where

import Control.Comonad.Cofree
import qualified Control.Comonad.Trans.Cofree as CofreeT (CofreeF (..))
import Control.Monad.State (State)
import qualified Control.Monad.State as State
import Data.Functor.Foldable
import Data.List (elemIndex)
import Data.Map (Map)
import qualified Data.Map as Map
import Naturals (NExpr (..), NExprs (..), NResult)
import Telomare (DataType (..), FragExpr (..), FragExprF (..), FragExprUR (..),
                 FragExprURSansAnnotation (FragExprURSA, unFragExprURSA),
                 FragIndex (..), IExpr (..), IExprF (..), LocTag,
                 PartialType (..), RecursionSimulationPieces (..), Term3 (..),
                 forget, forgetAnnotationFragExprUR, g2i, indentWithOneChild',
                 indentWithTwoChildren', isNum, rootFrag)
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

indent :: Int -> String
indent 0 = []
indent n = ' ' : ' ' : indent (n - 1)

showPIExpr :: Int -> Int -> IExpr -> String
showPIExpr _ _ Zero = "Z"
showPIExpr _ _ Env = "E"
showPIExpr l i (Pair a b) =
  concat ["P\n", indent i, showPIExpr l (i + 1) a, "\n", indent i, showPIExpr l (i + 1) b]
showPIExpr l i (Gate a b) = -- "G"
  "G\n" <> indent i <> showPIExpr l (i + 1) a <> "\n" <> indent i <> showPIExpr l (i + 1) b
showPIExpr _ _ Trace = "T"
showPIExpr l i (Defer x) = "D " <> showPIExpr l i x
showPIExpr l i (PLeft x) = "L " <> showPIExpr l i x
showPIExpr l i (PRight x) = "R " <> showPIExpr l i x
showPIExpr l i (SetEnv x) = "S " <> showPIExpr l i x

showPIE = showPIExpr 80 1

showTPIExpr :: Map Int PartialType -> Int -> Int -> IExpr -> String
showTPIExpr typeMap l i expr =
  let recur = showTPIExpr typeMap l i
      indented x = (indent i <> showTPIExpr typeMap l (i + 1) x)
  in case expr of
    Zero       -> "Z"
    Env        -> "E"
    (Pair a b) -> concat ["P\n", indented a, "\n", indented b]
    Gate a b   -> "G\n" <> indented a <> "\n" <> indented b
    Trace      -> "T"

showNExpr :: Map FragIndex NResult -> Int -> Int -> NExpr -> String
showNExpr nMap l i expr =
  let recur = showNExpr nMap l i
      showTwo c a b =
        concat [c, "\n", indent i, showNExpr nMap l (i + 1) a, "\n", indent i, showNExpr nMap l (i + 1) b]
  in case expr of
  NZero -> "Z"
  NEnv -> "E"
  (NPair a b) -> showTwo "P" a b
  NGate a b -> showTwo "G" a b
  NTrace -> "T"
  (NDefer ind) -> case Map.lookup ind nMap of
    (Just n) -> "D " <> recur n
    _        -> "NDefer error: no function found for " <> show ind
  (NLeft x) -> "L " <> recur x
  (NRight x) -> "R " <> recur x
  (NSetEnv x) -> "S " <> recur x
  (NAdd a b) -> showTwo "+" a b
  (NMult a b) -> showTwo "X" a b
  (NPow a b) -> showTwo "^" a b
  (NApp c i) -> showTwo "$" c i
  (NNum n) -> show n --concat ["()"]
  (NToChurch c i) -> showTwo "<" c i
  (NOldDefer x) -> "% " <> recur x
  (NTwiddle x) -> "W " <> recur x

showNIE (NExprs m) = case Map.lookup (FragIndex 0) m of
  Just f -> showNExpr m 80 1 f
  _      -> "error: no root nexpr"

showFragInds inds = let showInd (FragIndex i) = i in show (fmap showInd inds)

showOneNExpr :: Int -> Int -> NExpr -> String
showOneNExpr l i expr =
  let recur = showOneNExpr l i
      showTwo c a b =
        concat [c, "\n", indent i, showOneNExpr l (i + 1) a, "\n", indent i, showOneNExpr l (i + 1) b]
  in case expr of
      NZero                    -> "Z"
      NEnv                     -> "E"
      (NPair a b)              -> showTwo "P" a b
      NGate a b                -> showTwo "G" a b
      NTrace                   -> "T"
      (NDefer (FragIndex ind)) -> concat ["[", show ind, "]"]
      (NLeft x)                -> "L " <> recur x
      (NRight x)               -> "R " <> recur x
      (NSetEnv x)              -> "S " <> recur x
      (NAdd a b)               -> showTwo "+" a b
      (NMult a b)              -> showTwo "X" a b
      (NPow a b)               -> showTwo "^" a b
      (NApp c i)               -> showTwo "$" c i
      (NNum n)                 -> show n --concat ["()"]
      (NToChurch c i)          -> showTwo "<" c i
      (NOldDefer x)            -> "% " <> recur x
      (NTwiddle x)             -> "W " <> recur x
      NToNum                   -> "["

showNExprs :: NExprs -> String
showNExprs (NExprs m) = concatMap
  (\(FragIndex k,v) -> concat [show k, " ", showOneNExpr 80 2 v, "\n"])
  $ Map.toList m

-- termMap, function->type lookup, root frag type
data TypeDebugInfo = TypeDebugInfo Term3 (FragIndex -> PartialType) PartialType

instance PrettyPrintable Term3 where
  showP (Term3 termMap) = showFrag (unFragExprUR $ rootFrag termMap) where
    showFrag = cata showF
    showF (_ CofreeT.:< x) = sf x
    showL (a CofreeT.:< _) = show a
    sf = \case
      ZeroFragF -> pure "Z"
      PairFragF a b -> indentWithTwoChildren' "P" a b
      EnvFragF -> pure "E"
      SetEnvFragF x -> indentWithOneChild' "S" x
      DeferFragF fi -> case Map.lookup fi termMap of
        Just frag -> let f = unFragExprUR frag
                     in indentWithOneChild' ("D" <> showL (project f)) $ showFrag f
        z -> error $ "PrettyPrint Term3 bad index found: " <> show z
      AbortFragF -> pure "A"
      GateFragF l r -> indentWithTwoChildren' "G" l r
      LeftFragF x -> indentWithOneChild' "L" x
      RightFragF x -> indentWithOneChild' "R" x
      TraceFragF -> pure "T"
      AuxFragF x -> case x of
        SizingWrapper _ x' -> indentWithOneChild' "?" . showFrag $ unFragExprUR x'
        NestedSetEnvs _ -> pure "%"

showTypeDebugInfo :: TypeDebugInfo -> String
showTypeDebugInfo (TypeDebugInfo (Term3 m) lookup rootType) =
  let termMap = forgetAnnotationFragExprUR <$> m
      showFrag (FragIndex i) ty frag = show i <> ": " <> show (PrettyPartialType ty) <> "\n" <> showExpr 80 2 frag
      showExpr l i =
        let recur = showExpr l i
            showTwo c a b =
              concat [c, "\n", indent i, showExpr l (i + 1) a, "\n", indent i, showExpr l (i + 1) b]
            showThree x a b c =
              concat [x, "\n", indent i, showExpr l (i + 1) a, "\n", indent i, showExpr l (i + 1) b, "\n", indent i, showExpr l (i + 1) c]
        in \case
          ZeroFrag                                   -> "Z"
          PairFrag a b                               -> showTwo "P" a b
          EnvFrag                                    -> "E"
          SetEnvFrag x                               -> "S " <> recur x
          DeferFrag (FragIndex ind)                  -> "[" <> show ind <> "]"
          AbortFrag                                  -> "A"
          GateFrag l r                               -> showTwo "G" l r
          LeftFrag x                                 -> "L " <> recur x
          RightFrag x                                -> "R " <> recur x
          TraceFrag                                  -> "T"
          AuxFrag (SizingWrapper _ (FragExprURSA x)) -> "?" <> recur x
          AuxFrag (NestedSetEnvs _)                  -> "%"
  in showFrag (FragIndex 0) rootType (unFragExprURSA $ rootFrag termMap) <> "\n"
     <> concatMap (\(k, v) -> showFrag k (lookup k) v <> "\n")
                  (tail . Map.toAscList . Map.map unFragExprURSA $ termMap)

newtype PrettyIExpr = PrettyIExpr IExpr

instance Show PrettyIExpr where
  show (PrettyIExpr iexpr) = case iexpr of
    p@(Pair a b) -> if isNum p
      then show $ g2i p
      else concat ["(", show (PrettyIExpr a), ",", show (PrettyIExpr b), ")"]
    Zero -> "0"
    x -> show x

indentSansFirstLine :: Int -> String -> String
indentSansFirstLine i x = removeLastNewLine res where
  res = unlines $ (\(s:ns) -> s:((indent i <>) <$> ns)) (lines x)
  indent 0 = []
  indent n = ' ' : indent (n - 1)
  removeLastNewLine str =
    case reverse str of
      '\n' : rest -> reverse rest
      x           -> str

newtype PrettierIExpr = PrettierIExpr IExpr

instance Show PrettierIExpr where
  show (PrettierIExpr iexpr) = removeRedundantParens $ cata alg iexpr where
    removeRedundantParens :: String -> String
    removeRedundantParens str = unlines $ removeRedundantParensOneLine <$> lines str
    filterOnce :: Eq a => a -> [a] -> [a]
    filterOnce y = \case
      []     -> []
      (x:xs) -> if x == y then xs else x : filterOnce y xs
    removeRedundantParensOneLine :: String -> String
    removeRedundantParensOneLine str =
      case (elemIndex '(' str, elemIndex ')' str) of
        (Just x, Just y) -> filterOnce ')' . filterOnce '(' $ str
        _                -> str
    alg :: Base IExpr String -> String
    alg = \case
      PairF x y -> case (y, readMaybe x :: Maybe Int) of
                     ("0", Just x) -> show $ x + 1
                     _ -> "P\n" <>
                          "  (" <> indentSansFirstLine 3 x <> ")\n" <>
                          "  (" <> indentSansFirstLine 3 y <> ")"
                     -- _ -> if (length . lines $ x) == 1 && (length . lines $ y) == 1
                     --        then "(" <> x <> ", " <> y  <> ")"
                     --        else "( " <> indentSansFirstLine 2 x <> "\n" <>
                     --             ", " <> indentSansFirstLine 2 y <> "\n" <>
                     --             ")"
      ZeroF -> "0"
      EnvF -> "E"
      TraceF -> "T"
      SetEnvF x -> "S\n" <>
                   "  (" <> indentSansFirstLine 3 x <> ")"
      DeferF x -> "D\n" <>
                   "  (" <> indentSansFirstLine 3 x <> ")"
      GateF x y -> "G\n" <>
                   "  (" <> indentSansFirstLine 3 x <> ")\n" <>
                   "  (" <> indentSansFirstLine 3 y <> ")"
      PLeftF x -> "L\n" <>
                  "  (" <> indentSansFirstLine 3 x <> ")"
      PRightF x -> "R\n" <>
                   "  (" <> indentSansFirstLine 3 x <> ")"

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
