{-# LANGUAGE LambdaCase #-}

-- |Post-parse desugaring. Case expressions are lowered to nested if/else
-- chains by the type-changing 'desugarTerm' boundary,
-- builtin names are bound ('addBuiltins') and partially applied builtins
-- are rewritten to direct forms ('optimizeBuiltinFunctions').
--
-- Raw parse-level sugar (multi-pattern lambdas, list assignments, UDT
-- declarations) is expanded before this stage runs, by 'Telomare.Expand'.
module Telomare.Desugar where

import Control.Comonad.Cofree (Cofree (..))
import qualified Control.Comonad.Trans.Cofree as C
import Data.Bifunctor (first)
import Data.Fix (Fix (..))
import Data.Functor.Foldable (Corecursive (embed), Recursive (..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Map.Strict (keys)
import Data.Set (Set)
import qualified Data.Set as Set
import Telomare.IR.Base
import Telomare.IR.Loc
import Telomare.IR.Surface

-- |Paths from the root of a pattern, through pairs, to each of its integer
-- literals, paired with the literal. A path is the composition of 'HLeft'
-- and 'HRight' that reaches the corresponding leaf of a matched term.
-- e.g. PatternPair (PatternVar "x") (PatternPair (PatternInt 0) (PatternVar "y"))
--      will return [(HLeft . HRight, 0)]
findInts :: PatternA -> [(DesugaredSurfaceTerm -> DesugaredSurfaceTerm, Int)]
findInts = cata alg where
  alg = \case
    PatternPairF x y      -> (first (. HLeft) <$> x) <> (first (. HRight) <$> y)
    PatternIntF i         -> [(id, i)]
    PatternAnnotatedF x _ -> x
    _                     -> []

-- |Like 'findInts', for string literals.
findStrings :: PatternA -> [(DesugaredSurfaceTerm -> DesugaredSurfaceTerm, String)]
findStrings = cata alg where
  alg = \case
    PatternPairF x y      -> (first (. HLeft) <$> x) <> (first (. HRight) <$> y)
    PatternStringF str    -> [(id, str)]
    PatternAnnotatedF x _ -> x
    _                     -> []

findPatternVars :: LocTag -> PatternA
                -> Map String (DesugaredSurfaceTerm -> DesugaredSurfaceTerm)
findPatternVars _anno = cata alg where
  alg = \case
    PatternPairF x y      -> ((. HLeft) <$> x) <> ((. HRight) <$> y)
    PatternVarF name      -> Map.singleton (locatedNameText name) id
    PatternAnnotatedF x _ -> x
    _                     -> Map.empty

-- TODO: Annotate without so much fuzz
-- |Checks that every pair node of the pattern is a pair in the term. The
-- nodes are arbitrary values, so each is coerced to a Bool before it reaches
-- @and@, whose arguments are refined to Bool.
pairStructureCheck :: PatternA -> DesugaredSurfaceTerm -> DesugaredSurfaceTerm
pairStructureCheck p upt = let a = GeneratedLoc "pairStructureCheck" Nothing
                               toBool :: DesugaredSurfaceTerm -> DesugaredSurfaceTerm
                               toBool x = ITEP x (a :< IntUPF 1) (a :< IntUPF 0)
  in AppP (AppP (AppP (rewriteOuterTag a $ VarP "__case_foldl")
                         (VarP "__case_and"))
                  (a :< IntUPF 1))
           ((a :<) . ListUPF $ toBool . ($ upt) <$> pairRoute2Dirs p)

pairRoute2Dirs :: PatternA -> [DesugaredSurfaceTerm -> DesugaredSurfaceTerm]
pairRoute2Dirs = cata alg where
  alg = \case
    PatternPairF x y      -> [id] <> ((. HLeft) <$> x) <> ((. HRight) <$> y)
    PatternAnnotatedF x _ -> x
    _                     -> []

-- |Realize a pattern's literal skeleton as a term, with variables and
-- ignores as zeroes. Polymorphic in the case witness and pattern parameter
-- so both the expanded and desugared phases can use it.
patternToTerm :: LocTag -> PatternA -> Cofree (UnprocessedParsedTermF c p) LocTag
patternToTerm anno = cata alg where
  alg = \case
    PatternPairF x y       -> anno :< embedB (PairSF x y)
    PatternIntF i          -> anno :< IntUPF i
    PatternStringF str     -> anno :< StringUPF str
    PatternVarF _          -> anno :< IntUPF 0
    PatternIgnoreF         -> anno :< IntUPF 0
    PatternAnnotatedF x _  -> x

mkCaseAlternative :: DesugaredSurfaceTerm -- ^ Term to be cased
                  -> DesugaredSurfaceTerm -- ^ Case result to be made lambda and applied
                  -> PatternA -- ^ Pattern
                  -> DesugaredSurfaceTerm -- ^ case result as a lambda applied to the appropriate part of the term to be cased
mkCaseAlternative casedUPT@(anno :< _) caseResult p = appVars2ResultLambdaAlts patternVarsOnUPT . makeLambdas caseResult . keys $ patternVarsOnUPT where
  patternVarsOnUPT :: Map String DesugaredSurfaceTerm
  patternVarsOnUPT = ($ casedUPT) <$> findPatternVars anno p
  appVars2ResultLambdaAlts :: Map String DesugaredSurfaceTerm
                            -> DesugaredSurfaceTerm -- ^ case result as lambda
                            -> DesugaredSurfaceTerm
  appVars2ResultLambdaAlts m = \case
    lam@(LamP varName upt) ->
      case Map.lookup (locatedNameText varName) m of
        Nothing -> lam
        Just x -> AppP (LamP varName (appVars2ResultLambdaAlts (Map.delete (locatedNameText varName) m) upt)) x
    x -> x
  makeLambdas :: DesugaredSurfaceTerm
              -> [String]
              -> DesugaredSurfaceTerm
  makeLambdas aupt@(anno' :< _) = \case
    []     -> aupt
    (x:xs) -> LamP (locatedName anno' x) (makeLambdas aupt xs)

-- |Lower a case expression to nested if/else chains that try each
-- alternative in order, aborting when none matches.
caseToNestedIfs :: DesugaredSurfaceTerm -- ^ Term to be pattern matched
                -> [(PatternA, DesugaredSurfaceTerm)] -- ^ Alternatives
                -> DesugaredSurfaceTerm
caseToNestedIfs x@(anno :< _) = foldr alternative nonExhaustive where
  nonExhaustive =
    ITEP (anno :< IntUPF 1)
         (AppP (VarP "__case_abort") (anno :< StringUPF "Non-exhaustive patterns in case"))
         (anno :< IntUPF 0)
  alternative (p, result@(resultAnno :< _)) =
    ITEP (patternMatches resultAnno x p) (mkCaseAlternative x result p)

-- |A Bool-valued term checking that the term has the pattern's pair
-- structure and that each literal leaf equals the pattern's. Integer leaves
-- are compared with @dEqual@ and string leaves, as whole strings, with
-- @listEqual@.
patternMatches :: LocTag -> DesugaredSurfaceTerm -> PatternA -> DesugaredSurfaceTerm
patternMatches anno x p = allOf $ intChecks <> stringChecks <> [pairStructureCheck p x]
  where
    intChecks = [ equal "__case_dEqual" (path x) (anno :< IntUPF i)
                | (path, i) <- findInts p ]
    stringChecks = [ equal "__case_listEqual" (path x) (anno :< StringUPF str)
                   | (path, str) <- findStrings p ]
    equal :: String -> DesugaredSurfaceTerm -> DesugaredSurfaceTerm -> DesugaredSurfaceTerm
    equal helper a = AppP (AppP (VarP helper) a)
    allOf = \case
      [c]    -> c
      [a, b] -> AppP (AppP (rewriteOuterTag anno $ VarP "__case_and") a) b
      cs     -> AppP (AppP (AppP (rewriteOuterTag anno $ VarP "__case_foldl")
                                 (VarP "__case_and"))
                           (anno :< IntUPF 1))
                     (anno :< ListUPF cs)

-- |Run every post-sugar rewrite and remove the case capability from the term
-- type before resolution.
desugarTerm :: ExpandedSurfaceTerm -> DesugaredSurfaceTerm
desugarTerm = lowerCases
            . optimizeBuiltinFunctions
            . addBuiltins
            . addCaseHelperAliases

lowerCases :: ExpandedSurfaceTerm -> DesugaredSurfaceTerm
lowerCases = cata go where
  go = \case
    _ C.:< CaseUPF x ls -> caseToNestedIfs x ls
    anno C.:< UnprocessedParsedTermH x -> anno :< UnprocessedParsedTermH x
    anno C.:< UnprocessedParsedTermL x -> anno :< UnprocessedParsedTermL x
    anno C.:< UnprocessedParsedTermB x -> anno :< UnprocessedParsedTermB x
    anno C.:< LetUPF bindings body     -> anno :< LetUPF bindings body
    anno C.:< ListUPF terms            -> anno :< ListUPF terms
    anno C.:< IntUPF n                 -> anno :< IntUPF n
    anno C.:< StringUPF s              -> anno :< StringUPF s

-- |Capture the helper definitions used by generated case code in the
-- outer resolved let. The aliases cannot be written in source, so nested
-- bindings cannot capture the generated references.
addCaseHelperAliases :: ExpandedSurfaceTerm -> ExpandedSurfaceTerm
addCaseHelperAliases _term@(loc :< LetUPF bindings body) =
  loc :< LetUPF (aliases <> bindings) body
  where
    aliases =
      [ ( locatedName (GeneratedLoc ("case helper " <> name) (Just loc)) alias
        , loc :< UnprocessedParsedTermL (VarF name)
        )
      | (name, alias) <- [ ("and", "__case_and")
                         , ("foldl", "__case_foldl")
                         , ("dEqual", "__case_dEqual")
                         , ("listEqual", "__case_listEqual")
                         , ("abort", "__case_abort")
                         ]
      , name `elem` (letBindingName <$> bindings)
      ]
addCaseHelperAliases term = term


rewriteOuterTag :: anno -> Cofree a anno -> Cofree a anno
rewriteOuterTag anno (_ :< x) = anno :< x


optimizeBuiltinFunctions :: ExpandedSurfaceTerm -> ExpandedSurfaceTerm
optimizeBuiltinFunctions = go builtinNames
  where
    builtinNames = Set.fromList ["left", "right", "trace", "pair", "app"]

    go :: Set String -> ExpandedSurfaceTerm -> ExpandedSurfaceTerm
    go scope (anno :< term) = optimize scope $ case term of
      UnprocessedParsedTermL (AppF inner y) -> case project inner of
        AppAFP _ f x -> case project f of
          VarAFP _ "pair" | "pair" `Set.member` scope ->
            anno :< UnprocessedParsedTermB (PairSF (go scope x) (go scope y))
          VarAFP _ "app"  | "app" `Set.member` scope ->
            anno :< UnprocessedParsedTermL (AppF (go scope x) (go scope y))
          _ -> anno :< UnprocessedParsedTermL (AppF (go scope inner) (go scope y))
        _ -> anno :< UnprocessedParsedTermL (AppF (go scope inner) (go scope y))
      UnprocessedParsedTermL (LamF name body) ->
        anno :< UnprocessedParsedTermL (LamF name (go (Set.delete (locatedNameText name) scope) body))
      other -> anno :< mapScoped (go . foldr updateScope scope) other

    -- A let binder re-exposes a builtin when tagged as its definition;
    -- every other binder (including case-pattern variables, which the
    -- parser never tags 'BuiltinLoc') shadows it.
    updateScope name =
      let text = locatedNameText name
      in if locatedNameLoc name == BuiltinLoc text
           then Set.insert text
           else Set.delete text

    optimize :: Set String -> ExpandedSurfaceTerm -> ExpandedSurfaceTerm
    optimize scope term = case project term of
      AppAFP a (GFix (AppAFP _ f x)) y -> case project f of
        VarAFP _ "pair" | "pair" `Set.member` scope -> embed $ PairAFP a x y
        VarAFP _ "app"  | "app" `Set.member` scope  -> embed $ AppAFP a x y
        _                                           -> term
      AppAFP a f x -> case project f of
        VarAFP _ "left"  | "left" `Set.member` scope  -> HLeft x
        VarAFP _ "right" | "right" `Set.member` scope -> HRight x
        VarAFP _ "trace" | "trace" `Set.member` scope -> a :< UnprocessedParsedTermH (HTraceF x)
        VarAFP _ "pair"  | "pair" `Set.member` scope  -> partial a x PairP
        VarAFP _ "app"   | "app" `Set.member` scope   -> partial a x AppP
        _ -> term
      _ -> term

    partial anno x constructor =
      let argument = locatedName anno "__builtin_arg"
      in embed $ LamAFP anno argument (constructor x (embed $ VarAFP anno "__builtin_arg"))


addBuiltins :: ExpandedSurfaceTerm -> ExpandedSurfaceTerm
addBuiltins aupt = GeneratedLoc "addBuiltins" Nothing :< LetUPF
  [ bind "zero" (builtin "zero" :< IntUPF 0)
  , bind "left" (tagBuiltin "left" $ LamP (locatedName (builtin "left") "x") (HLeft $ VarP "x"))
  , bind "right" (tagBuiltin "right" $ LamP (locatedName (builtin "right") "x") (HRight $ VarP "x"))
  , bind "trace" (tagBuiltin "trace" $ LamP (locatedName (builtin "trace") "x") (HTrace $ VarP "x"))
  , bind "pair" (tagBuiltin "pair" $ LamP (locatedName (builtin "pair") "x") (LamP (locatedName (builtin "pair") "y") (PairP (VarP "x") (VarP "y"))))
  , bind "app" (tagBuiltin "app" $ LamP (locatedName (builtin "app") "x") (LamP (locatedName (builtin "app") "y") (AppP (VarP "x") (VarP "y"))))
  ]
  aupt
  where
    tagBuiltin :: String -> Fix (UnprocessedParsedTermF () PatternA) -> ExpandedSurfaceTerm
    tagBuiltin n = tag (BuiltinLoc n)
    builtin = BuiltinLoc
    bind name value = (locatedName (builtin name) name, value)
