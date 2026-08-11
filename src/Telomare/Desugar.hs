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
import Data.Bifunctor (bimap)
import Data.Fix (Fix (..))
import qualified Data.Foldable as F
import Data.Functor.Foldable (Base, Corecursive (embed), Recursive (..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Map.Strict (keys)
import Data.Set (Set)
import qualified Data.Set as Set
import Telomare.Error
import Telomare.IR.Base
import Telomare.IR.Core
import Telomare.IR.Loc
import Telomare.IR.Surface
import Telomare.IR.Types

-- | Finds all PatternInt leaves returning "directions" to these leaves through pairs
-- in the form of a combination of RightUP and LeftUP from the root
-- e.g. PatternPair (PatternVar "x") (PatternPair (PatternInt 0) (PatternVar "y"))
--      will return [LeftUP . RightUP]
findInts :: LocTag -> PatternA -> [DesugaredSurfaceTerm -> DesugaredSurfaceTerm]
findInts anno = cata alg where
  alg = \case
    PatternPairF x y      -> ((. HLeft) <$> x) <> ((. HRight) <$> y)
    PatternIntF x         -> [id]
    PatternAnnotatedF x _ -> x
    _                     -> []

-- | Finds all PatternString leaves returning "directions" to these leaves through pairs
-- in the form of a combination of RightUP and LeftUP from the root
-- e.g. PatternPair (PatternVar "x") (PatternPair (PatternString "Hello, world!") (PatternVar "y"))
--      will return [LeftUP . RightUP]
findStrings :: LocTag -> PatternA -> [DesugaredSurfaceTerm -> DesugaredSurfaceTerm]
findStrings anno = cata alg where
  alg = \case
    PatternPairF x y      -> ((. HLeft) <$> x) <> ((. HRight) <$> y)
    PatternStringF x      -> [id]
    PatternAnnotatedF x _ -> x
    _                     -> []

findPatternVars :: LocTag -> PatternA
                -> Map String (DesugaredSurfaceTerm -> DesugaredSurfaceTerm)
findPatternVars anno = cata alg where
  alg = \case
    PatternPairF x y      -> ((. HLeft) <$> x) <> ((. HRight) <$> y)
    PatternVarF name      -> Map.singleton (locatedNameText name) id
    PatternAnnotatedF x _ -> x
    _                     -> Map.empty

-- TODO: Annotate without so much fuzz
pairStructureCheck :: PatternA -> DesugaredSurfaceTerm -> DesugaredSurfaceTerm
pairStructureCheck p upt = let a = GeneratedLoc "pairStructureCheck" Nothing in
  AppP (AppP (AppP (rewriteOuterTag a $ VarP "__case_foldl")
                      (VarP "__case_and"))
               (a :< IntUPF 1))
        ((a :<) . ListUPF $ ($ upt) <$> pairRoute2Dirs p)

pairRoute2Dirs :: PatternA -> [DesugaredSurfaceTerm -> DesugaredSurfaceTerm]
pairRoute2Dirs = cata alg where
  anno = (GeneratedLoc "pairRoute2Dirs" Nothing :<)
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

case2annidatedIfs :: DesugaredSurfaceTerm -- ^ Term to be pattern matched
                  -> [PatternA] -- ^ All patterns in a case expression
                  -> [DesugaredSurfaceTerm] -- ^ Int leaves on term
                  -> [DesugaredSurfaceTerm] -- ^ Int leaves on pattern
                  -> [DesugaredSurfaceTerm] -- ^ String leaves on term
                  -> [DesugaredSurfaceTerm] -- ^ String leaves on pattern
                  -> [DesugaredSurfaceTerm] -- ^ Case alternatives
                  -> DesugaredSurfaceTerm
case2annidatedIfs (anno :< _) [] [] [] [] [] [] =
  ITEP (anno :< IntUPF 1)
        (AppP (VarP "__case_abort") (anno :< StringUPF "Non-exhaustive patterns in case"))
        (anno :< IntUPF 0)
case2annidatedIfs x (aPattern:as) ((_ :< ListUPF []) : bs) ((_ :< ListUPF []) :cs) (dirs2StringOnUPT:ds) (dirs2StringOnPattern:es) (resultAlternative@(anno :< _):fs) =
  ITEP (AppP (AppP (rewriteOuterTag anno $ VarP "__case_and")
                   (AppP (AppP (VarP "__case_listEqual") dirs2StringOnUPT) dirs2StringOnPattern))
             (pairStructureCheck aPattern x))
       (mkCaseAlternative x resultAlternative aPattern)
       (case2annidatedIfs x as bs cs ds es fs)
case2annidatedIfs x (aPattern:as) (dirs2IntOnUPT:bs) (dirs2IntOnPattern:cs) ((_ :< ListUPF []) : ds) ((_ :< ListUPF []) : es) (resultAlternative@(anno :< _):fs) =
    ITEP (AppP (AppP (rewriteOuterTag anno $ VarP "__case_and")
                        (AppP (AppP (VarP "__case_listEqual") dirs2IntOnUPT) dirs2IntOnPattern))
                 (pairStructureCheck aPattern x))
          (mkCaseAlternative x resultAlternative aPattern)
          (case2annidatedIfs x as bs cs ds es fs)
case2annidatedIfs x (aPattern:as) (dirs2IntOnUPT:bs) (dirs2IntOnPattern:cs) (dirs2StringOnUPT:ds) (dirs2StringOnPattern:es) (resultAlternative@(anno :< _):fs) =
    ITEP (AppP (AppP (AppP (rewriteOuterTag anno $ VarP "__case_foldl")
                           (VarP "__case_and"))
                     (anno :< IntUPF 1))
               (anno :< ListUPF [ AppP (AppP (VarP "__case_listEqual") dirs2IntOnUPT) dirs2IntOnPattern
                                  , AppP (AppP (VarP "__case_listEqual") dirs2StringOnUPT) dirs2StringOnPattern
                                  , pairStructureCheck aPattern x
                                  ]))
          (mkCaseAlternative x resultAlternative aPattern)
          (case2annidatedIfs x as bs cs ds es fs)
case2annidatedIfs _ _ _ _ _ _ _ = error "case2annidatedIfs: lists don't match in size"

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
    anno C.:< CaseUPF x ls ->
      let duplicate x = (x,x)
          pairApplyList :: ([a -> a], a) -> [a]
          pairApplyList x = ($ snd x) <$> fst x
          patterns = fst <$> ls
          resultCaseAlts = snd <$> ls
          dirs2LeavesOnUPT f = fmap (\y -> anno :< ListUPF y) $ (($ x) <$>) . f <$> patterns
          dirs2LeavesOnPattern f = ((\a -> anno :< ListUPF a) . pairApplyList . bimap f (patternToTerm anno) . duplicate <$> patterns)
      in case2annidatedIfs x
                           patterns
                           (dirs2LeavesOnUPT (findInts anno))
                           (dirs2LeavesOnPattern $ findInts anno)
                           (dirs2LeavesOnUPT $ findStrings anno)
                           (dirs2LeavesOnPattern $ findStrings anno)
                           resultCaseAlts
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
addCaseHelperAliases term@(loc :< LetUPF bindings body) =
  loc :< LetUPF (aliases <> bindings) body
  where
    aliases =
      [ ( locatedName (GeneratedLoc ("case helper " <> name) (Just loc)) alias
        , loc :< UnprocessedParsedTermL (VarF name)
        )
      | (name, alias) <- [ ("and", "__case_and")
                         , ("foldl", "__case_foldl")
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
      LetUPF bindings body ->
        let scope' = foldr updateScope scope bindings
        in anno :< LetUPF (fmap (fmap $ go scope') bindings) (go scope' body)
      CaseUPF scrutinee alternatives ->
        anno :< CaseUPF (go scope scrutinee)
          [ (mapPattern scope pattern', go (scope Set.\\ patternVars pattern') body)
          | (pattern', body) <- alternatives
          ]
      other -> anno :< fmap (go scope) other

    updateScope (name, _) =
      let text = locatedNameText name
      in if locatedNameLoc name == BuiltinLoc text
           then Set.insert text
           else Set.delete text

    patternVars :: PatternA -> Set String
    patternVars = cata $ \case
      PatternVarF name      -> Set.singleton (locatedNameText name)
      PatternAnnotatedF p _ -> p
      p                     -> F.fold p

    mapPattern :: Set String -> PatternA -> PatternA
    mapPattern scope = cata $ \case
      PatternAnnotatedF p (AnnotatedEST annotation) ->
        embed $ PatternAnnotatedF p (AnnotatedEST $ go scope annotation)
      p -> embed p

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
