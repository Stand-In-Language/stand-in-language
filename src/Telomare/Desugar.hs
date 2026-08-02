{-# LANGUAGE LambdaCase #-}

-- |Post-parse desugaring: @AUPT -> AUPT@ rewrites over the surface AST.
-- Case expressions are lowered to nested if/else chains ('removeCaseUPs'),
-- builtin names are bound ('addBuiltins') and partially applied builtins
-- are rewritten to direct forms ('optimizeBuiltinFunctions').
--
-- Sugar with no surface-AST representation (multi-pattern lambdas, list
-- assignments, UDT declarations) is expanded during parsing instead, by
-- 'Telomare.Parse.Sugar'.
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
findInts :: LocTag -> PatternA -> [AUPT -> AUPT]
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
findStrings :: LocTag -> PatternA -> [AUPT -> AUPT]
findStrings anno = cata alg where
  alg = \case
    PatternPairF x y      -> ((. HLeft) <$> x) <> ((. HRight) <$> y)
    PatternStringF x      -> [id]
    PatternAnnotatedF x _ -> x
    _                     -> []

fitPatternVarsToCasedUPT :: PatternA -> AUPT -> AUPT
fitPatternVarsToCasedUPT p aupt@(anno :< _) = applyVars2UPT varsOnUPT $ pattern2UPT anno p where
  varsOnUPT :: Map String AUPT
  varsOnUPT = ($ aupt) <$> findPatternVars anno p
  applyVars2UPT :: Map String AUPT
                -> AUPT
                -> AUPT
  applyVars2UPT m = \case
    LamP str x ->
      case Map.lookup (locatedNameText str) m of
        Just a  -> AppP (LamP str (applyVars2UPT m x)) a
        Nothing -> LamP str x
    x -> x


findPatternVars :: LocTag -> PatternA -> Map String (AUPT -> AUPT)
findPatternVars anno = cata alg where
  alg = \case
    PatternPairF x y      -> ((. HLeft) <$> x) <> ((. HRight) <$> y)
    PatternVarF str       -> Map.singleton str id
    PatternAnnotatedF x _ -> x
    _                     -> Map.empty

-- TODO: Annotate without so much fuzz
pairStructureCheck :: PatternA -> AUPT -> AUPT
pairStructureCheck p upt = let a = GeneratedLoc "pairStructureCheck" Nothing in
  AppP (AppP (AppP (rewriteOuterTag a $ VarP "foldl")
                      (VarP "and"))
               (a :< IntUPF 1))
        ((a :<) . ListUPF $ ($ upt) <$> pairRoute2Dirs p)

pairRoute2Dirs :: PatternA -> [AUPT -> AUPT]
pairRoute2Dirs = cata alg where
  anno = (GeneratedLoc "pairRoute2Dirs" Nothing :<)
  alg = \case
    PatternPairF x y      -> [id] <> ((. HLeft) <$> x) <> ((. HRight) <$> y)
    PatternAnnotatedF x _ -> x
    _                     -> []

pattern2UPT :: LocTag -> PatternA -> AUPT
pattern2UPT anno = cata alg where
  alg = \case
    PatternPairF x y       -> PairP x y
    PatternIntF i          -> anno :< IntUPF i
    PatternStringF str     -> anno :< StringUPF str
    PatternVarF str        -> anno :< IntUPF 0
    PatternIgnoreF         -> anno :< IntUPF 0
    PatternAnnotatedF x _  -> x
      -- Note that "__ignore" is a special variable name and not accessible to users because
      -- parsing of VarUPs doesn't allow variable names to start with `_`

mkCaseAlternative :: AUPT -- ^ UPT to be cased
                  -> AUPT -- ^ Case result to be made lambda and applied
                  -> PatternA -- ^ Pattern
                  -> AUPT -- ^ case result as a lambda applied to the appropirate part of the UPT to be cased
mkCaseAlternative casedUPT@(anno :< _) caseResult p = appVars2ResultLambdaAlts patternVarsOnUPT . makeLambdas caseResult . keys $ patternVarsOnUPT where
  patternVarsOnUPT :: Map String AUPT
  patternVarsOnUPT = ($ casedUPT) <$> findPatternVars anno p
  appVars2ResultLambdaAlts :: Map String AUPT
                           -> AUPT -- ^ case result as lambda
                           -> AUPT
  appVars2ResultLambdaAlts m = \case
    lam@(LamP varName upt) ->
      case Map.lookup (locatedNameText varName) m of
        Nothing -> lam
        Just x -> AppP (LamP varName (appVars2ResultLambdaAlts (Map.delete (locatedNameText varName) m) upt)) x
    x -> x
  makeLambdas :: AUPT
              -> [String]
              -> AUPT
  makeLambdas aupt@(anno' :< _) = \case
    []     -> aupt
    (x:xs) -> LamP (locatedName anno' x) (makeLambdas aupt xs)

case2annidatedIfs :: AUPT -- ^ Term to be pattern matched
                  -> [PatternA] -- ^ All patterns in a case expression
                  -> [AUPT] -- ^ Int leaves as ListUPs on UPT
                  -> [AUPT] -- ^ Int leaves as ListUPs on pattern
                  -> [AUPT] -- ^ String leaves as ListUPs on UPT
                  -> [AUPT] -- ^ String leaves as ListUPs on pattern
                  -> [AUPT] -- ^ Case's alternatives
                  -> AUPT
case2annidatedIfs (anno :< _) [] [] [] [] [] [] =
  ITEP (anno :< IntUPF 1)
        (AppP (VarP "abort") (anno :< StringUPF "Non-exhaustive patterns in case"))
        (anno :< IntUPF 0)
case2annidatedIfs x (aPattern:as) ((_ :< ListUPF []) : bs) ((_ :< ListUPF []) :cs) (dirs2StringOnUPT:ds) (dirs2StringOnPattern:es) (resultAlternative@(anno :< _):fs) =
  ITEP (AppP (AppP (rewriteOuterTag anno $ VarP "and")
                   (AppP (AppP (VarP "listEqual") dirs2StringOnUPT) dirs2StringOnPattern))
             (pairStructureCheck aPattern x))
       (mkCaseAlternative x resultAlternative aPattern)
       (case2annidatedIfs x as bs cs ds es fs)
case2annidatedIfs x (aPattern:as) (dirs2IntOnUPT:bs) (dirs2IntOnPattern:cs) ((_ :< ListUPF []) : ds) ((_ :< ListUPF []) : es) (resultAlternative@(anno :< _):fs) =
    ITEP (AppP (AppP (rewriteOuterTag anno $ VarP "and")
                        (AppP (AppP (VarP "listEqual") dirs2IntOnUPT) dirs2IntOnPattern))
                 (pairStructureCheck aPattern x))
          (mkCaseAlternative x resultAlternative aPattern)
          (case2annidatedIfs x as bs cs ds es fs)
case2annidatedIfs x (aPattern:as) (dirs2IntOnUPT:bs) (dirs2IntOnPattern:cs) (dirs2StringOnUPT:ds) (dirs2StringOnPattern:es) (resultAlternative@(anno :< _):fs) =
    ITEP (AppP (AppP (AppP (rewriteOuterTag anno $ VarP "foldl")
                           (VarP "and"))
                     (anno :< IntUPF 1))
               (anno :< ListUPF [ AppP (AppP (VarP "listEqual") dirs2IntOnUPT) dirs2IntOnPattern
                                  , AppP (AppP (VarP "listEqual") dirs2StringOnUPT) dirs2StringOnPattern
                                  , pairStructureCheck aPattern x
                                  ]))
          (mkCaseAlternative x resultAlternative aPattern)
          (case2annidatedIfs x as bs cs ds es fs)
case2annidatedIfs _ _ _ _ _ _ _ = error "case2annidatedIfs: lists don't match in size"

removeCaseUPs :: AUPT -> AUPT
removeCaseUPs = cata go where
  go = \case
    anno C.:< CaseUPF x ls ->
      let duplicate x = (x,x)
          pairApplyList :: ([a -> a], a) -> [a]
          pairApplyList x = ($ snd x) <$> fst x
          patterns = fst <$> ls
          resultCaseAlts = snd <$> ls
          dirs2LeavesOnUPT f = fmap (\y -> anno :< ListUPF y) $ (($ x) <$>) . f <$> patterns
          dirs2LeavesOnPattern f = ((\a -> anno :< ListUPF a) . pairApplyList . bimap f (pattern2UPT anno) . duplicate <$> patterns)
      in case2annidatedIfs x
                           patterns
                           (dirs2LeavesOnUPT (findInts anno))
                           (dirs2LeavesOnPattern $ findInts anno)
                           (dirs2LeavesOnUPT $ findStrings anno)
                           (dirs2LeavesOnPattern $ findStrings anno)
                           resultCaseAlts
    x -> embed x


rewriteOuterTag :: anno -> Cofree a anno -> Cofree a anno
rewriteOuterTag anno (_ :< x) = anno :< x


optimizeBuiltinFunctions :: AUPT -> AUPT
optimizeBuiltinFunctions = cata f where
  f = \case
    twoApp@(AppAFP a (GFix (AppAFP _ f x)) y) ->
      case project f of
        VarAFP _ "pair" -> embed $ PairAFP a x y
        VarAFP _ "app"  -> embed $ AppAFP a x y
        _               -> embed twoApp
    oneApp@(AppAFP a f x) ->
      case project f of
        VarAFP _ "left" -> HLeft x
        VarAFP _ "right" -> HRight x
        VarAFP _ "trace" -> a :< UnprocessedParsedTermH (HTraceF x)
        VarAFP _ "pair" -> embed $ LamAFP a (locatedName a "y") (PairP x (embed $ VarAFP a "y"))
        VarAFP _ "app" -> embed $ LamAFP a (locatedName a "y") (AppP x (embed $ VarAFP a "y"))
        _             -> embed oneApp
    x -> embed x


addBuiltins :: AUPT -> AUPT
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
    tagBuiltin :: String -> Fix (UnprocessedParsedTermF PatternA) -> AUPT
    tagBuiltin n = tag (BuiltinLoc n)
    builtin = BuiltinLoc
    bind name value = (locatedName (builtin name) name, value)


