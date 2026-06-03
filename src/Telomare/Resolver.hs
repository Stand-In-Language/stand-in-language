{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Telomare.Resolver where

import Codec.Binary.UTF8.String (encode)
import Control.Comonad.Cofree (Cofree (..), unwrap)
import Control.Comonad.Trans.Cofree (CofreeF)
import qualified Control.Comonad.Trans.Cofree as C
import Control.Lens.Combinators (transform)
import Control.Monad (forM, forM_, (<=<))
import Control.Monad.Identity (Identity (..))
import Control.Monad.Reader (MonadReader (ask), reader, runReaderT)
import Control.Monad.State (StateT, evalStateT)
import qualified Control.Monad.State as State
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Reader (ReaderT, local)
import Control.Monad.Trans.Writer.Strict (WriterT (..), tell, writer)
import Crypto.Hash (Digest, SHA256, hash)
import Data.Bifunctor (Bifunctor (first, second), bimap)
import qualified Data.ByteArray as BA
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Char (ord)
import Data.Fix (Fix)
import qualified Data.Foldable as F
import Data.Functor.Foldable (Base, Corecursive (ana, apo, embed),
                              Recursive (cata))
import Data.List (delete, elem, elemIndex, find, foldl', intercalate, nubBy,
                  zip4)
import qualified Data.Map as Map
import Data.Map.Strict (Map, fromList, keys)
import Data.Monoid (Sum (..))
import Data.Set (Set, (\\))
import qualified Data.Set as Set
import Debug.Trace (trace, traceShow, traceShowId)
import PrettyPrint (prettyPrint)
import Telomare
import Telomare.Parser (AnnotatedUPT (unAnnotatedUPT, AnnotatedUPT), TelomareParser, identifier, PatternA, AUPT, appAUPT, iteAUPT)
import Text.Megaparsec (errorBundlePretty, runParser)

debug :: Bool
debug = False

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

-- |Int to ParserTerm
i2t :: a -> Int -> Cofree (ParserTermF l v) a
i2t anno = ana coalg where
  coalg 0 = anno C.:< ParserTermB ZeroSF
  coalg n = anno C.:< ParserTermB (PairSF (n-1) 0)

-- |List of Int's to ParserTerm
ints2t :: Foldable t => a -> t Int -> Cofree (ParserTermF l v) a
ints2t anno = foldr ((\x y -> anno :< ParserTermB (PairSF x y)) . i2t anno) (anno :< ParserTermB ZeroSF)

-- |String to ParserTerm
s2t :: (Foldable t, Functor t) => a -> t Char -> Cofree (ParserTermF l v) a
s2t anno = ints2t anno . fmap ord

instance MonadFail (Either ResolverError) where
  fail = Left . MissingDefinitions . pure

-- | Finds all PatternInt leaves returning "directions" to these leaves through pairs
-- in the form of a combination of RightUP and LeftUP from the root
-- e.g. PatternPair (PatternVar "x") (PatternPair (PatternInt 0) (PatternVar "y"))
--      will return [LeftUP . RightUP]
findInts :: LocTag -> PatternA -> [AUPT -> AUPT]
findInts anno = cata alg where
  alg = \case
    PatternPairF x y      -> ((. (anno :< ) . LeftUPF) <$> x) <> ((. (anno :< ) . RightUPF) <$> y)
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
    PatternPairF x y      -> ((. (anno :< ) . LeftUPF) <$> x) <> ((. (anno :< ) . RightUPF) <$> y)
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
    anno :< LamUPF str x ->
      case Map.lookup (locatedNameText str) m of
        Just a  -> anno :< AppUPF (anno :< LamUPF str (applyVars2UPT m x)) a
        Nothing -> anno :< LamUPF str x
    x -> x

-- |Collect all free variable names in a `AnnotatedUPT` expresion
varsUPT :: AUPT -> Set String
varsUPT = cata alg' where
  alg' (_ C.:< x) = alg x
  alg (VarUPF n)     = Set.singleton n
  alg (LamUPF str x) = del (locatedNameText str) x
  alg e              = F.fold e
  del :: String -> Set String -> Set String
  del n x = if Set.member n x then Set.delete n x else x

-- |Like 'varsUPT' but also descends into 'Pattern' type annotations so that
-- names referenced via @: T@ patterns (e.g. UDT validators) are included.
freeVarsDeep :: AUPT -> Set String
freeVarsDeep = cata alg' where
  alg' (_ C.:< x) = alg x
  alg (VarUPF n)           = Set.singleton n
  alg (LamUPF n body)      = Set.delete (locatedNameText n) body
  alg (CaseUPF scrut alts) = scrut <> foldMap (\(p, body) -> patternRefs p <> body) alts <> caseRefs
    where
      caseRefs = Set.fromList ["and", "listEqual", "foldl", "abort"]
  alg e                    = F.fold e

  patternRefs :: PatternA -> Set String
  patternRefs = cata palg where
    palg :: PatternF AnnotatedUPT (Set String) -> Set String
    palg (PatternAnnotatedF inner ty) = inner <> freeVarsDeep (unAnnotatedUPT ty)
    palg e                            = F.fold e

-- |Keep only bindings transitively reachable from @root@. Unreachable
-- bindings are skipped by 'process' and 'compile', giving large speedups
-- when a snippet only uses a small slice of a large Prelude+UDT environment.
--
-- 'freeVarsDeep' also accounts for names that 'removeCaseUPs' (called
-- inside 'process') injects into case alternatives: @and@, @listEqual@,
-- @foldl@, @abort@. Without these the pruned LetUPF would fail with
-- MissingDefinitions after case expansion.
pruneBindings :: AUPT -> [(String, AUPT)] -> [(String, AUPT)]
pruneBindings root bs = filter ((`Set.member` reachable) . fst) bs
  where
    seed      = freeVarsDeep root
    bmap      = Map.fromList $ fmap (second freeVarsDeep) bs
    expand r  = r <> F.fold (Map.restrictKeys bmap r)
    reachable = until (\s -> expand s == s) expand seed

mkLambda4FreeVarUPs :: AUPT -> AUPT
mkLambda4FreeVarUPs aupt@(anno :< _) = go aupt freeVars where
  freeVars = Set.toList . varsUPT $ aupt
  go x = \case
    []     -> x
    (y:ys) -> embed . (anno C.:<) . LamUPF (locatedName UnknownLoc y) $ go x ys

findPatternVars :: LocTag -> PatternA -> Map String (AUPT -> AUPT)
findPatternVars anno = cata alg where
  alg = \case
    PatternPairF x y      -> ((. (anno :< ). LeftUPF) <$> x) <> ((. (anno :< ). RightUPF) <$> y)
    PatternVarF str       -> Map.singleton str id
    PatternAnnotatedF x _ -> x
    _                     -> Map.empty

-- TODO: Annotate without so much fuzz
pairStructureCheck :: PatternA -> AUPT -> AUPT
pairStructureCheck p upt = let a = GeneratedLoc "pairStructureCheck" Nothing
                               appAUPT' = appAUPT "pairStructureCheck"
  in
  appAUPT' (appAUPT' (appAUPT' (a :< VarUPF "foldl")
                      (a :< VarUPF "and"))
               (a :< IntUPF 1))
        ((a :<) . ListUPF $ ($ upt) <$> pairRoute2Dirs p)

pairRoute2Dirs :: PatternA -> [AUPT -> AUPT]
pairRoute2Dirs = cata alg where
  anno = (GeneratedLoc "pairRoute2Dirs" Nothing :<)
  alg = \case
    PatternPairF x y      -> [id] <> ((. anno . LeftUPF) <$> x) <> ((. anno . RightUPF) <$> y)
    PatternAnnotatedF x _ -> x
    _                     -> []

pattern2UPT :: LocTag -> PatternA -> AUPT
pattern2UPT anno = cata alg where
  alg = \case
    PatternPairF x y       -> anno :< PairUPF x y
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
    lam@(_ :< LamUPF varName upt) ->
      case Map.lookup (locatedNameText varName) m of
        Nothing -> lam
        Just x -> anno :< AppUPF (anno :< LamUPF varName (appVars2ResultLambdaAlts (Map.delete (locatedNameText varName) m) upt)) x
    x -> x
  makeLambdas :: AUPT
              -> [String]
              -> AUPT
  makeLambdas aupt@(anno' :< _) = \case
    []     -> aupt
    (x:xs) -> anno' :< LamUPF (locatedName anno' x) (makeLambdas aupt xs)

case2annidatedIfs :: AUPT -- ^ Term to be pattern matched
                  -> [PatternA] -- ^ All patterns in a case expression
                  -> [AUPT] -- ^ Int leaves as ListUPs on UPT
                  -> [AUPT] -- ^ Int leaves as ListUPs on pattern
                  -> [AUPT] -- ^ String leaves as ListUPs on UPT
                  -> [AUPT] -- ^ String leaves as ListUPs on pattern
                  -> [AUPT] -- ^ Case's alternatives
                  -> AUPT
case2annidatedIfs (anno :< _) [] [] [] [] [] [] =
  iteAUPT "case2annidatedIfs" (anno :< IntUPF 1)
        (appAUPT "case2annidatedIfs" (anno :< VarUPF "abort") (anno :< StringUPF "Non-exhaustive patterns in case"))
        (anno :< IntUPF 0)
case2annidatedIfs x (aPattern:as) ((_ :< ListUPF []) : bs) ((_ :< ListUPF []) :cs) (dirs2StringOnUPT:ds) (dirs2StringOnPattern:es) (resultAlternative@(anno :< _):fs) = let appAUPT' = appAUPT "case2annidatedIfs" in
    iteAUPT "case2annidatedIfs" (appAUPT' (appAUPT' (anno :< VarUPF "and")
                        (appAUPT' (appAUPT' (anno :< VarUPF "listEqual") dirs2StringOnUPT) dirs2StringOnPattern))
                 (pairStructureCheck aPattern x))
          (mkCaseAlternative x resultAlternative aPattern)
          (case2annidatedIfs x as bs cs ds es fs)
case2annidatedIfs x (aPattern:as) (dirs2IntOnUPT:bs) (dirs2IntOnPattern:cs) ((_ :< ListUPF []) : ds) ((_ :< ListUPF []) : es) (resultAlternative@(anno :< _):fs) = let appAUPT' = appAUPT "case2annidatedIfs" in
    iteAUPT "case2annidatedIfs" (appAUPT' (appAUPT' (anno :< VarUPF "and")
                        (appAUPT' (appAUPT' (anno :< VarUPF "listEqual") dirs2IntOnUPT) dirs2IntOnPattern))
                 (pairStructureCheck aPattern x))
          (mkCaseAlternative x resultAlternative aPattern)
          (case2annidatedIfs x as bs cs ds es fs)
case2annidatedIfs x (aPattern:as) (dirs2IntOnUPT:bs) (dirs2IntOnPattern:cs) (dirs2StringOnUPT:ds) (dirs2StringOnPattern:es) (resultAlternative@(anno :< _):fs) = let appAUPT' = appAUPT "case2annidatedIfs" in
    iteAUPT "case2annidatedIfs" (appAUPT' (appAUPT' (appAUPT' (anno :< VarUPF "foldl")
                                (anno :< VarUPF "and"))
                        (anno :< IntUPF 1))
                 (anno :< ListUPF [ appAUPT' (appAUPT' (anno :< VarUPF "listEqual") dirs2IntOnUPT) dirs2IntOnPattern
                                  , appAUPT' (appAUPT' (anno :< VarUPF "listEqual") dirs2StringOnUPT) dirs2StringOnPattern
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

type VarList = [String]

debruijinize :: MonadFail m => VarList -> Term1 -> m Term2
debruijinize vl = \case
  (anno :< (ParserTermB ZeroSF)) -> pure $ anno :< ParserTermB ZeroSF
  (anno :< (ParserTermB (PairSF a b))) -> (\x y -> anno :< ParserTermB (PairSF x y)) <$> debruijinize vl a <*> debruijinize vl b
  (anno :< TVarF n) -> case elemIndex n vl of
               Just i  -> pure $ anno :< TVarF i
               Nothing -> fail ("undefined identifier " <> n)
  (anno :< TAppF i c) -> (\x y -> anno :< TAppF x y) <$> debruijinize vl i <*> debruijinize vl c
  (anno :< TCheckF c tc) -> (\x y -> anno :< TCheckF x y) <$> debruijinize vl c <*> debruijinize vl tc
  (anno :< TITEF i t e) -> (\x y z -> anno :< TITEF x y z) <$> debruijinize vl i
                                                           <*> debruijinize vl t
                                                           <*> debruijinize vl e
  (anno :< TLeftF x) -> (\y -> anno :< TLeftF y) <$> debruijinize vl x
  (anno :< TRightF x) -> (\y -> anno :< TRightF y) <$> debruijinize vl x
  (anno :< TTraceF x) -> (\y -> anno :< TTraceF y) <$> debruijinize vl x
  (anno :< THashF x) -> (\y -> anno :< THashF y) <$> debruijinize vl x
  (anno :< TLamF (Open n) x) -> (\y -> anno :< TLamF (Open ()) y) <$> debruijinize (n : vl) x
  (anno :< TLamF (Closed n) x) -> (\y -> anno :< TLamF (Closed ()) y) <$> debruijinize (n : vl) x
  (anno :< TChurchF n) -> pure $ anno :< TChurchF n
  (anno :< TLimitedRecursionF t r b) -> (\x y z -> anno :< TLimitedRecursionF x y z) <$> debruijinize vl t <*> debruijinize vl r <*> debruijinize vl b
  (anno :< TUnsizedRepeaterF) -> pure $ anno :< TUnsizedRepeaterF

-- | Close all naked open lambdas
closeLams :: Term2 -> Term2
closeLams = runIdentity .($ True) . runReaderT . cata f where
  f = \case
    anno C.:< x -> case x of
      TLamF lt ix -> ask >>= \naked -> if naked
        then (\x' -> anno :< TLamF (Closed ()) x') <$> local (const False) ix
        else (\x' -> anno :< TLamF lt x') <$> local (const False) ix
      x' -> (anno :<) <$> sequence x'

debruijinizeApp :: forall m. (Monad m, MonadFail m) => Term1 -> m Term2
debruijinizeApp = fmap closeLams . ($ []) . runReaderT . cata f where
  f = \case
    anno C.:< x -> case x of
      TLamF lt ix -> (\lx -> anno :< TLamF (convLam lt) lx) <$> local (lt:) ix
      TVarF n     -> ask >>= \vl -> lift $ findElem anno n vl
      x           -> fmap (anno :<) . sequence $ conv x
  conv = \case
    ParserTermB x -> ParserTermB x
    TAppF c i -> TAppF c i
    TCheckF tc c -> TCheckF tc c
    TITEF i t e -> TITEF i t e
    TLeftF x -> TLeftF x
    TRightF x -> TRightF x
    TTraceF x -> TTraceF x
    THashF x -> THashF x
    TChurchF n -> TChurchF n
    TLimitedRecursionF t r b -> TLimitedRecursionF t r b
    TUnsizedRepeaterF -> TUnsizedRepeaterF
  convLam = \case
    Open _ -> Open ()
    Closed _ -> Closed ()
    LetBinding _ _ -> Open ()
  findElem anno n vl = case find (ff n) (zip [0..] vl) of
    Just (i, LetBinding c _) -> pure $ iterate (\ix -> anno :< TAppF ix (anno :< TUnsizedRepeaterF)) (anno :< TVarF i) !! c
    Just (i, _) -> pure $ anno :< TVarF i
    _ -> fail $ "undefined identifier " <> n
  ff n = \case
    (_, Open n') | n' == n -> True
    (_, Closed n') | n' == n -> True
    (_, LetBinding _ n') | n' == n -> True
    _ -> False


rewriteOuterTag :: anno -> Cofree a anno -> Cofree a anno
rewriteOuterTag anno (_ :< x) = anno :< x

splitExpr :: Term2 -> Term3
splitExpr = flip State.evalState (toEnum 0, toEnum 0) . cata f where
  f = \case
    (anno C.:< g) -> rewriteOuterTag anno <$> case g of
      ParserTermB ZeroSF -> pure zeroB
      ParserTermB (PairSF a b) -> pairS a b
      TVarF n -> pure $ varB n
      TAppF c i -> appS c i
      TCheckF tc c -> (\tc' c' -> anno :< Term3CheckingWrapper anno tc' c') <$> tc <*> c
      TITEF i t e -> iteB_ <$> i <*> t <*> e
      TLeftF x -> leftB <$> x
      TRightF x -> rightB <$> x
      TTraceF x -> x -- TODO add trace back in, or rethink
      TLamF (Open ()) x -> lamS x
      TLamF (Closed ()) x -> clamS x
      TChurchF n -> i2CB anno n
      TLimitedRecursionF t r b -> unsizedRecursionWrapper anno t r b
      TUnsizedRepeaterF -> do
        urt <- State.gets snd
        State.modify (\(fi, _) -> (fi, succ urt))
        repeaterAndAbort anno urt

openLambda :: String -> Term1 -> Term1
openLambda name body@(anno :< _) = anno :< TLamF (Open name) body

closedLambda :: String -> Term1 -> Term1
closedLambda name body@(anno :< _) = anno :< TLamF (Closed name) body

-- |Transformation from `AnnotatedUPT` to `Term1` validating and inlining `VarUP`s
validateVariables :: AnnotatedUPT
                  -> Either ResolverError Term1
validateVariables (AnnotatedUPT term) =
  let
      validateWithEnvironment = \case
        anno :< LetUPF preludeMap inner -> do
          oldPrelude <- State.get

          -- Build dependency graph
          let dependencies :: Map String (Set String)
              dependencies = Map.fromList
                [(locatedNameText name, Set.fromList $ getDirectDeps def) | (name, def) <- preludeMap]

              -- Get direct variable dependencies (only those defined in this let block)
              -- Uses Set to properly handle lambda-bound variable shadowing
              letBindingNames = Set.fromList (letBindingName <$> preludeMap)
              getDirectDeps = Set.toList . cata alg where
                alg = \case
                    (_ C.:< VarUPF n) -> if Set.member n letBindingNames then Set.singleton n else Set.empty
                    (_ C.:< LamUPF v body) -> Set.delete (locatedNameText v) body
                    (_ C.:< LetUPF binds body) ->
                      let boundNames = Set.fromList (letBindingName <$> binds)
                          bindDeps = foldMap letBindingValue binds
                      in Set.union (bindDeps Set.\\ boundNames) (body Set.\\ boundNames)
                    (_ C.:< ITEUPF i t e) -> i <> t <> e
                    (_ C.:< PairUPF a b) -> a <> b
                    (_ C.:< ListUPF l) -> F.fold l
                    (_ C.:< AppUPF f x) -> f <> x
                    (_ C.:< UnsizedRecursionUPF t r b) -> t <> r <> b
                    (_ C.:< LeftUPF x) -> x
                    (_ C.:< RightUPF x) -> x
                    (_ C.:< TraceUPF x) -> x
                    (_ C.:< CheckUPF cf x) -> cf <> x
                    (_ C.:< HashUPF x) -> x
                    _ -> Set.empty

          -- Check if original order works (no forward references)
          let originalOrder = letBindingName <$> preludeMap
              hasForwardRef = any (\(i, name) ->
                let deps = Map.findWithDefault Set.empty name dependencies
                    laterNames = Set.fromList $ drop (i + 1) originalOrder
                in not . Set.null $ deps `Set.intersection` laterNames
                ) (zip [0..] originalOrder)
              -- Topological sort with cycle detection
              topologicalSort :: [String] -> Map String (Set String) -> Either ResolverError [String]
              topologicalSort names deps = go [] Set.empty names
                where
                  go :: [String] -> Set String -> [String] -> Either ResolverError [String]
                  go result _ [] = Right (reverse result)
                  go result inProgress remaining =
                    case find (canProcess remaining inProgress) remaining of
                      Nothing ->
                        -- Must be a cycle - find it for error message
                        let findCycleFrom start = go' start Set.empty
                              where go' curr visited
                                      | curr `Set.member` visited = [curr]
                                      | otherwise =
                                          case find (`elem` remaining) (Set.toList $ Map.findWithDefault Set.empty curr deps) of
                                            Nothing -> []
                                            Just next -> curr : go' next (Set.insert curr visited)
                        in Left $ DefinitionCycle (findCycleFrom (head remaining))
                      Just name ->
                        let inProgress' = inProgress `Set.union`
                                         Map.findWithDefault Set.empty name deps
                        in go (name : result) inProgress' (delete name remaining)

                  canProcess rn inProgress name =
                    all (`notElem` rn) (Set.toList $ Map.findWithDefault Set.empty name deps)

                  delete x = filter (/= x)

          -- Only reorder if necessary
          sortedBindings <- if hasForwardRef
            then case topologicalSort originalOrder dependencies of
              Left cycle -> State.lift . Left $ cycle
              Right sortedNames ->
                pure [(name, def) | name <- sortedNames,
                      (name', def) <- preludeMap, name == locatedNameText name']
            else pure $ first locatedNameText <$> preludeMap  -- Keep original order

          -- Process bindings in order
          forM_ sortedBindings $ \(name, def) -> do
            validatedDef <- validateWithEnvironment def
            State.modify (Map.insert name validatedDef)

          result <- validateWithEnvironment inner
          State.put oldPrelude
          pure result
        anno :< LamUPF v x -> do
          oldState <- State.get
          State.modify (Map.insert (locatedNameText v) (anno :< TVarF (locatedNameText v)))
          result <- validateWithEnvironment x
          State.put oldState
          pure $ openLambda (locatedNameText v) result
        anno :< VarUPF n -> do
          definitionsMap <- State.get
          case Map.lookup n definitionsMap of
            Just v -> pure v
            _      -> State.lift . Left $ MissingDefinitionAt anno n

        anno :< ITEUPF i t e -> (\a b c -> anno :< TITEF a b c) <$> validateWithEnvironment i
                                                                <*> validateWithEnvironment t
                                                                <*> validateWithEnvironment e
        anno :< IntUPF x -> pure $ i2t anno x
        anno :< StringUPF s -> pure $ s2t anno s
        anno :< PairUPF a b -> (\x y -> anno :< ParserTermB (PairSF x y)) <$> validateWithEnvironment a
                                                            <*> validateWithEnvironment b
        anno :< ListUPF l -> foldr (\x y -> anno :< ParserTermB (PairSF x y)) (anno :< ParserTermB ZeroSF) <$> mapM validateWithEnvironment l
        anno :< AppUPF f x -> (\a b -> anno :< TAppF a b) <$> validateWithEnvironment f
                                                          <*> validateWithEnvironment x
        anno :< UnsizedRecursionUPF t r b ->
          (\x y z -> anno :< TAppF (anno :< TLimitedRecursionF x y z) (anno :< TUnsizedRepeaterF))
          <$> validateWithEnvironment t
          <*> validateWithEnvironment r
          <*> validateWithEnvironment b
        anno :< ChurchUPF n -> pure $ anno :< TChurchF n
        anno :< LeftUPF x -> (\y -> anno :< TLeftF y) <$> validateWithEnvironment x
        anno :< RightUPF x -> (\y -> anno :< TRightF y) <$> validateWithEnvironment x
        anno :< TraceUPF x -> (\y -> anno :< TTraceF y) <$> validateWithEnvironment x
        anno :< CheckUPF cf x -> (\y y'-> anno :< TCheckF y y') <$> validateWithEnvironment cf <*> validateWithEnvironment x
        anno :< HashUPF x -> (\y -> anno :< THashF y) <$> validateWithEnvironment x
  in State.evalStateT (validateWithEnvironment term) Map.empty

annotateUnsizedCount :: AUPT -> Cofree (UnprocessedParsedTermF PatternA) (LocTag, Int)
annotateUnsizedCount = capTop . flip evalStateT 0 . cata f where
  f = \case
    anno C.:< x -> case x of
      ur@(UnsizedRecursionUPF _ _ _) -> sequence ur >>= \nur -> do
        n <- State.get
        State.put (n + 1)
        lift (Set.singleton n, (anno, 0) :< AppUPF ((anno, 0) :< nur) ((anno, 0) :< VarUPF (':' : show n)))
      LetUPF bindings inner -> (\b i -> (anno, 0) :< LetUPF b i) <$> traverse rebind bindings <*> inner
      x -> ((anno, 0) :<) <$> sequence x
  rebind (n, x) = (\(n', x') -> (n, x')) <$> cap (locatedNameText n) (evalStateT x 0)
  cap n (vs, x@((anno, _) :< _)) = lift (Set.empty, (n, foldr (\v b -> (anno, length vs) :< LamUPF (locatedName anno (':' : show v)) b) x vs))
  -- HACK vars are just placehorders for next step
  capTop (vs, x@((anno, _) :< _)) =
    foldr (\v b -> (anno, length vs) :< AppUPF ((anno, 0) :< LamUPF (locatedName anno (':' : show v)) b) ((anno, 0) :< VarUPF (':' : show v))) x vs


-- convert let bindings to nested lambda/app brackets
letsToApps :: AnnotatedUPT -> Either ResolverError Term1
letsToApps (AnnotatedUPT term) =
   -- Topological sort with cycle detection
  let topologicalSort :: [String] -> Map String (Set String) -> Either ResolverError [String]
      topologicalSort names deps = go [] Set.empty names
        where
          go :: [String] -> Set String -> [String] -> Either ResolverError [String]
          go result _ [] = Right result
          go result inProgress remaining =
            case find (canProcess remaining inProgress) remaining of
              Nothing ->
                -- Must be a cycle - find it for error message
                let findCycleFrom start = go' start Set.empty
                      where go' curr visited
                              | curr `Set.member` visited = [curr]
                              | otherwise =
                                  case find (`elem` remaining) (Set.toList $ Map.findWithDefault Set.empty curr deps) of
                                    Nothing -> []
                                    Just next -> curr : go' next (Set.insert curr visited)
                in Left $ DefinitionCycle (findCycleFrom (head remaining))
              Just name ->
                let inProgress' = inProgress `Set.union`
                                  Map.findWithDefault Set.empty name deps
                in go (name : result) inProgress' (delete name remaining)

          canProcess rn inProgress name =
            all (`notElem` rn) (Set.toList $ Map.findWithDefault Set.empty name deps)

          delete x = filter (/= x)
      getTransitive :: Map String (Set String) -> String -> Set String
      getTransitive deps n = Set.singleton n <> case Map.lookup n deps of
        Just s | not (null s) -> mconcat . fmap (getTransitive deps) $ Set.toList s
        _ -> Set.empty
      getTransitive' deps = mconcat . fmap (getTransitive deps) . Set.toList
      makeBindingsAsoc (name, def) = case runWriterT def of
        Left s           -> Left s
        Right (nx, refs) -> pure (locatedNameText name, (nx,refs))
      -- f algebra builds Term1 wrapped with metadata (WriterT) of unbound refs (Set String) or ResolverError
      buildRefs ((anno, urC) C.:< upf) = case upf of
        VarUPF n -> writer ((anno, urC) :< TVarF n, Set.singleton n)
        LamUPF v x -> f (runWriterT x) where
          name = locatedNameText v
          f (Right (nx, refs)) = let nrefs = Set.delete name refs in if null nrefs && urC == 0
            then writer ((anno, urC) :< TLamF (Closed name) nx, nrefs)
            else writer ((anno, urC) :< TLamF (Open name) nx, nrefs)
          f (Left s)           = lift $ Left s
        LetUPF bindings inner -> case runWriterT inner of
          Left s -> lift $ Left s
          Right (nInner, refs) -> WriterT $ do
            -- Build dependency graph
            nBindings <- traverse makeBindingsAsoc bindings
            let originalOrder = letBindingName <$> bindings
                dependencies = Map.fromList $ fmap (second snd) nBindings
                sortedBindings :: Either ResolverError [(String, Cofree (ParserTermF String String) (LocTag, Int))]
                sortedBindings =
                  case topologicalSort originalOrder dependencies of
                    Left cycle -> Left cycle
                    Right sortedNames ->
                      pure [(name, def) | name <- sortedNames, (name', (def, _)) <- nBindings, name == name']
                makeBinding (n,d@((_, c) :< _)) inner@(a :< _) = a :< TAppF (a :< TLamF (LetBinding c n) inner) d
            sortedBindings >>= \sb -> let trans = getTransitive' dependencies refs
                                          sb' = [(n,t) | (n,t) <- sb,  n `elem` trans]
                                          fst' (x,_,_) = x
                                          newRefs = Set.difference trans (Set.fromList $ fmap fst sb')
                                      in pure (foldr makeBinding nInner $ reverse sb', newRefs)
        x -> WriterT . fmap (first (((anno, urC) :<) . brt)) . runWriterT $ sequence x where
          brt = \case
            ITEUPF i t e -> TITEF i t e
            IntUPF n -> unwrap $ i2t (anno, urC) n
            StringUPF s -> unwrap $ s2t (anno, urC) s
            PairUPF a b -> ParserTermB $ PairSF a b
            ListUPF l -> unwrap $ foldr (\x y -> (anno, urC) :< ParserTermB (PairSF x y)) ((anno, urC) :< ParserTermB ZeroSF) l
            AppUPF f x -> TAppF f x
            UnsizedRecursionUPF t r b -> TLimitedRecursionF t r b
            ChurchUPF n -> TChurchF n
            LeftUPF x -> TLeftF x
            RightUPF x -> TRightF x
            TraceUPF x -> TTraceF x
            CheckUPF cf x -> TCheckF cf x
            HashUPF x -> THashF x
      cleanup = \case
        Left s -> Left s
        Right (x, refs) -> forgetURCount <$> addRepeaters refs x
      -- HACK extended from annotateUnsizedCount
      addRepeaters refs = if null refs
        then pure
        else \case
        a :< TAppF x (_ :< TVarF v) -> case Set.partition (== v) refs of
          (found, rest) | length found == 1 -> (\c i -> a :< TAppF c i) <$> addRepeaters rest x <*> pure (a :< TUnsizedRepeaterF)
          _ -> Left . MissingDefinitions $ Set.toList refs
        _ -> Left . MissingDefinitions $ Set.toList refs

      forgetURCount :: Cofree (ParserTermF String String) (LocTag, Int) -> Term1
      forgetURCount = cata f where
        f ((a,c) C.:< x) = a :< x
  in cleanup . runWriterT . cata buildRefs $ annotateUnsizedCount term

optimizeBuiltinFunctions :: AUPT -> AUPT
optimizeBuiltinFunctions = transform optimize where
  optimize = \case
    twoApp@(anno0 :< AppUPF (_ :< AppUPF (_ :< f) x) y) ->
      case f of
        VarUPF "pair" -> anno0 :< PairUPF x y
        VarUPF "app"  -> anno0 :< AppUPF x y
        _             -> twoApp
    oneApp@(anno0 :< AppUPF (anno1 :< f) x) ->
      case f of
        VarUPF "left"  -> anno0 :< LeftUPF x
        VarUPF "right" -> anno0 :< RightUPF x
        VarUPF "trace" -> anno0 :< TraceUPF x
        VarUPF "pair"  -> anno0 :< LamUPF (locatedName anno0 "y") (anno1 :< PairUPF x (anno1 :< VarUPF "y"))
        VarUPF "app"   -> anno0 :< LamUPF (locatedName anno0 "y") (anno1 :< AppUPF x (anno1 :< VarUPF "y"))
        _             -> oneApp
        -- VarUP "check" TODO
    x -> x

-- |Process an `Term2` to have all `HashUP` replaced by a unique number.
-- The unique number is constructed by doing a SHA1 hash of the Term2 and
-- adding one for all consecutive HashUP's.
generateAllHashes :: Term2 -> Term2
generateAllHashes x@(anno :< _) = transform interm x where
  hash' :: ByteString -> Digest SHA256
  hash' = hash
  term2Hash :: Term2 -> ByteString
  term2Hash = BS.pack . BA.unpack . hash' . BS.pack . encode . show . (forget :: Cofree (ParserTermF () Int) LocTag -> Fix (ParserTermF () Int))
  bs2Term2 :: ByteString -> Term2
  bs2Term2 bs = ints2t anno . drop 24 $ fromInteger . toInteger <$> BS.unpack bs
  interm :: Term2 -> Term2
  interm = \case
    (anno :< THashF term1) -> bs2Term2 . term2Hash $ term1
    x                      -> x

addBuiltins :: AUPT -> AUPT
addBuiltins aupt = GeneratedLoc "addBuiltins" Nothing :< LetUPF
  [ bind "zero" (builtin "zero" :< IntUPF 0)
  , bind "left" (builtin "left" :< LamUPF (locatedName (builtin "left") "x") (builtin "left" :< LeftUPF (builtin "left" :< VarUPF "x")))
  , bind "right" (builtin "right" :< LamUPF (locatedName (builtin "right") "x") (builtin "right" :< RightUPF (builtin "right" :< VarUPF "x")))
  , bind "trace" (builtin "trace" :< LamUPF (locatedName (builtin "trace") "x") (builtin "trace" :< TraceUPF (builtin "trace" :< VarUPF "x")))
  , bind "pair" (builtin "pair" :< LamUPF (locatedName (builtin "pair") "x") (builtin "pair" :< LamUPF (locatedName (builtin "pair") "y") (builtin "pair" :< PairUPF (builtin "pair" :< VarUPF "x") (builtin "pair" :< VarUPF "y"))))
  , bind "app" (builtin "app" :< LamUPF (locatedName (builtin "app") "x") (builtin "app" :< LamUPF (locatedName (builtin "app") "y") (builtin "app" :< AppUPF (builtin "app" :< VarUPF "x") (builtin "app" :< VarUPF "y"))))
  ]
  aupt
  where
    builtin = BuiltinLoc
    bind name value = (locatedName (builtin name) name, value)

-- |Process an `AnnotatedUPT` to a `Term3` with failing capability.
process :: AnnotatedUPT
        -> Either ResolverError Term3
process upt = (\dt -> debugTrace ("Resolver process term:\n" <> prettyPrint dt) dt) . splitExpr <$> process2Term2 upt

processWlet :: AnnotatedUPT -> Either ResolverError Term3
processWlet = fmap (splitExpr . (\dt -> debugTrace ("Resolver processWlet before split:\n" <> pt dt) dt)) . process2Term2let where
  pt x = prettyPrint $ fg x
  fg :: Term2 -> Fix (ParserTermF () Int)
  fg = forget

process2Term2 :: AnnotatedUPT
              -> Either ResolverError Term2
process2Term2 = fmap generateAllHashes
              . debruijinize [] <=< (fmap tf . validateVariables)
              . AnnotatedUPT
              . removeCaseUPs
              . optimizeBuiltinFunctions
              . addBuiltins
              . unAnnotatedUPT
                 where tf x = debugTrace ("reg Term1:\n" <> prettyPrint x) x

process2Term2let :: AnnotatedUPT -> Either ResolverError Term2
process2Term2let = fmap generateAllHashes
                 . debruijinizeApp <=< fmap tf . letsToApps
                 . AnnotatedUPT
                 . removeCaseUPs
                 . optimizeBuiltinFunctions
                 . addBuiltins
                 . unAnnotatedUPT
                 where tf x = debugTrace ("wLet Term1:\n" <> prettyPrint x) x

-- |Helper function to compile to Term2
runTelomareParser2Term2 :: TelomareParser AnnotatedUPT -- ^Parser to run
                        -> String                      -- ^Raw string to be parsed
                        -> Either ResolverError Term2         -- ^Error on Left
runTelomareParser2Term2 parser str =
  first (ParseError . errorBundlePretty) (runParser parser "" str) >>= process2Term2

resolveImports' :: [(String, [Either AUPT (String, AUPT)])]
                -> [Either AUPT (String, AUPT)] -- ^Main module with both Import and Assignment
                -> [Either AUPT (String, AUPT)]
resolveImports' modules xs = lefts <> rights
  where
    lefts' = reverse . filter isLeft $ xs
    lefts = case lefts' of
      [] -> lefts'
      (y:ys) -> case y of
        (Left (_ :< (ImportUPF var))) ->
          case lookup var modules of
            Nothing -> error $ "Import error from " <> var -- TODO make return Either and get rid of this
            Just x  -> x
        (Left (_ :< (ImportQualifiedUPF q v))) ->
          case lookup v modules of
            Nothing -> error $ "Import error from " <> v -- TODO make return Either and get rid of this
            Just x  -> (fmap . fmap . first) (\str -> q <> "." <> str) x
        e -> error $ "Expected import statement. Got:\n" <> show e
    rights = filter isRight xs
    isLeft (Left _) = True
    isLeft _        = False
    isRight (Right _) = True
    isRight _         = False

resolveAllImports' :: [(String, [Either AUPT (String, AUPT)])]
                   -> [Either AUPT (String, AUPT)]
                   -> [Either AUPT (String, AUPT)]
resolveAllImports' modules x =
  let resolved = resolveImports' modules x
  in if resolved == x
     then resolved
     else resolveAllImports' modules resolved

resolveAllImports :: [(String, [Either AUPT (String, AUPT)])] -- ^All the modules
                  -> [Either AUPT (String, AUPT)] -- ^Module to be resolved (i.e. list of either Import_UPT or top level definitions)
                  -> [(String, AUPT)]
resolveAllImports x y = removeRights <$> resolveAllImports' x y
  where
    removeRights = \case
      Left x -> error $ "resolveImports: Left when should be all Right: " <> show x -- TODO make return Either and get rid of this
      Right x -> x

resolveImports :: [(String, [Either AUPT (String, AUPT)])]
               -> String
               -> [(String, AUPT)]
resolveImports modules moduleName = resolveAllImports modules principal
  where
    principal = case lookup moduleName modules of
      Nothing -> error $ "resolveImports: Module " <> moduleName <> " not found" -- TODO make return Either and get rid of this
      Just x  -> x

resolveMain :: [(String, [Either AUPT (String, AUPT)])] -- ^Modules: [(ModuleName, [Either Import (VariableName, BindedUPT)])]
            -> String -- ^Module name with main
            -> Either ResolverError AUPT
resolveMain allModules mainModule = case lookup mainModule allModules of
  Nothing -> Left $ ModuleNotFound mainModule
  Just lst -> let resolved :: [(String, AUPT)]
                  resolved = resolveImports allModules mainModule
                  maybeMain = lookup "main" resolved
              in case maybeMain of
                   Nothing -> Left $ NoMainFunction mainModule
                   Just x ->
                     let loc = case x of loc' :< _ -> loc'
                         locatedBindings = first (locatedName (GeneratedLoc "resolveMain.binding" (Just loc))) <$> pruneBindings x resolved
                     in Right $ GeneratedLoc "resolveMain" (Just loc) :< LetUPF locatedBindings x

main2Term3 :: [(String, [Either AUPT (String, AUPT)])] -- ^Modules: [(ModuleName, [Either Import (VariableName, BindedUPT)])]
           -> String -- ^Module name with main
           -> Either ResolverError Term3 -- ^Error on Left
main2Term3 moduleBindings s = resolveMain moduleBindings s >>= process . AnnotatedUPT

main2Term3let :: [(String, [Either AUPT (String, AUPT)])] -- ^Modules: [(ModuleName, [Either Import (VariableName, BindedUPT)])]
           -> String -- ^Module name with main
           -> Either ResolverError Term3 -- ^Error on Left
main2Term3let moduleBindings s = resolveMain moduleBindings s >>= processWlet . AnnotatedUPT
