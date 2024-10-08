{-# LANGUAGE LambdaCase #-}

module Telomare.TypeChecker where

import Control.Applicative
import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Lens.Plated (transform)
import Control.Monad.Except
import Control.Monad.State (State)
import qualified Control.Monad.State as State
import Data.Bifunctor (second)
import qualified Data.DList as DList
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace
import PrettyPrint
import Telomare (FragExpr (..), FragExprF (..), FragExprUR (..), FragIndex (..),
                 LocTag (..), PartialType (..), RecursionSimulationPieces (..),
                 Term3 (..), rootFrag)

debug :: Bool
debug = False

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

newtype DebugTypeMap = DebugTypeMap (Map Int PartialType)

instance Show DebugTypeMap where
  show (DebugTypeMap x) = ("typeMap:\n" ++) .
    concatMap ((++ "\n") . show . second PrettyPartialType) $ Map.toAscList x

data TypeCheckError
  = UnboundType Int
  | InconsistentTypes PartialType PartialType
  | RecursiveType Int
  deriving (Eq, Ord, Show)

-- State is closure environment, set of associations between type variables and types, unresolved type id supply
type AnnotateState = ExceptT TypeCheckError (State (PartialType, Set TypeAssociation, Int))

withNewEnv :: LocTag -> AnnotateState a -> AnnotateState (PartialType, a)
withNewEnv anno action = do
  (env, typeMap, v) <- State.get
  State.put (TypeVariable anno v, typeMap, v + 1)
  result <- action
  State.modify $ \(_, typeMap, v) -> (env, typeMap, v)
  pure (TypeVariable anno v, result)

setEnv :: PartialType -> AnnotateState ()
setEnv env = State.modify $ \(_, typeMap, v) -> (env, typeMap, v)

data TypeAssociation = TypeAssociation Int PartialType
  deriving (Eq, Ord, Show)

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

buildTypeMap :: Set TypeAssociation -> Either TypeCheckError (Map Int PartialType)
buildTypeMap assocSet =
  let multiMap = Map.fromListWith DList.append . fmap (\(TypeAssociation i t) -> (i, DList.singleton t))
        $ Set.toList assocSet
      getKeys = \case
        TypeVariable _ i -> DList.singleton i
        ArrTypeP a b     -> getKeys a <> getKeys b
        PairTypeP a b    -> getKeys a <> getKeys b
        _                -> mempty
      isRecursiveType resolvedSet k = case (Set.member k resolvedSet, Map.lookup k multiMap) of
        (True, _) -> Just k
        (_, Nothing) -> Nothing
        (_, Just t) -> foldr (\nk r -> isRecursiveType (Set.insert k resolvedSet) nk <|> r) Nothing
          $ foldMap getKeys t
      debugShowMap tm = debugTrace (concatMap (\(k, v) -> show k <> ": " <> show v <> "\n") $ Map.toAscList tm)
      buildMap assoc typeMap = case Set.minView assoc of
        Nothing -> debugShowMap typeMap $ pure typeMap
        Just (TypeAssociation i t, newAssoc) -> case Map.lookup i typeMap of
          Nothing -> buildMap newAssoc $ Map.insert i t typeMap
          Just t2 -> makeAssociations t t2 >>= (\assoc2 -> buildMap (newAssoc <> assoc2) typeMap)
  -- if any variables result in lookup cycles, fail with RecursiveType
  in case foldr (\t r -> isRecursiveType Set.empty t <|> r) Nothing (Map.keys multiMap) of
    Just k  -> Left $ RecursiveType k
    Nothing -> debugTrace (show multiMap) $ buildMap assocSet mempty

fullyResolve :: (Int -> Maybe PartialType) -> PartialType -> PartialType
fullyResolve resolve = convert where
    convert = transform endo
    endo = \case
      TypeVariable anno i -> case resolve i of
        Nothing -> TypeVariable anno i
        Just t  -> convert t -- debugTrace (show t) $ convert t
      x -> x

traceAssociate :: PartialType -> PartialType -> a -> a
traceAssociate a b = if debug
  then trace (concat ["associateVar ", show a, " -- ", show b])
  else id

associateVar :: PartialType -> PartialType -> AnnotateState ()
associateVar a b = liftEither (makeAssociations a b) >>= \set -> State.modify (changeState set) where
  changeState set (curVar, oldSet, v) = (curVar, oldSet <> set, v)

{-
-- convert a PartialType to a full type, aborting on circular references
fullyResolve :: Map Int PartialType -> PartialType -> Maybe DataType
fullyResolve typeMap x = case mostlyResolved of
  Left _ -> Nothing
  Right mr -> filterTypeVars mr
  where
    filterTypeVars ZeroTypeP = pure ZeroType
    filterTypeVars (TypeVariable _) = Nothing
    filterTypeVars (ArrTypeP a b) = ArrType <$> filterTypeVars a <*> filterTypeVars b
    filterTypeVars (PairTypeP a b) = PairType <$> filterTypeVars a <*> filterTypeVars b
    mostlyResolved = mostlyResolve typeMap x
-}

{--
 - reserve 0 -> n*2 TypeVariables for types of FragExprs
 -}
initState :: Term3 -> (PartialType, Set TypeAssociation, Int)
initState (Term3 termMap) =
  let startVariable = case Set.maxView (Map.keysSet termMap) of
        Nothing               -> 0
        Just (FragIndex i, _) -> (i + 1) * 2
  in (TypeVariable DummyLoc 0, Set.empty, startVariable)

getFragType :: LocTag -> FragIndex -> PartialType
getFragType anno (FragIndex i) = ArrTypeP (TypeVariable anno $ i * 2) (TypeVariable anno $ i * 2 + 1)

annotate :: Term3 -> AnnotateState PartialType
annotate (Term3 termMap) =
  let annotate' :: Cofree (FragExprF (RecursionSimulationPieces FragExprUR)) LocTag -> AnnotateState PartialType
      annotate' = \case
        anno :< ZeroFragF -> pure ZeroTypeP
        anno :< PairFragF a b -> PairTypeP <$> annotate' a <*> annotate' b
        anno :< EnvFragF -> (State.gets (\(t, _, _) -> t))
        anno :< SetEnvFragF x -> do
          xt <- annotate' x
          (it, (ot, _)) <- withNewEnv anno . withNewEnv anno $ pure ()
          associateVar (PairTypeP (ArrTypeP it ot) it) xt
          pure ot
        anno :< DeferFragF ind -> pure $ getFragType anno ind
        anno :< AbortFragF -> do
          (it, _) <- withNewEnv anno $ pure ()
          pure (ArrTypeP ZeroTypeP (ArrTypeP it it))
        anno :< GateFragF l r -> do
          lt <- annotate' l
          rt <- annotate' r
          associateVar lt rt
          pure $ ArrTypeP ZeroTypeP lt
        anno :< LeftFragF x -> do
          xt <- annotate' x
          (la, _) <- withNewEnv anno $ pure ()
          associateVar (PairTypeP la AnyType) xt
          pure la
        anno :< RightFragF x -> do
          xt <- annotate' x
          (ra, _) <- withNewEnv anno $ pure ()
          associateVar (PairTypeP AnyType ra) xt
          pure ra
        anno :< TraceFragF -> (State.gets (\(t, _, _) -> t))
        anno :< AuxFragF (NestedSetEnvs _) -> (State.gets (\(t, _, _) -> t))
        anno :< AuxFragF (SizingWrapper _ (FragExprUR x)) -> annotate' x
      initInputType :: LocTag -> FragIndex -> AnnotateState ()
      initInputType anno fi = let (ArrTypeP it _) = getFragType anno fi in State.modify (\(_, s, i) -> (it, s, i))
      associateOutType :: LocTag -> FragIndex -> PartialType -> AnnotateState ()
      associateOutType anno fi ot = let (ArrTypeP _ ot2) = getFragType anno fi in associateVar ot ot2
      rootType anno = initInputType anno (FragIndex 0) >> annotate' (unFragExprUR $ rootFrag termMap)
  in sequence_ (Map.mapWithKey (\k v -> initInputType DummyLoc k >> annotate' (unFragExprUR v) >>= associateOutType DummyLoc k) termMap) >> rootType DummyLoc

partiallyAnnotate :: Term3 -> Either TypeCheckError (PartialType, Int -> Maybe PartialType)
partiallyAnnotate term =
  let runner :: State (PartialType, Set TypeAssociation, Int) (Either TypeCheckError PartialType)
      runner = runExceptT $ annotate term
      (rt, (_, s, _)) = State.runState runner (initState term)
  in (,) <$> rt <*> (flip Map.lookup <$> buildTypeMap s)

inferType :: Term3 -> Either TypeCheckError PartialType
inferType tm = lookupFully <$> partiallyAnnotate tm where
  lookupFully (ty, resolver) = fullyResolve resolver ty

typeCheck :: PartialType -> Term3 -> Maybe TypeCheckError
typeCheck t tm@(Term3 typeMap) = convert (partiallyAnnotate tm >>= associate) where
  associate (ty, resolver) = debugTrace ("COMPARING TYPES " <> show (t, fullyResolve resolver ty) <> "\n" <> debugMap ty resolver)
    . traceAgain $ makeAssociations (fullyResolve resolver ty) t
  debugMap ty resolver = showTypeDebugInfo (TypeDebugInfo tm (fullyResolve resolver . getFragType DummyLoc)
                                            (fullyResolve resolver ty))
  traceAgain s = debugTrace ("Resulting thing " <> show s) s
  convert = \case
    Left er -> Just er
    _       -> Nothing
