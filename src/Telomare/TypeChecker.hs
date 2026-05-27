{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternSynonyms #-}

module Telomare.TypeChecker where

import Control.Applicative
import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Lens.Plated (transform)
import Control.Monad.Except
import Control.Monad.State (State)
import qualified Control.Monad.State as State
import Data.Bifunctor (second)
import qualified Data.DList as DList
import Data.Foldable (fold)
import Data.Functor.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Semigroup (Max (..))
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace
import PrettyPrint
import Telomare (AbortableF (..), FunctionIndex (FunctionIndex), LocTag (..),
                 PartExprF (..), PartialType (..), StuckF (..), Term3,
                 Term3F (..), TypeCheckError (..), pattern AbortFW,
                 pattern BasicFW, pattern PairB, pattern StuckFW, pattern ZeroB)

debug :: Bool
debug = False

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

newtype DebugTypeMap = DebugTypeMap (Map Int PartialType)

instance Show DebugTypeMap where
  show (DebugTypeMap x) = ("typeMap:\n" ++) .
    concatMap ((++ "\n") . show . second PrettyPartialType) $ Map.toAscList x

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

initState :: Term3 -> (PartialType, Set TypeAssociation, Int)
initState t = (TypeVariable (GeneratedLoc "TypeChecking initial var" Nothing) 0, Set.empty, 0)

annotate :: Term3 -> AnnotateState PartialType
annotate term =
  let annotate' :: Term3 -> AnnotateState PartialType
      annotate' = \case
        anno :< g -> case g of
          BasicFW ZeroSF -> pure ZeroTypeP
          BasicFW (PairSF a b) -> PairTypeP <$> annotate' a <*> annotate' b
          BasicFW EnvSF -> State.gets (\(t, _, _) -> t)
          BasicFW (SetEnvSF x) -> do
            xt <- annotate' x
            (it, (ot, _)) <- withNewEnv anno . withNewEnv anno $ pure ()
            associateVar (debugTrace ("setenv result " <> show xt <> " -- and out type " <> show ot) $ PairTypeP (ArrTypeP it ot) it) xt
            pure ot
          StuckFW (DeferSF fi x) -> withNewEnv anno (annotate' x)
                                       >>= \(it, ot) -> pure $ ArrTypeP it ot
          AbortFW AbortF -> do
            (it, _) <- withNewEnv anno $ pure ()
            pure (ArrTypeP ZeroTypeP (ArrTypeP it it))
          BasicFW (GateSF l r) -> do
            lt <- annotate' l
            rt <- annotate' r
            associateVar lt rt
            pure $ ArrTypeP ZeroTypeP lt
          BasicFW (LeftSF x) -> do
            xt <- annotate' x
            (la, _) <- withNewEnv anno $ pure ()
            associateVar (PairTypeP la AnyType) xt
            pure la
          BasicFW (RightSF x) -> do
            xt <- annotate' x
            (ra, _) <- withNewEnv anno $ pure ()
            associateVar (PairTypeP AnyType ra) xt
            pure ra
          Term3CheckingWrapper _ _ c -> annotate' c
          Term3Unsized _ -> State.gets (\(t, _, _) -> t)
  in annotate' term

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
typeCheck t tm = convert (partiallyAnnotate tm >>= associate) where
  associate (ty, resolver) = debugTrace ("typechecking term:\n" <> prettyPrint tm <> "\nCOMPARING TYPES " <> show (t, fullyResolve resolver ty))
     $ makeAssociations (fullyResolve resolver ty) t
  convert = \case
    Left er -> Just er
    _       -> Nothing
