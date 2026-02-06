{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Telomare.Possible where

import Control.Applicative
import Control.Comonad.Cofree (Cofree ((:<)), hoistCofree)
import qualified Control.Comonad.Trans.Cofree as CofreeT (CofreeF (..))
import Control.Lens.Plated (transform)
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader (Reader, ReaderT, ask, local, runReaderT)
import qualified Control.Monad.Reader as Reader
import Control.Monad.State.Strict (State, StateT)
import qualified Control.Monad.State.Strict as State
import qualified Control.Monad.State.Lazy as StateL
import Control.Monad.Trans.Class
import Data.Bifunctor
import Data.Char (chr)
import Data.DList (DList)
import qualified Data.DList as DList
import Data.Fix (Fix (..), hoistFix')
import Data.Foldable
import Data.Functor.Classes
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import Data.Kind
import Data.List (nub, nubBy, partition, sortBy)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Monoid
-- import Data.SBV ((.<), (.>))
-- import qualified Data.SBV as SBV
-- import qualified Data.SBV.Control as SBVC
import Control.Comonad.Trans.Cofree (CofreeF, headF)
import Control.Monad.Reader.Class
import Data.GenValidity
import Data.GenValidity.Map
import Data.Semigroup (Max (..))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Validity (Validity (..), declare, trivialValidation)
import Data.Void
import Debug
import Debug.Trace
import GHC.Generics (Generic)
import PrettyPrint
import Telomare (AbstractRunTime (..), BreakState' (..), FragExpr (..),
                 FragExprF (..), FragExprUR (..), FragIndex, IExpr (..),
                 IExprF (SetEnvF), LocTag (DummyLoc), PartialType (..),
                 RecursionPieceFrag, RecursionSimulationPieces (..),
                 RunTimeError (..), TelomareLike (fromTelomare, toTelomare),
                 Term3 (..), Term4 (..),
                 UnsizedRecursionToken (UnsizedRecursionToken), buildFragMap,
                 convertAbortMessage, deferF, env, forget, g2i, i2g,
                 indentWithChildren', indentWithOneChild, indentWithOneChild',
                 indentWithTwoChildren, indentWithTwoChildren',
                 pattern AbortAny, pattern AbortRecursion,
                 pattern AbortUnsizeable, pattern AbortUser, rootFrag, s2g,
                 sindent, toPartialType)
import Telomare.PossibleData
import Test.QuickCheck (Arbitrary (..), Gen, oneof)
import Test.QuickCheck.Gen (sized)
-- import           Telomare.TypeChecker
-- import Data.SBV.RegExp (everything)
import Telomare.RunTime (hvmEval)

debug :: Bool
debug = False

debugTrace :: String -> a -> a
-- debugTrace s x = if debug then debugTrace' s x else x
debugTrace s x = if debug then trace s x else x

{-
testSBV :: SBV.Symbolic SBV.Word8
testSBV = do
  b <- SBV.sBool "b"
  a <- SBV.sWord8 "a"
  SBV.constrain $ a + 5 .< 10
  SBV.constrain $ a .> 2
  SBV.constrain b
  SBVC.query $ SBVC.checkSat >>= \case
      SBVC.Unk   -> undefined -- error "Solver returned unknown!"
      SBVC.Unsat -> undefined -- error "Solver couldn't solve constraints"
      SBVC.Sat   -> SBVC.getValue a
-}

-- testSBV' :: IO Int
-- testSBV' = fromIntegral <$> SBV.runSMT testSBV

anaM' :: (Monad m, Corecursive t, x ~ Base t, Traversable x) => (a -> m (Base t a)) -> a -> m t
anaM' f = c where c = (fmap embed . mapM c) <=< f

basicStep :: (Base g ~ f, BasicBase f, Corecursive g, Recursive g) => (f g -> g) -> f g -> g
basicStep handleOther = \case
  BasicFW (LeftSF z@(BasicEE ZeroSF))      -> z
  BasicFW (LeftSF (BasicEE (PairSF l _)))  -> l
  BasicFW (RightSF z@(BasicEE ZeroSF))     -> z
  BasicFW (RightSF (BasicEE (PairSF _ r))) -> r
  GateSwitch l _ (BasicEE ZeroSF)          -> l
  GateSwitch _ r (BasicEE (PairSF _ _))    -> r
  -- stuck values
  x@(BasicFW ZeroSF)                       -> embed x
  x@(BasicFW (PairSF _ _))                 -> embed x
  x@(BasicFW (GateSF _ _))                 -> embed x
  x                                        -> handleOther x

basicStepM :: (Base g ~ f, BasicBase f, Traversable f, Corecursive g, Recursive g, PrettyPrintable g, Monad m) => (f g -> m g) -> f g -> m g
basicStepM handleOther x = f x where
  f = \case
    BasicFW (LeftSF z@(BasicEE ZeroSF))      -> pure z
    BasicFW (LeftSF (BasicEE (PairSF l _)))  -> pure l
    BasicFW (RightSF z@(BasicEE ZeroSF))     -> pure z
    BasicFW (RightSF (BasicEE (PairSF _ r))) -> pure r
    GateSwitch l _ (BasicEE ZeroSF)          -> pure l
    GateSwitch _ r (BasicEE (PairSF _ _))    -> pure r
    -- stuck values
    x@(BasicFW ZeroSF)                       -> pure $ embed x
    x@(BasicFW (PairSF _ _))                 -> pure $ embed x
    x@(BasicFW (GateSF _ _))                 -> pure $ embed x

    _                                        -> handleOther x

transformNoDefer :: (Base g ~ f, StuckBase f, Recursive g) => (f g -> g) -> g -> g
transformNoDefer f = c where
  c = f . c' . project
  c' = \case
    s@(StuckFW (DeferSF _ _)) -> s
    x                         -> fmap c x

transformNoDeferM :: (Base g ~ f, StuckBase f, Traversable f, Monad m, Recursive g) => (f g -> m g) -> g -> m g
transformNoDeferM f = c where
  c = f <=< (c' . project)
  c' = \case
    s@(StuckFW (DeferSF _ _)) -> pure s
    x                         -> mapM c x

stuckStep :: (Base a ~ f, StuckBase f, BasicBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
stuckStep handleOther = \case
  ff@(FillFunction (StuckEE (DeferSF fid d)) e) -> db $ transformNoDefer (basicStep (stuckStep handleOther) . replaceEnv) d where
    e' = project e
    db = if False -- fid == toEnum 74
      then debugTrace ("stuckstep dumping output:\n" <> prettyPrint (embed ff))
      -- then debugTrace ("function " <> show fid)
      else id
    replaceEnv = \case
      BasicFW EnvSF -> e'
      x             -> x
  -- stuck value
  x@(StuckFW _) -> embed x
  x -> handleOther x

stuckStepDebug :: (Base a ~ f, StuckBase f, BasicBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
stuckStepDebug handleOther = \case
  ff@(FillFunction (StuckEE (DeferSF fid d)) e) -> db $ transformNoDefer (basicStep (stuckStepDebug handleOther) . replaceEnv) d' where
    interestingIds = []
    e' = project e
    db = if False -- fid == toEnum 74
      then debugTrace ("stuckstep dumping output:\n" <> prettyPrint (embed ff))
      -- then debugTrace ("function " <> show fid)
      else id
    d' = if fromEnum fid `elem` interestingIds -- if fid == toEnum unsizedStepMw -- unsizedStepMrfa
      -- then debugTrace ("stuckStep dumping environment\n" <> prettyPrint e) d
      then debugTrace ("stuckStep dumping environment for " <> show fid <> "\n"  <> prettyPrint e) d
      else debugTrace ("stuckStep hit " <> show (fromEnum fid)) d
    replaceEnv = \case
      BasicFW EnvSF -> e'
      x             -> x
  -- stuck value
  x@(StuckFW _) -> embed x
  x -> handleOther x

stuckStepM :: (Base a ~ f, Traversable f, StuckBase f, BasicBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (f a -> m a) -> f a -> m a
stuckStepM handleOther x = f x where
  f = \case
    FillFunction (StuckEE (DeferSF fid d)) e -> transformNoDeferM runStuck d where
      runStuck = basicStepM (stuckStepM handleOther) . replaceEnv
      e' = project e
      replaceEnv = \case
        BasicFW EnvSF -> e'
        x             -> x
    -- stuck value
    x@(StuckFW _) -> pure $ embed x
    _ -> handleOther x

stuckStepDebugM :: forall a f m j. (Base a ~ f, Traversable f, StuckBase f, BasicBase f, AbortBase f, UnsizedBase f, IndexedInputBase f, SuperBase f
                   , ShallowEq1 f, Show a, Eq a, Recursive a, Corecursive a, PrettyPrintable a, GenValidAdj a, Monad m
                   , Gennable a ~ j, GenValid j, Eq j)
  => (f a -> m a) -> f a -> m a
stuckStepDebugM handleOther x = f x where
  interestingIds = []
  f = \case
    ff@(FillFunction (StuckEE (DeferSF fid d)) e) -> db $ transformNoDeferM runStuck d' where
      runStuck = basicStepM (stuckStepDebugM handleOther) . replaceEnv
      e' = project e
      d' = if fromEnum fid `elem` interestingIds -- if fid == toEnum unsizedStepMw -- unsizedStepMrfa
        then debugTrace ("stuckStepDebugM dumping environment for " <> show fid <> "\n"  <> prettyPrint e) d
        else debugTrace ("stuckStepDebugM hit " <> show (fromEnum fid)) d
      db = id
      replaceEnv = \case
        BasicFW EnvSF -> e'
        x             -> x
    -- stuck value
    x@(StuckFW _) -> pure $ embed x
    _ -> handleOther x

stuckStepWithTrace :: (Base a ~ f, MonadReader s m, s ~ TCallStack a, Traversable f, StuckBase f, BasicBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> m a) -> f a -> m a
stuckStepWithTrace handleOther = \case
  FillFunction (StuckEE (DeferSF fid d)) e -> local addTrace $ transformNoDeferM runStuck d where
    addTrace = ((fid, e) :)
    runStuck = basicStepM (stuckStepM handleOther) . replaceEnv
    e' = project e
    replaceEnv = \case
      BasicFW EnvSF -> e'
      x             -> x
  -- stuck value
  x@(StuckFW _) -> pure $ embed x
  x -> handleOther x

failAndPrintStack :: (Base a ~ f, MonadReader s m, s ~ TCallStack a, Corecursive a, PrettyPrintable a)
  => f a -> m b
failAndPrintStack x = do
  s <- ask
  error ("could not evaluate\n" <> prettyPrint (embed x) <> concatMap printCall s) where
    printCall (fi, i) = "\n--> from " <> show fi <> " with argument\n" <> prettyPrint i

gateBasicResult :: (Base g ~ f, BasicBase f, Recursive g, Corecursive g) => (g -> GateResult g) -> g -> GateResult g
gateBasicResult handleOther = \case
  BasicEE ZeroSF -> GateResult True False Nothing
  BasicEE (PairSF _ _) -> GateResult False True Nothing
  x -> handleOther x

gateSuperResult :: (Base g ~ f, SuperBase f, Recursive g, Corecursive g) => (g -> GateResult g) -> (g -> GateResult g) -> g -> GateResult g
gateSuperResult step handleOther = \case
  SuperEE (EitherPF n a b) -> let GateResult la ra ba = step a
                                  GateResult lb rb bb = step b
                                  co = case (ba, bb) of
                                    (Just ba', Just bb') -> pure . superEE $ EitherPF n ba' bb'
                                    _ -> ba <|> bb
                              in GateResult (la || lb) (ra || rb) co
  x -> handleOther x

gateAbortResult :: (Base g ~ f, AbortBase f, Recursive g, Corecursive g) => (g -> GateResult g) -> g -> GateResult g
gateAbortResult handleOther = \case
  a@(AbortEE (AbortedF _)) -> GateResult False False $ Just a
  x -> handleOther x

gateIndexedResult :: (Base g ~ f, IndexedInputBase f, Recursive g, Corecursive g) => (g -> GateResult g) -> g -> GateResult g
gateIndexedResult handleOther = \case
  -- IndexedEE (IVarF n) -> GateResult True False Nothing -- wait, why lb but no rb?
  IndexedEE (IVarF n) -> GateResult True True Nothing
  x -> handleOther x

mergeShallow :: (Base g ~ f, SuperBase f, ShallowEq1 f, Recursive g, Corecursive g) => Maybe Integer -> g -> g -> g
mergeShallow n a b = if shallowEq1 (project a) (project b)
  then a
  else superEE $ EitherPF n a b

foldGateResult :: forall g f. (Base g ~ f, SuperBase f, Recursive g, Corecursive g) => Maybe Integer -> g -> g -> GateResult g -> g
foldGateResult n l r (GateResult doL doR o) =
  let filterLeft = \case
        SuperFW (EitherPF nt a _) | nt == n -> a
        x -> embed x
      filterRight = \case
        SuperFW (EitherPF nt _ b) | nt == n -> b
        x -> embed x
      fl = if null n then l else cata filterLeft l
      fr = if null n then r else cata filterRight r
      branchPart = case (doL, doR) of
        (True, True) -> pure . superEE $ EitherPF n fl fr
        (True, _)    -> pure fl
        (_, True)    -> pure fr
        _            -> Nothing
  in case (o, branchPart) of
    (Just o', Just bp) -> superEE $ EitherPF Nothing o' bp
    (Just x, _)        -> x
    (_, Just x)        -> x
    _                  -> error "foldGateResult: no results"

superStep :: forall a f. (Base a ~ f, BasicBase f, SuperBase f, ShallowEq1 f, Recursive a, Corecursive a, PrettyPrintable a)
  => (a -> GateResult a) -> (f a -> a) -> (f a -> a) -> f a -> a
superStep gateResult step handleOther =
  let filterLeft :: Maybe Integer -> f a -> a
      filterLeft n = \case
        SuperFW (EitherPF nt a _) | nt == n -> a
        x -> embed x
      filterRight :: Maybe Integer -> f a -> a
      filterRight n = \case
        SuperFW (EitherPF nt _ b) | nt == n -> b
        x -> embed x
  in \case
    BasicFW (LeftSF (SuperEE (EitherPF n a b))) -> mergeShallow n (step . embedB . LeftSF $ a) (step . embedB . LeftSF $ b)
    BasicFW (RightSF (SuperEE (EitherPF n a b))) -> mergeShallow n (step . embedB . RightSF $ a) (step . embedB . RightSF $ b)
    BasicFW (SetEnvSF (SuperEE (EitherPF n a b))) -> mergeShallow n (step . embedB . SetEnvSF $ a) (step . embedB . SetEnvSF $ b)
    -- GateSwitch l r x@(SuperEE (EitherPF n _ _)) -> (\dx -> debugTrace ("superStep gateSwitch\n" <> prettyPrint dx) dx) . foldGateResult n l r $ gateResult x
    GateSwitch l r x@(SuperEE (EitherPF n _ _)) -> foldGateResult n l r $ gateResult x
    (FillFunction (SuperEE (EitherPF n sca scb)) e) -> mergeShallow n
      (step . embedB . SetEnvSF . basicEE . PairSF sca $ if null n then e else cata (filterLeft n) e)
      (step . embedB . SetEnvSF . basicEE . PairSF scb $ if null n then e else cata (filterRight n) e)
    -- stuck values
    x@(SuperFW (EitherPF _ _ _)) -> embed x
    x -> handleOther x

superUnsizedStep :: forall a f. (Base a ~ f, Traversable f, BasicBase f, SuperBase f, UnsizedBase f, ShallowEq1 f, Recursive a, Corecursive a, PrettyPrintable a)
  => (a -> GateResult a) -> (f a -> a) -> (f a -> a) -> f a -> a
superUnsizedStep gateResult step handleOther =
  let filterLeft :: Maybe Integer -> f a -> a
      filterLeft n = \case
        SuperFW (EitherPF nt a _) | nt == n -> a
        x -> embed x
      filterRight :: Maybe Integer -> f a -> a
      filterRight n = \case
        SuperFW (EitherPF nt _ b) | nt == n -> b
        x -> embed x
  in \case
    BasicFW (LeftSF (SuperEE (EitherPF n a b))) -> mergeShallow n (step . embedB . LeftSF $ a) (step . embedB . LeftSF $ b)
    BasicFW (RightSF (SuperEE (EitherPF n a b))) -> mergeShallow n (step . embedB . RightSF $ a) (step . embedB . RightSF $ b)
    BasicFW (SetEnvSF (SuperEE (EitherPF n a b))) -> mergeShallow n (step . embedB . SetEnvSF $ a) (step . embedB . SetEnvSF $ b)
    GateSwitch l r x@(SuperEE (EitherPF n _ _)) -> wrapSS $ foldGateResult n l r res where
      wrapSS = if null (unSizedRecursion srx) then id else unsizedEE . SizeStageF srx
      (srx, nx) = extractSizeStages x
      res = gateResult nx
      extractSizeStages = cata $ \case
        UnsizedFW (SizeStageF sr (srb, x)) -> (sr <> srb, x)
        x -> embed <$> sequence x
    (FillFunction (SuperEE (EitherPF n sca scb)) e) -> mergeShallow n
      (step . embedB . SetEnvSF . basicEE . PairSF sca $ if null n then e else cata (filterLeft n) e)
      (step . embedB . SetEnvSF . basicEE . PairSF scb $ if null n then e else cata (filterRight n) e)
    -- stuck values
    x@(SuperFW (EitherPF _ _ _)) -> embed x
    x -> handleOther x

superStepM :: forall a f m. (Base a ~ f, Traversable f, BasicBase f, SuperBase f, ShallowEq1 f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (a -> GateResult a) -> (f a -> m a) -> (f a -> m a) -> f a -> m a
superStepM gateResult step handleOther x = f x where
  pbStep bf = step . embedB . bf
  filterLeft :: Maybe Integer -> f a -> a
  filterLeft n = \case
        SuperFW (EitherPF nt a _) | nt == n -> a
        x -> embed x
  filterRight :: Maybe Integer -> f a -> a
  filterRight n = \case
        SuperFW (EitherPF nt _ b) | nt == n -> b
        x -> embed x
  f = \case
    BasicFW (LeftSF (SuperEE (EitherPF n a b))) -> mergeShallow n <$> pbStep LeftSF a <*> pbStep LeftSF b
    BasicFW (RightSF (SuperEE (EitherPF n a b))) -> mergeShallow n <$> pbStep RightSF a <*> pbStep RightSF b
    BasicFW (SetEnvSF (SuperEE (EitherPF n a b))) -> mergeShallow n <$> pbStep SetEnvSF a <*> pbStep SetEnvSF b
    GateSwitch l r x@(SuperEE (EitherPF n _ _)) -> pure . foldGateResult n l r $ gateResult x
    FillFunction (SuperEE (EitherPF n sca scb)) e -> mergeShallow n
       <$> (pbStep SetEnvSF . basicEE . PairSF sca $ if null n then e else cata (filterLeft n) e)
       <*> (pbStep SetEnvSF . basicEE . PairSF scb $ if null n then e else cata (filterRight n) e)
    -- stuck values
    x@(SuperFW (EitherPF _ _ _)) -> pure $ embed x

    _ -> handleOther x

-- just for debugging
superStepM' :: forall a f m. (Base a ~ f, Traversable f, BasicBase f, SuperBase f, ShallowEq1 f, Recursive a, Corecursive a, PrettyPrintable a, Show a, Monad m)
  => (a -> GateResult a) -> (f a -> m a) -> (f a -> m a) -> f a -> m a
superStepM' gateResult step handleOther x = f x where
  pbStep bf = step . embedB . bf
  filterLeft :: Maybe Integer -> f a -> a
  filterLeft n = \case
        SuperFW (EitherPF nt a _) | nt == n -> a
        x -> embed x
  filterRight :: Maybe Integer -> f a -> a
  filterRight n = \case
        SuperFW (EitherPF nt _ b) | nt == n -> b
        x -> embed x
  -- traceSwitch x = debugTrace ("super switch:\n" <> prettyPrint x <> "\nswitch gateResult: " <> show (gateResult x)) x
  traceSwitch x = x
  -- tsf x = debugTrace ("super switch fold result:\n" <> prettyPrint x) x
  tsf x = x
  -- dtff x y = debugTrace ("superStep fillFunction\n" <> prettyPrint (embed x) <> "\n-- result\n" <> prettyPrint y) y
  dtff x y = y
  {-
  dtfl e x = debugTrace ("superStep ff filter left before\n" <> prettyPrint e <> "\nafter filter\n" <> prettyPrint x) x
  dtfr e x = debugTrace ("superStep ff filter right before\n" <> prettyPrint e <> "\nafter filter\n" <> prettyPrint x) x
-}
  dtfl e = id
  dtfr e = id
  f = \case
    BasicFW (LeftSF (SuperEE (EitherPF n a b))) -> mergeShallow n <$> pbStep LeftSF a <*> pbStep LeftSF b
    BasicFW (RightSF (SuperEE (EitherPF n a b))) -> mergeShallow n <$> pbStep RightSF a <*> pbStep RightSF b
    BasicFW (SetEnvSF (SuperEE (EitherPF n a b))) -> mergeShallow n <$> pbStep SetEnvSF a <*> pbStep SetEnvSF b
    GateSwitch l r x@(SuperEE (EitherPF n _ _)) -> pure . tsf . foldGateResult n l r . gateResult $ traceSwitch x
    ff@(FillFunction (SuperEE (EitherPF n sca scb)) e) -> (\nl nr -> dtff ff $ mergeShallow n nl nr)
       <$> (pbStep SetEnvSF . basicEE . PairSF sca $ if null n then e else dtfl e (cata (filterLeft n) e))
       <*> (pbStep SetEnvSF . basicEE . PairSF scb $ if null n then e else dtfr e (cata (filterRight n) e))
    -- stuck values
    x@(SuperFW (EitherPF _ _ _)) -> pure $ embed x

    _ -> handleOther x

superAbortStep :: (Base g ~ f, Traversable f, BasicBase f, SuperBase f, AbortBase f, ShallowEq1 f, Recursive g, Corecursive g)
  => (f g -> g) -> (f g -> g) -> f g -> g
superAbortStep step handleOther x = f x where
  pbStep bf = step . project . bf
  f = \case
    FillFunction (AbortEE AbortF) (SuperEE (EitherPF n a b)) ->
      mergeShallow n (pbStep (fillFunction (abortEE AbortF)) a) (pbStep (fillFunction (abortEE AbortF)) b)
    _ -> handleOther x

superAbortStepM :: (Base g ~ f, Traversable f, BasicBase f, SuperBase f, AbortBase f, ShallowEq1 f, Recursive g, Corecursive g, Monad m)
  => (f g -> m g) -> (f g -> m g) -> f g -> m g
superAbortStepM step handleOther x = f x where
  pbStep bf = step . project . bf
  f = \case
    FillFunction (AbortEE AbortF) (SuperEE (EitherPF n a b)) ->
      liftM2 (mergeShallow n) (pbStep (fillFunction (abortEE AbortF)) a) (pbStep (fillFunction (abortEE AbortF)) b)
    _ -> handleOther x

indexedAbortStep :: (Base a ~ f, Traversable f, BasicBase f, AbortBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
indexedAbortStep handleOther = \case
  FillFunction (AbortEE AbortF) (IndexedEE (IVarF n)) -> abortEE $ AbortedF AbortAny
  x -> handleOther x

indexedAbortStepM :: (Base a ~ f, Traversable f, BasicBase f, AbortBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (f a -> m a) -> f a -> m a
indexedAbortStepM handleOther = \case
  FillFunction (AbortEE AbortF) (IndexedEE (IVarF n)) -> pure . abortEE $ AbortedF AbortAny
  x -> handleOther x

indexedSuperStep :: (Base a ~ f, Traversable f, BasicBase f, SuperBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
indexedSuperStep handleOther = \case
  GateSwitch l r (IndexedEE (IVarF n)) -> superEE $ EitherPF (pure n) l r
  x -> handleOther x

indexedSuperStepM :: (Base a ~ f, Traversable f, BasicBase f, SuperBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (f a -> m a) -> f a -> m a
indexedSuperStepM handleOther = \case
  GateSwitch l r (IndexedEE (IVarF n)) -> pure . superEE $ EitherPF (pure n) l r

  x -> handleOther x

fuzzyStepM :: (Base a ~ f, Traversable f, BasicBase f, FuzzyBase f, Recursive a, Corecursive a, Show a, PrettyPrintable a, Monad m) => (a -> a -> a)
  -> (f (m a) -> m a) -> (f (m a) -> m a) -> f (m a) -> m a
fuzzyStepM merge step handleOther x = sequence x >>= f where
  liftStep x = step . fmap pure . embedB . x
  f = \case
    BasicFW (LeftSF s@(FuzzyEE SomeInputF)) -> pure s
    BasicFW (LeftSF (FuzzyEE (MaybePairF l _))) -> pure l
    BasicFW (RightSF s@(FuzzyEE SomeInputF)) -> pure s
    BasicFW (RightSF (FuzzyEE (MaybePairF _ r))) -> pure r
    GateSwitch l r (FuzzyEE _) -> pure $ merge l r
    FillFunction (FuzzyEE (FunctionListF l)) e -> do
      rl <- mapM (liftStep SetEnvSF . basicEE . flip PairSF e) l
      case rl of
        (x:xs) -> pure $ foldl' merge x xs
        _      -> error "superStepM fill functionlist, unexpected empty list"
    -- stuck values
    x@(FuzzyFW _) -> pure $ embed x
    _ -> handleOther x

abortStep :: (Base a ~ f, BasicBase f, StuckBase f, AbortBase f, Recursive a, Corecursive a, PrettyPrintable a) => (f a -> a) -> f a -> a
abortStep handleOther =
  \case
    BasicFW (LeftSF a@(AbortEE (AbortedF _))) -> a
    BasicFW (RightSF a@(AbortEE (AbortedF _))) -> a
    BasicFW (SetEnvSF a@(AbortEE (AbortedF _))) -> a
    FillFunction a@(AbortEE (AbortedF _)) _ -> a
    GateSwitch _ _ a@(AbortEE (AbortedF _)) -> a
    FillFunction (AbortEE AbortF) a@(AbortEE (AbortedF _)) -> a
    FillFunction (AbortEE AbortF) (BasicEE ZeroSF) -> deferB abortInd . basicEE $ EnvSF
    FillFunction (AbortEE AbortF) e@(BasicEE (PairSF _ _)) -> (\x -> debugTrace ("aborted with value: " <> prettyPrint x) x) . abortEE $ AbortedF m where
      m = cata truncF e
      truncF = \case
        BasicFW ZeroSF       -> Zero
        BasicFW (PairSF a b) -> Pair a b
        _                    -> Zero -- consider generating a warning?
    -- stuck values
    x@(AbortFW (AbortedF _)) -> embed x
    x@(AbortFW AbortF) -> embed x
    x -> handleOther x

abortStepM :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, AbortBase f, Recursive a, Corecursive a, Monad m)
  => (f a -> m a) -> f a -> m a
abortStepM handleOther x = f x where
  f = \case
    BasicFW (LeftSF a@(AbortEE (AbortedF _))) -> pure a
    BasicFW (RightSF a@(AbortEE (AbortedF _))) -> pure a
    BasicFW (SetEnvSF a@(AbortEE (AbortedF _))) -> pure a
    FillFunction a@(AbortEE (AbortedF _)) _ -> pure a
    GateSwitch _ _ a@(AbortEE (AbortedF _)) -> pure a
    FillFunction (AbortEE AbortF) a@(AbortEE (AbortedF _)) -> pure a
    FillFunction (AbortEE AbortF) (BasicEE ZeroSF) -> pure . deferB abortInd . basicEE $ EnvSF
    FillFunction (AbortEE AbortF) e@(BasicEE (PairSF _ _)) -> pure . abortEE $ AbortedF m where
      m = cata truncF e
      truncF = \case
        BasicFW ZeroSF       -> Zero
        BasicFW (PairSF a b) -> Pair a b
        _                    -> Zero -- consider generating a warning?
    -- stuck values
    x@(AbortFW (AbortedF _)) -> pure $ embed x
    x@(AbortFW AbortF) -> pure $ embed x
    _ -> handleOther x

-- list of defer indexes for functions generated during eval. Need to be unique (grammar under defer n should always be the same)
[twiddleInd, unsizedStepMEInd, unsizedStepMTInd, unsizedStepMa, unsizedStepMrfa, unsizedStepMrfb, unsizedStepMw, removeRefinementWrappersTC, abortInd]
  = take 9 [-1, -2 ..]

deferB :: (Base g ~ f, StuckBase f, Recursive g, Corecursive g) => Int -> g -> g
deferB n = stuckEE . DeferSF (toEnum n)

lamB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => Int -> g -> g
lamB n x = pairB (deferB n x) envB

twiddleB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
twiddleB = deferB twiddleInd $ pairB (leftB (rightB envB)) (pairB (leftB envB) (rightB (rightB envB)))

appB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> g -> g
appB c i = setEnvB (setEnvB (pairB twiddleB (pairB i c)))

-- only intended for use inside of unsizedStep
iteB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> g -> g -> g
iteB i t e = fillFunction (fillFunction (gateB (deferB unsizedStepMEInd e) (deferB unsizedStepMTInd t)) i) envB -- TODO THIS IS HOW TO DO LAZY IF/ELSE, COPY!

argOneB :: (Base g ~ f, BasicBase f, Recursive g, Corecursive g) => g
argOneB = leftB envB
argTwoB :: (Base g ~ f, BasicBase f, Recursive g, Corecursive g) => g
argTwoB = leftB (rightB envB)
argThreeB :: (Base g ~ f, BasicBase f, Recursive g, Corecursive g) => g
argThreeB = leftB (rightB (rightB envB))
argFourB :: (Base g ~ f, BasicBase f, Recursive g, Corecursive g) => g
argFourB = leftB (rightB (rightB (rightB envB)))

unsizedTestIndexed :: (Base g ~ f, BasicBase f, AbortBase f, IndexedInputBase f, Recursive g, Corecursive g)
  => Set Integer -> (UnsizedRecursionToken -> g -> g) -> UnsizedRecursionToken -> g -> g
unsizedTestIndexed zeroes handleOther ri = \case
  iv@(IndexedEE (IVarF n)) -> debugTrace ("evalRecursionTest ivar " <> show n) $ if isUnbounded zeroes n
    then debugTrace ("evalRecursion punted to abort on " <> show n) abortEE . AbortedF . AbortUnsizeable . i2g . fromEnum $ ri
    else if Set.member n zeroes
    then debugTrace ("unsizedTestIndexed resolved to zero for var " <> show n) zeroB
    else iv
  x -> handleOther ri x

unsizedTestSuper :: (Base g ~ f, SuperBase f, AbortBase f, Recursive g, Corecursive g)
  => (g -> g) -> (UnsizedRecursionToken -> g -> g) -> UnsizedRecursionToken -> g -> g
unsizedTestSuper reTest handleOther ri = \case
  SuperEE (EitherPF n a b) -> let getAU = \case
                                    a@(AbortEE (AbortedF (AbortUnsizeable _))) -> Just a
                                    _ -> Nothing
                                  na = reTest a
                                  nb = reTest b
                                  Just r = getAU na <|> getAU nb <|> (Just . superEE $ EitherPF n na nb)
                              in r
  x -> handleOther ri x

unsizedTestDeferred :: (Base g ~ f, DeferredEvalBase f, Recursive g, Corecursive g)
  => (UnsizedRecursionToken -> g -> g) -> UnsizedRecursionToken -> g -> g
unsizedTestDeferred handleOther ri = \case
  x@(DeferredEE (BarrierF _)) -> x
  x -> handleOther ri x

unsizedTestUnsized :: (Base g ~ f, UnsizedBase f, Recursive g, Corecursive g)
  => (g -> g) -> (UnsizedRecursionToken -> g -> g) -> UnsizedRecursionToken -> g -> g
unsizedTestUnsized reTest handleOther ri = \case
  UnsizedEE (SizeStageF sm x) -> unsizedEE . SizeStageF sm $ reTest x
  x -> handleOther ri x


unsizedStep :: forall a f. (Base a ~ f, Traversable f, BasicBase f, StuckBase f, AbortBase f, UnsizedBase f
                           , Recursive a, Corecursive a, Eq a, PrettyPrintable a)
  => Int -> (UnsizedRecursionToken -> a -> a)
  -> (f a -> a) -> (f a -> a) -> f a -> a
unsizedStep maxSize recursionTest fullStep handleOther =
  let combineSizes :: SizedRecursion -> a -> a
      combineSizes sm = \case
        UnsizedEE (SizeStageF smb x) -> unsizedEE $ SizeStageF (smb <> sm) x
        x -> unsizedEE $ SizeStageF sm x
  in \case
    UnsizedFW (SizingWrapperF _ tok (BasicEE (PairSF d (BasicEE (PairSF b (BasicEE (PairSF r (BasicEE (PairSF tp (BasicEE ZeroSF))))))))))
      -> case tp of
            BasicEE (PairSF (StuckEE (DeferSF sid tf)) e) ->
              let nt = pairB (stuckEE . DeferSF sid . unsizedEE $ RecursionTestF tok tf) e
                  trb = pairB b (pairB r (pairB nt zeroB))
                  -- \t r b i ->
                  rf = lamB unsizedStepMrfa (iteB (appB argFourB argOneB)
                                              (appB (appB argThreeB (unsizedEE $ SizeStepStubF tok 1 envB)) argOneB)
                                              (unsizedEE . SizeStageF (SizedRecursion . Map.singleton tok $ pure 1) $ appB argTwoB argOneB))
              in pairB (deferB unsizedStepMw rf) trb
    UnsizedFW (SizeStepStubF tok n (BasicEE (PairSF _ e))) -> -- id -- debugTrace ("hit sizestepstub with " <> show n <> "\nand env of\n" <> prettyPrint e)
      pairB (deferB unsizedStepMrfa (unsizedEE . SizeStageF (SizedRecursion . Map.singleton tok $ pure (n + 1)) $ iteB (appB argFourB argOneB)
                                                (appB (appB argThreeB (unsizedEE $ SizeStepStubF tok (n + 1) envB)) argOneB)
                                                (appB argTwoB argOneB))) e
    UnsizedFW (RecursionTestF ri x) -> recursionTest ri x
    BasicFW (LeftSF (UnsizedEE (SizeStageF sm x))) -> combineSizes sm . fullStep . embedB $ LeftSF x
    BasicFW (RightSF (UnsizedEE (SizeStageF sm x))) -> combineSizes sm . fullStep . embedB $ RightSF x
    BasicFW (SetEnvSF (UnsizedEE (SizeStageF sm x))) -> combineSizes sm . fullStep . embedB $ SetEnvSF x
    FillFunction (UnsizedEE (SizeStageF sm x)) e -> combineSizes sm . fullStep . project $ fillFunction x e
    GateSwitch l r (UnsizedEE (SizeStageF sm x)) -> combineSizes sm . fullStep . project $ gateSwitch l r x
    -- stuck value
    ss@(UnsizedFW (SizeStageF _ _)) -> embed ss
    t@(UnsizedFW (RecursionTestF _ _)) -> embed t
    x -> handleOther x

unsizedStepM :: forall a f t m. (Base a ~ f, Traversable f, BasicBase f, StuckBase f, AbortBase f, UnsizedBase f
                            , Recursive a, Corecursive a, Eq a, PrettyPrintable a, m ~ StrictAccum SizedRecursion, MonadTrans t, Applicative (t m))
  => Int -> (UnsizedRecursionToken -> a -> a)
  -> (f a -> t m a) -> f a -> t m a
unsizedStepM maxSize recursionTest handleOther x = f x where
  f = \case
    UnsizedFW (SizingWrapperF _ tok (BasicEE (PairSF d (BasicEE (PairSF b (BasicEE (PairSF r (BasicEE (PairSF tp (BasicEE ZeroSF))))))))))
      -> case tp of
            BasicEE (PairSF (StuckEE (DeferSF sid tf)) e) ->
              let nt = pairB (stuckEE . DeferSF sid . unsizedEE $ RecursionTestF tok tf) e
                  trb = pairB b (pairB r (pairB nt zeroB))
                  argOne = leftB envB
                  argTwo = leftB (rightB envB)
                  argThree = leftB (rightB (rightB envB))
                  argFour = leftB (rightB (rightB (rightB envB)))
                  argFive = leftB (rightB (rightB (rightB (rightB envB))))
                  iteB i t e = fillFunction (fillFunction (gateB (deferB unsizedStepMEInd e) (deferB unsizedStepMTInd t)) i) envB -- TODO THIS IS HOW TO DO LAZY IF/ELSE, COPY!
                  abrt = lamB unsizedStepMa . abortEE . AbortedF $ AbortRecursion (i2g (fromEnum tok))
                  rf n = lamB unsizedStepMrfb (lamB unsizedStepMrfa (iteB (appB argFive argOne)
                                                                         (appB (appB argFour argTwo) argOne)
                                                                         (unsizedEE . SizeStageF (SizedRecursion . Map.singleton tok $ pure n)
                                                                          $ appB argThree argOne)))
                  -- rf' n = appB (rf n) (rf' (n + 1))
                  rf' n = if n > maxSize
                    -- then error "reached recursion limit"
                    then abrt
                    else appB (rf n) (rf' (n + 1))
              in pure $ pairB (deferB unsizedStepMw $ rf' 1) trb
    UnsizedFW (RecursionTestF ri x) -> pure $ recursionTest ri x
    -- UnsizedFW (SizeStageF urt n x) -> debugTrace ("unsizedStepM hit size of " <> show (urt, n)) StrictAccum (SizedRecursion $ Map.singleton urt n) x
    UnsizedFW (SizeStageF sr x) -> lift $ StrictAccum sr x
    -- stuck value
    t@(UnsizedFW (RecursionTestF _ _)) -> pure $ embed t
    _ -> handleOther x

forceSizes :: Int -> UnsizedExpr -> UnsizedExpr
forceSizes n = cata $ \case
  UnsizedFW (SizingWrapperF _ _ sx) -> sx
  UnsizedFW (UnsizedStubF _ _) -> iterate (basicEE . SetEnvSF) envB !! n
  x -> embed x

unsizedStepM' :: forall a f t m. (Base a ~ f, Traversable f, BasicBase f, StuckBase f, AbortBase f, UnsizedBase f, Recursive a, Corecursive a
                                   , Eq a, PrettyPrintable a, m ~ StrictAccum SizedRecursion, MonadTrans t, Applicative (t m))
  => Int -> Set Integer -> (UnsizedRecursionToken -> a -> a) -> (f a -> t m a) -> f a -> t m a
unsizedStepM' maxSize zeros recursionTest handleOther x = f x where
  f = \case
    UnsizedFW (SizingWrapperF _ tok uwe@(BasicEE (PairSF d (BasicEE (PairSF b (BasicEE (PairSF r (BasicEE (PairSF tp (BasicEE ZeroSF))))))))))
      -> case tp of
            BasicEE (PairSF (StuckEE (DeferSF sid tf)) e) ->
              let nt = pairB (stuckEE . DeferSF sid . unsizedEE $ RecursionTestF tok tf) e
                  trb = pairB b (pairB r (pairB nt zeroB))
                  argOne = leftB envB
                  argTwo = leftB (rightB envB)
                  argThree = leftB (rightB (rightB envB))
                  argFour = leftB (rightB (rightB (rightB envB)))
                  argFive = leftB (rightB (rightB (rightB (rightB envB))))
                  iteB i t e = fillFunction (fillFunction (gateB (deferB unsizedStepMEInd e) (deferB unsizedStepMTInd t)) i) envB -- TODO THIS IS HOW TO DO LAZY IF/ELSE, COPY!
                  abrt = lamB unsizedStepMa . abortEE . AbortedF $ AbortRecursion (i2g (fromEnum tok))
                  rf n = lamB unsizedStepMrfb (lamB unsizedStepMrfa (iteB (appB argFive argOne)
                                                                         (appB (appB argFour argTwo) argOne)
                                                                         (unsizedEE . SizeStageF (SizedRecursion . Map.singleton tok $ pure n)
                                                                          $ appB argThree argOne)))
                  -- rf' n = appB (rf n) (rf' (n + 1))
                  rf' n = if n > maxSize
                    -- then error "reached recursion limit"
                    then abrt
                    else appB (rf n) (rf' (n + 1))
                  dbt = id
              in pure . dbt $ pairB (deferB unsizedStepMw $ rf' 1) trb
    UnsizedFW (RecursionTestF ri x) -> pure $ recursionTest ri x
    -- UnsizedFW (SizeStageF urt n x) -> debugTrace ("unsizedStepM hit size of " <> show (urt, n)) StrictAccum (SizedRecursion $ Map.singleton urt n) x
    UnsizedFW (SizeStageF sr x) -> lift $ StrictAccum sr x
    -- stuck value
    t@(UnsizedFW (RecursionTestF _ _)) -> pure $ embed t
    _ -> handleOther x

unsizedStepM''' :: forall a f t m. (Base a ~ f, Traversable f, BasicBase f, StuckBase f, AbortBase f, UnsizedBase f, Recursive a, Corecursive a
                                   , Eq a, PrettyPrintable a, m ~ StrictAccum SizedRecursion, MonadTrans t, Applicative (t m))
  => Int -> Set Integer -> (UnsizedRecursionToken -> a -> a) -> (f a -> t m a) -> f a -> t m a
unsizedStepM''' maxSize zeros recursionTest handleOther x = f x where
  argOne = leftB envB
  argTwo = leftB (rightB envB)
  argThree = leftB (rightB (rightB envB))
  argFour = leftB (rightB (rightB (rightB envB)))
  iteB i t e = fillFunction (fillFunction (gateB (deferB unsizedStepMEInd e) (deferB unsizedStepMTInd t)) i) envB -- TODO THIS IS HOW TO DO LAZY IF/ELSE, COPY!
  dbt t = id -- trace ("unsizedStep hit unsized false branch for " <> show t)
  -- dbtse = unsizedEE . TraceF "sss else path"
  dbtse = id
  dbtw tok uwe = debugTrace ("inside sizing wrapper " <> show tok <> ":\n" <> prettyPrint uwe)
  dbrt x = x -- debugTrace ("unsized test value:\n" <> prettyPrint x) x
  -- dbtisss = unsizedEE . TraceF "inside expanded sss"
  dbtisss = id
  -- argTOne = leftB . unsizedEE $ TraceF "env inside sss" envB
  argTOne = leftB envB
  argT2One = leftB . unsizedEE $ TraceF "env inside unwrapped sizing wrapper" envB
  -- argT2One = leftB envB
  f = \case
    UnsizedFW (SizingWrapperF _ _ x) -> pure x
    UnsizedFW (UnsizedStubF tok (BasicEE (PairSF _ (BasicEE (PairSF _ (BasicEE (PairSF _ (BasicEE (PairSF _ env))))))))) -> case env of
      BasicEE (PairSF b (BasicEE (PairSF r (BasicEE (PairSF tp (BasicEE ZeroSF)))))) -> case tp of
        BasicEE (PairSF (StuckEE (DeferSF sid tf)) e) ->
          let nt = pairB (stuckEE . DeferSF sid . unsizedEE $ RecursionTestF tok tf) e
              trb = pairB b (pairB r (pairB nt zeroB))
              dbti = id
              -- \t r b i ->
              rf = deferB unsizedStepMrfa (iteB (dbti $ appB argFour argT2One)
                                          (appB (appB argThree (unsizedEE $ SizeStepStubF tok 1 envB)) argOne)
                                          (dbt tok . unsizedEE . SizeStageF (SizedRecursion . Map.singleton tok $ pure 1) $ appB argTwo argOne))
              result = pairB zeroB (pairB zeroB (pairB zeroB (pairB (pairB rf trb) zeroB)))
          in pure $ result
    UnsizedFW (SizeStepStubF tok n e@(BasicEE (PairSF _ es))) ->
      let dbti = id
      in pure $ pairB (deferB unsizedStepMrfa $ dbtisss (iteB (dbti $ appB argFour argTOne)
                                                (appB (appB argThree (unsizedEE $ SizeStepStubF tok (n + 1) e)) argOne)
                                                (dbtse . unsizedEE . SizeStageF (SizedRecursion . Map.singleton tok $ pure (n + 1)) $ appB argTwo argOne))) es
    UnsizedFW (RecursionTestF ri x) -> pure . recursionTest ri $ dbrt x
    UnsizedFW (SizeStageF sr x) -> lift . debugTrace ("Hit SizeStage: " <> show sr) $ StrictAccum sr x
    UnsizedFW (TraceF s x) -> pure $ debugTrace ("Hit TraceF: " <> s <> "\n" <> prettyPrint x) x
    _ -> handleOther x

zeroedInputStepM :: (Base a ~ g, Traversable f, IndexedInputBase f, BasicBase g, Corecursive a, Monad m) => Set Integer -> (f a -> m a) -> f a -> m a
zeroedInputStepM zeros handleOther = f where
  f = \case
    IndexedFW (IVarF n) | Set.member n zeros -> pure $ basicEE ZeroSF
    x -> handleOther x

indexedInputStep :: (Base a ~ f, BasicBase f, IndexedInputBase f, Recursive a, Corecursive a) => Set Integer -> (f a -> a) -> f a -> a
indexedInputStep zeroes handleOther =
  let res n = if Set.member n zeroes then zeroB else indexedEE $ IVarF n
  in \case
  BasicFW (LeftSF (IndexedEE (IVarF n))) -> res $ n * 2 + 1
  BasicFW (RightSF (IndexedEE (IVarF n))) -> res $ n * 2 + 2
  BasicFW (LeftSF (IndexedEE AnyF)) -> indexedEE AnyF
  BasicFW (RightSF (IndexedEE AnyF)) -> indexedEE AnyF
  IndexedFW (IVarF n) -> res n
  -- stuck values
  i@(IndexedFW _) -> embed i

  x -> handleOther x

{-
  7 8 9 A B C D E
   3   4   5   6
     1       2
         0
  B (11) : R -> L -> L
  P Z
    P Z
      Z
    Z

  11 % 2 = 1 -- L
  (11 - 1) / 2 = 5
  5 % 2 = 1 -- L
  (5 - 1) / 2 = 2
  2 % 2 = 0 -- R
  (2 - 1) / 2 = 0

-}

indexedInputStep' :: (Base a ~ f, BasicBase f, IndexedInputBase f, Recursive a, Corecursive a) => Set Integer -> (f a -> a) -> f a -> a
indexedInputStep' zeroes handleOther =
  let res n = if Set.member n zeroes then zeroB else indexedEE $ IVarF n
  in \case
  -- BasicFW (LeftSF (IndexedEE (IVarF n))) -> debugTrace ("indexedInputStep left " <> show n) . res $ n * 2 + 1
  BasicFW (LeftSF (IndexedEE (IVarF n))) -> res $ n * 2 + 1
  BasicFW (RightSF (IndexedEE (IVarF n))) -> res $ n * 2 + 2
  BasicFW (LeftSF (IndexedEE AnyF)) -> indexedEE AnyF
  BasicFW (RightSF (IndexedEE AnyF)) -> indexedEE AnyF
  IndexedFW (IVarF n) -> res n
  -- stuck values
  i@(IndexedFW _) -> embed i

  x -> handleOther x

indexAbortIfUnboundStep :: (Base a ~ f, BasicBase f, AbortBase f, IndexedInputBase f, Recursive a, Corecursive a, Show a) => Set Integer -> (f a -> a) -> f a -> a
indexAbortIfUnboundStep zeroes handleOther =
  -- let res s n = (\x -> debugTrace ("indexAbortIfUnboundStep res " <> s <> " " <> show n <> " " <> show x) x) $ case (Set.member n zeroes, isUnbounded zeroes n) of
  let res s n = case (Set.member n zeroes, isUnbounded zeroes n) of
        (True, _) -> zeroB
        (_, True) -> abortEE $ AbortedF AbortAny
        _ -> pairB (indexedEE . IVarF $ n * 2 + 1) (indexedEE . IVarF $ n * 2 + 2)
      leftI = \case
        BasicEE (PairSF l _) -> l
        x -> x
      rightI = \case
        BasicEE (PairSF _ r) -> r
        x -> x
  in \case
  BasicFW (LeftSF (IndexedEE (IVarF n))) -> leftI $ res "left" n
  BasicFW (RightSF (IndexedEE (IVarF n))) -> rightI $ res "right" n
  IndexedFW (IVarF n) -> res "bare" n
  x -> handleOther x

indexedInputStepM :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => Set Integer -> (f a -> m a) -> f a -> m a
indexedInputStepM zeroes handleOther x = f x where
  res n = if Set.member n zeroes then zeroB else indexedEE $ IVarF n
  f = \case
    BasicFW (LeftSF (IndexedEE (IVarF n))) -> pure . res $ n * 2 + 1
    BasicFW (RightSF (IndexedEE (IVarF n))) -> pure . res $ n * 2 + 2
    BasicFW (LeftSF (IndexedEE AnyF)) -> pure $ indexedEE AnyF
    BasicFW (RightSF (IndexedEE AnyF)) -> pure $ indexedEE AnyF
    BasicFW (SetEnvSF (IndexedEE AnyF)) -> pure $ indexedEE AnyF
    FillFunction (IndexedEE AnyF) _ -> pure $ indexedEE AnyF
    GateSwitch _ _ (IndexedEE AnyF) -> pure $ indexedEE AnyF
    IndexedFW (IVarF n) -> pure $ res n
    -- stuck values
    i@(IndexedFW _) -> pure $ embed i

    _ -> handleOther x

indexedInputStepM' :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => Set Integer -> (f a -> m a) -> f a -> m a
indexedInputStepM' zeroes handleOther x = f x where
  res n = if Set.member n zeroes then zeroB else indexedEE $ IVarF n
  f = \case
    -- BasicFW (LeftSF (IndexedEE (IVarF n))) -> debugTrace ("indexedInputStepM left " <> show n)  . pure . res $ n * 2 + 1
    BasicFW (LeftSF (IndexedEE (IVarF n))) -> pure . res $ n * 2 + 1
    BasicFW (RightSF (IndexedEE (IVarF n))) -> pure . res $ n * 2 + 2
    BasicFW (LeftSF (IndexedEE AnyF)) -> pure $ indexedEE AnyF
    BasicFW (RightSF (IndexedEE AnyF)) -> pure $ indexedEE AnyF
    BasicFW (SetEnvSF (IndexedEE AnyF)) -> pure $ indexedEE AnyF
    FillFunction (IndexedEE AnyF) _ -> pure $ indexedEE AnyF
    GateSwitch _ _ (IndexedEE AnyF) -> pure $ indexedEE AnyF
    IndexedFW (IVarF n) -> pure $ res n
    -- stuck values
    i@(IndexedFW _) -> pure $ embed i

    _ -> handleOther x

indexedInputIgnoreSwitchStepM :: (Base a ~ f, Traversable f, BasicBase f, IndexedInputBase f, Recursive a, Corecursive a, Monad m)
  => (f a -> m a) -> f a -> m a
indexedInputIgnoreSwitchStepM handleOther x = f x where
  f = \case
    GateSwitch _ _ (IndexedEE (IVarF _)) -> pure $ indexedEE AnyF
    _ -> handleOther x

indexSwitchSuperSplitStep :: (Base a ~ f, BasicBase f, IndexedInputBase f, SuperBase f, Recursive a, Corecursive a) => (f a -> a) -> f a -> a
indexSwitchSuperSplitStep handleOther = \case
  GateSwitch l r (IndexedEE AnyF) -> superEE $ EitherPF Nothing l r

  x -> handleOther x

deferredEvalStep :: (Base a ~ f, Traversable f, BasicBase f, DeferredEvalBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
deferredEvalStep handleOther = \case
    -- combine
    BasicFW (LeftSF (DeferredEE (BarrierF (DeferredEE (ManyLefts n x))))) -> deferredEE . BarrierF . deferredEE $ ManyLefts (n + 1) x
    BasicFW (RightSF (DeferredEE (BarrierF (DeferredEE (ManyRights n x))))) -> deferredEE . BarrierF . deferredEE $ ManyRights (n + 1) x
    BasicFW (LeftSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . deferredEE $ ManyLefts 1 x
    BasicFW (RightSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . deferredEE $ ManyRights 1 x
    BasicFW (SetEnvSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . basicEE $ SetEnvSF x
    FillFunction (DeferredEE (BarrierF c)) e -> deferredEE . BarrierF $ fillFunction c e
    GateSwitch l r (DeferredEE (BarrierF s)) -> deferredEE . BarrierF $ gateSwitch l r s
    -- stuck values
    d@(DeferredFW _) -> embed d

    x -> handleOther x

deferredEvalStep' :: (Base a ~ f, Traversable f, BasicBase f, DeferredEvalBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
deferredEvalStep' handleOther = \case
    BasicFW (LeftSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . basicEE $ LeftSF x
    BasicFW (RightSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . basicEE $ RightSF x
    BasicFW (SetEnvSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . basicEE $ SetEnvSF x
    FillFunction (DeferredEE (BarrierF c)) e -> deferredEE . BarrierF $ fillFunction c e
    GateSwitch l r (DeferredEE (BarrierF s)) -> deferredEE . BarrierF $ gateSwitch l r s
    -- stuck values
    d@(DeferredFW _) -> embed d

    x -> handleOther x

abortDeferredStep :: (Base a ~ f, BasicBase f, AbortBase f, DeferredEvalBase f, Recursive a, Corecursive a)
  => (f a -> a) -> f a -> a
abortDeferredStep handleOther = \case
  FillFunction a@(AbortEE AbortF) (DeferredEE (BarrierF e)) -> deferredEE . BarrierF $ fillFunction a e

  x -> handleOther x

-- is a variable limited in value or unbounded?
isUnbounded :: Set Integer -> Integer -> Bool
isUnbounded s n = f s where
  f s'
    | null s' = True
    | Set.member n s' = False
    | otherwise = (f . Set.map (flip div 2 . pred)) $ Set.filter (>= n) s'

extractZeroes :: InputSizingExpr -> Set Integer
extractZeroes = cleanup . f Nothing where
  f expected = f' expected . project
  f' :: Maybe Bool -> InputSizingExprF InputSizingExpr -> Maybe (StrictAccum (Set Integer) InputSizingExpr)
  f' expected = \case
    z@(BasicFW ZeroSF) -> case expected of
      Just True -> Nothing
      _         -> pure . pure $ embed z
    p@(BasicFW (PairSF _ _)) -> case expected of
      Just False -> Nothing
      _          -> pure . pure $ embed p
    -- IndexedFW (IVarF n) -> debugTrace ("extractZeroes hit ivar of " <> show n) $ case expected of
    IndexedFW (IVarF n) -> case expected of
      Just False -> Just (StrictAccum (Set.singleton n) $ basicEE ZeroSF)
      Just True  -> Just (StrictAccum Set.empty $ pairB zeroB zeroB)
      _          -> Just (StrictAccum Set.empty zeroB)
    -- FillFunction (AbortEE AbortF) i -> debugTrace ("extractZeroes hit abort with:\n" <> prettyPrint i) $ f (Just False) i
    FillFunction (AbortEE AbortF) i -> f (Just False) i
    GateSwitch l r s ->
      let nl = f expected l
          nr = f expected r
          pf = \case
            Just (StrictAccum s _) -> s
            _ -> Set.empty
      -- in debugTrace ("extractZeroes gate switch " <> show expected <> " " <> show (pf nl, pf nr) <> "\n" <> prettyPrint s) $ case (nl, nr) of
      in case (nl, nr) of
        (Nothing, Nothing) -> debugTrace "extractZeroes gate nothing" Nothing
        (Just (StrictAccum sta x), Just (StrictAccum stb _)) -> debugTrace "extractZeroes gate both" $ case f Nothing s of
          Nothing -> Nothing
          Just (StrictAccum st _) -> pure $ StrictAccum (st <> Set.intersection sta stb) x
        (Just (StrictAccum sta x), _) -> case f (Just False) s of
          Nothing                  -> Nothing
          Just (StrictAccum stb _) -> pure $ StrictAccum (sta <> stb) x
        (_, Just (StrictAccum sta x)) -> case f (Just True) s of
          Nothing                  -> Nothing
          Just (StrictAccum stb _) -> pure $ StrictAccum (sta <> stb) x
    _ -> Nothing
  cleanup = \case
    Just (StrictAccum s _) -> s
    _ -> Set.empty

zeroToBranch :: (Base a ~ f, BasicBase f, Corecursive a) => Integer -> a
{-
zeroToBranch = ana f where
  f 0 = embedB ZeroSF
  f n = let n' = div (n - 1) 2 in if even n
    then embedB (PairSF n' 0)
    else embedB (PairSF 0 n')
-}
zeroToBranch n = g n id where
  g :: (Base a ~ f, BasicBase f, Corecursive a) => Integer -> (a -> a) -> a
  g 0 f = f zeroB
  g n f = let g' = g (div (n - 1) 2) in if even n
    then g' (pairB zeroB . f)
    else g' (flip pairB zeroB . f)

testB :: UnsizedExpr
testB = zeroToBranch 11

pathToBranch :: Integer -> String
pathToBranch n = g n id where
  g 0 f = f []
  g n f = let g' = g (div (n - 1) 2) in if even n
    then g' (('R' :) . f)
    else g' (('L' :) . f)

-- "P Z\n  P P Z\n      Z\n    Z"
-- >>> prettyPrint testB
-- "P Z\n  P P Z\n      Z\n    Z"
--
-- >>> pathToBranch 11
-- "RLL"
-- >>> (' ' :) $ map toEnum [33..100]
-- " !\"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcd"


{-
  2   1
  4   3
  8   7
  16  15
  32  31
  64  63

  63 = 6L
  inputtest = 5L


  !
  "#
   $%&'
   ()*+,-./
   0123456789:;<=>?
   @ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_
   `abcd
-}

findInputLimitStepM :: (InputSizingExprF InputSizingExpr -> StrictAccum (Set Integer) InputSizingExpr)
  -> InputSizingExprF InputSizingExpr -> StrictAccum (Set Integer) InputSizingExpr
findInputLimitStepM handleOther x = f x where
  f = \case
    UnsizedFW (RefinementWrapperF lt tc c) ->
      let
        {-
          innerTC = appB (leftB envB) (rightB envB)
          performTC = deferB removeRefinementWrappersTC . setEnvB $ pairB (setEnvB $ pairB (abortEE AbortF) innerTC) (rightB envB)
-}
          performTC = setEnvB $ pairB (abortEE AbortF) (appB tc c)
          wrapDefer = \case
            -- g@(GateSwitch _ _ (IndexedEE _)) -> trace "wrapped defer" . deferredEE . BarrierF $ embed g
            GateSwitch l r i@(IndexedEE _) -> deferredEE . BarrierF $ gateSwitch (ev l) (ev r) i
            x -> error $ "findInputLimitStepM eval unexpected:\n" <> prettyPrint x
          evalStep = basicStep (stuckStep (abortStep (deferredEvalStep (abortDeferredStep (indexedInputStep' Set.empty wrapDefer)))))
          -- evalStep = basicStep (stuckStepDebug (abortStep (deferredEvalStep (abortDeferredStep (indexedInputStep' Set.empty wrapDefer)))))
          convertIL :: InputSizingExpr -> UnsizedExpr
          convertIL = cata f where
            f = convertBasic (convertStuck (convertAbort (convertIndexed convertFail)))
            convertFail z = error ("findInputLimitStepM convert failed on unexpected\n" <> prettyPrint z)
          ev = transformNoDefer evalStep
          stripBarrier = \case
            DeferredFW (BarrierF x) -> x
            x -> embed x
          -- dtit x = debugTrace ("findInputLimitStepM tc test unprocessed is:\n" <> prettyPrint x) x
          dtit = id
          -- dtit x = debugTrace ("findInputLimitStepM eval with test zero is:\n" <> prettyPrint (transformNoDefer evalStepT (convertIL x))) x
          -- dtt x = debugTrace ("findInputLimitStepM tc test is:\n" <> prettyPrint x) x
          dtt = id
          s = extractZeroes . cata stripBarrier . dtt . transformNoDefer evalStep . dtit $ performTC
          -- s = extractZeroes . cata stripBarrier . dtt . transformNoDefer evalStep . dtit . setEnvB $ pairB performTC (pairB tc c)
      in StrictAccum s c
    _ -> handleOther x

unsized2abortExpr :: UnsizedExpr -> AbortExpr
unsized2abortExpr = cata (convertBasic (convertStuck (convertAbort unexpected))) where
  unexpected x = error $ "unsized2abortExpr unexpected unsized bit: " <> prettyPrint (fmap (const ' ') x)

term3ToUnsizedExpr :: Int -> Term3 -> UnsizedExpr
term3ToUnsizedExpr maxSize (Term3 termMap) =
  let fragLookup = (termMap Map.!)
      f = \case
        ZeroFrag -> basicEE ZeroSF
        PairFrag a b -> basicEE $ PairSF (f a) (f b)
        EnvFrag -> basicEE EnvSF
        SetEnvFrag x -> basicEE . SetEnvSF $ f x
        DeferFrag ind -> stuckEE . DeferSF (toEnum $ fromEnum ind) . f . forget . unFragExprUR $ fragLookup ind
        AbortFrag -> abortEE AbortF
        GateFrag l r -> basicEE $ GateSF (f l) (f r)
        LeftFrag x -> basicEE . LeftSF $ f x
        RightFrag x -> basicEE . RightSF $ f x
        TraceFrag -> unsizedEE . TraceF "from Term3" $ basicEE EnvSF
        AuxFrag (SizingWrapper loc tok (FragExprUR x)) -> unsizedEE . SizingWrapperF loc tok . f $ forget x
        AuxFrag (NestedSetEnvs t) -> unsizedEE . UnsizedStubF t . embed $ embedB EnvSF
        AuxFrag (CheckingWrapper loc (FragExprUR tc) (FragExprUR c)) -> unsizedEE $ RefinementWrapperF loc (f $ forget tc) (f $ forget c)
  in f . forget . unFragExprUR $ rootFrag termMap

-- get simple input limits derived from refinements
-- returns a set of guaranteed Zeros, where the Integer is the encoded path from root of intput
getInputLimits :: UnsizedExpr -> Set Integer
getInputLimits = getAccum . transformNoDeferM evalStep . convertIS where
  convertU = \case
    UnsizedFW (SizingWrapperF _ _ _) -> indexedEE AnyF
    UnsizedFW (UnsizedStubF _ _) -> indexedEE AnyF
    UnsizedFW (RecursionTestF _ x) -> x
    UnsizedFW rw@(RefinementWrapperF _ _ _) -> unsizedEE rw
    x -> error $ "getInputLimits convert, unhandled:\n" <> prettyPrint x
  convertIS :: UnsizedExpr -> InputSizingExpr
  convertIS = cata $ convertBasic (convertStuck (convertAbort (convertIndexed convertU)))
  unexpectedI x = error $ "getInputLimits eval, unexpected:\n" <> prettyPrint x
  evalStep = basicStepM (stuckStepM (abortStepM (indexedInputStepM Set.empty (indexedInputIgnoreSwitchStepM (findInputLimitStepM unexpectedI)))))

capMain :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> g -> g
capMain i c = appB c i


isClosure :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> Bool
isClosure = \case
  BasicEE (PairSF (StuckEE (DeferSF _ _)) _) -> True
  _                                          -> False

sizeTerm :: Int -> UnsizedExpr -> Either UnsizedRecursionToken AbortExpr
sizeTerm maxSize x = tidyUp . foldAborted . debugResult . transformNoDefer evalStep $ peTerm where
  failConvert x = error $ "sizeTerm convert, unhandled:\n" <> prettyPrint x
  forceType :: StuckExpr -> StuckExpr
  forceType = id
  showZeros z = debugTrace ("sizeTerm zeros are: " <> show z <> "\nzeros are:\n" <> concatMap (prettyPrint . forceType . zeroToBranch) z)
  --zeros = (\x -> debugTrace ("sizeTerm zeros are " <> show x) x) $ getInputLimits x
  zeros = (\z -> showZeros z z) $ getInputLimits x
  debugResult r = debugTrace ("sizeTerm result is\n" <> prettyPrint r) r
  {-
  convertForPartial :: UnsizedExpr -> InputSizingExpr
  convertForPartial = cata $ convertBasic (convertStuck (convertAbort (convertUnsized (convertIndexed failConvert))))
  convertFromPartial :: InputSizingExpr -> UnsizedExpr
  convertFromPartial = cata $ convertBasic (convertStuck (convertAbort (convertUnsized (convertIndexed failConvert))))
-}
  -- cm = removeRefinementWrappers . capMain (indexedEE $ IVarF 0) $ convertForPartial x
  cm = removeRefinementWrappers $ capMain (indexedEE $ IVarF 0) x
  -- showSizes sm x = debugTrace ("sizes are: " <> show sm <> "\nzeros are:\n" <> concatMap (prettyPrint . zeroToBranch) sm)
  showSizes sm = debugTrace ("sizes are: " <> show sm)
  tidyUp =  \case
    (Just (UnsizableSR i), sm) -> Left i
    (_, SizedRecursion sm) -> let sized = showSizes sm $ setSizes sm peTerm
                              in pure . clean $ if isClosure x
                                                then uncap sized
                                                else sized
      where uncap = \case
              BasicEE (SetEnvSF (BasicEE (PairSF d _))) -> basicEE $ PairSF d (basicEE ZeroSF)
              z -> error ("sizeTerm tidyUp trying to uncap something that isn't a main function: " <> show z)
  clean :: UnsizedExpr -> AbortExpr
  clean = cata (convertBasic (convertStuck (convertAbort failConvert)))
  convertPartialError x = error ("convertPartialSizing unhandled " <> prettyPrint x)
  tracePartialSizes = id
  setSizes :: Map UnsizedRecursionToken (Maybe Int) -> UnsizedExpr -> UnsizedExpr
  setSizes sizeMap = cata $ \case
    UnsizedFW sw@(SizingWrapperF loc tok sx) -> sx
    UnsizedFW us@(UnsizedStubF tok _) -> tracePartialSizes $ case Map.lookup tok sizeMap of
      Just (Just n) -> debugTrace ("sizeTerm setting size: " <> show (tok, n)) iterate (basicEE . SetEnvSF) (basicEE EnvSF) !! n
      _      ->  basicEE . SetEnvSF $ basicEE EnvSF
    x -> embed x
  setSomeSizes :: Map UnsizedRecursionToken (Maybe Int) -> InputSizingExpr -> InputSizingExpr
  setSomeSizes sizeMap = cata $ \case
    UnsizedFW sw@(SizingWrapperF loc tok sx) -> case Map.lookup tok sizeMap of
      Just (Just _) -> sx
      _             -> embed $ embedU sw
    UnsizedFW us@(UnsizedStubF tok _) -> tracePartialSizes $ case Map.lookup tok sizeMap of
      Just (Just n) -> iterate (basicEE . SetEnvSF) (basicEE EnvSF) !! n
      _             -> embed $ embedU us
    x -> embed x
  foldAborted = cata f where
    f = \case
      AbortFW (AbortedF (AbortRecursion _)) -> (Just . UnsizableSR $ toEnum (-2), mempty)
      AbortFW (AbortedF AbortAny) -> (Just . UnsizableSR $ toEnum (-1), mempty)
      AbortFW (AbortedF (AbortUnsizeable t)) -> (Just . UnsizableSR . toEnum . g2i $ t, mempty)
      UnsizedFW (SizeStageF sm x) -> (Nothing, sm) <> x
      x                                 -> Data.Foldable.fold x
  nextPartialSizing (SizedRecursion sm, expr) = debugTrace ("partialSizes setting " <> show sm) $
    if not (null sm)
    then let nexpr = setSomeSizes sm expr in (evalPartialUnsized zeros nexpr, nexpr)
    else (evalPartialUnsized zeros expr, expr)
  hasSizes (SizedRecursion sm, _) = not . null $ Map.filter (not . null) sm
  {-
  peTerm = snd . head . dropWhile hasSizes . tail
    $ iterate nextPartialSizing (SizedRecursion Map.empty, cm)
-}
  -- peTerm = convertFromPartial cm -- in case debugging is needed
  peTerm = cm -- in case debugging is needed
  unhandledMerge x y = error ("sizeTerm unhandledMerge: " <> show (x,y))
  unhandledGate x = error ("sizeTerm unhandled gate input: " <> show x)
  gateResult = debugTrace "gateResult" gateBasicResult (gateAbortResult (gateIndexedResult (gateSuperResult gateResult unhandledGate)))
  unsizedTest ri = unsizedTestIndexed zeros (unsizedTestSuper (unsizedTest ri) (unsizedTestUnsized (unsizedTest ri) (const id))) ri
  evalStep = basicStep (stuckStep (abortStep (indexedAbortStep (indexedInputStep zeros (indexedSuperStep (superUnsizedStep gateResult evalStep (superAbortStep evalStep (unsizedStep maxSize unsizedTest evalStep unhandledError))))))))
  unhandledError x = error ("sizeTerm unhandled case\n" <> prettyPrint x)



sizeTermM :: Int -> Bool -> UnsizedExpr -> Either UnsizedRecursionToken AbortExpr
sizeTermM maxSize doCap x = tidyUp . ($ []) . runReaderT . transformNoDeferM evalStep $ cm where
  failConvert x = error $ "sizeTermM convert, unhandled:\n" <> prettyPrint x
  forceType :: StuckExpr -> StuckExpr
  forceType = id
  showZeros z = "\nsizeTermM zeros are: " <> show z <> "\nzeros are:\n" <> concatMap ((<> "\n") . prettyPrint . forceType . zeroToBranch) z
  -- zeros = (\x -> debugTrace ("sizeTerm zeros are " <> show x) x) $ getInputLimits x
  zeros = (\x -> debugTrace ("sizeTermM inital term is\n" <> prettyPrint cm <> showZeros x) x) $ getInputLimits cm'
  -- zeros = getInputLimits x
  dtt :: UnsizedExpr -> UnsizedExpr
  -- dtt t = debugTrace ("sizeTermM initial term is\n" <> prettyPrint t <> "\n...and result should be\n" <> prettyPrint (regularEval t)) t
  dtt t = debugTrace ("sizeTermM initial term is\n" <> prettyPrint t) t
  cm' = dtt $ if doCap
    then capMain (indexedEE $ IVarF 0) x
    else x
  cm = removeRefinementWrappers cm'
  tidyUp (StrictAccum (SizedRecursion sm) r) = debugTrace ("sizes are: " <> show sm <> "\nand result is:\n" <> prettyPrint r) $ case foldAborted r of
    Just (UnsizableSR i) -> debugTrace "sizeTermM hit unsizable" Left i
    _ -> let sized = setSizes sm cm
         in debugTrace "sizeTermM found all sizes" pure . clean $ if doCap
            then uncap sized
            else sized
      where uncap = \case
              AppEE c _ -> c
              z -> error ("sizeTermM tidyUp trying to uncap something that isn't a main function:\n" <> prettyPrint z)
  clean :: UnsizedExpr -> AbortExpr
  clean = cata (convertBasic (convertStuck (convertAbort failConvert)))
  setSizes :: Map UnsizedRecursionToken (Maybe Int) -> UnsizedExpr -> UnsizedExpr
  setSizes sizeMap = cata $ \case
    UnsizedFW sw@(SizingWrapperF loc tok sx) -> sx
    UnsizedFW us@(UnsizedStubF tok _) -> case Map.lookup tok sizeMap of
      Just (Just n) -> trace ("sizeTermM setting size: " <> show (tok, n)) iterate (basicEE . SetEnvSF) envB !! (n + 1)
      _      -> trace ("no size found for " <> show tok) setEnvB $ leftB envB
    UnsizedFW (TraceF _ x) -> x
    x -> embed x
  foldAborted = cata f where
    f = \case
      AbortFW (AbortedF (AbortRecursion i)) -> error $ "sizeTermM AbortRecursion hit, which should never happen, for token " <> show (g2i i)
      AbortFW (AbortedF AbortAny) -> error "sizeTermM AbortAny hit"
      AbortFW (AbortedF (AbortUnsizeable t)) -> Just . UnsizableSR . toEnum . g2i $ t
      x                                 -> Data.Foldable.fold x
  unhandledMerge x y = error ("sizeTermM unhandledMerge: " <> show (x,y))
  unhandledGate x = error ("sizeTermM unhandled gate input: " <> show x)
  gateResult = gateBasicResult (gateAbortResult (gateIndexedResult (gateSuperResult gateResult unhandledGate)))
  unsizedTest :: UnsizedRecursionToken -> UnsizedExpr -> UnsizedExpr
  unsizedTest ri = unsizedTestIndexed zeros (unsizedTestSuper (unsizedTest ri) (const id)) ri
  -- unsizedTest' ri = (\x -> debugTrace ("unsizedTest value of\n" <> prettyPrint x) x) . unsizedTest ri
  unsizedTest' ri = unsizedTest ri . (\x -> debugTrace ("unsizedTest value of\n" <> prettyPrint x) x)
  unhandledError x = error ("sizeTerm unhandled case\n" <> prettyPrint x)
  -- evalStep = basicStepM (stuckStepWithTrace (abortStepM (indexedAbortStepM (indexedInputStepM zeros (indexedSuperStepM (superStepM gateResult evalStep (superAbortStepM evalStep (unsizedStepM maxSize unsizedTest failAndPrintStack))))))))
  evalStep = basicStepM (stuckStepDebugM (abortStepM (indexedAbortStepM (indexedInputStepM zeros (indexedSuperStepM (superStepM gateResult evalStep (superAbortStepM evalStep (unsizedStepM''' maxSize zeros unsizedTest unhandledError))))))))
  -- evalStep = basicStepM (stuckStepWithTrace (abortStepM (indexedAbortStepM (indexedInputStepM zeros (indexedSuperStepM (superStepM gateResult evalStep (superAbortStepM evalStep (unsizedStepM''' maxSize zeros unsizedTest failAndPrintStack))))))))

{-
evalTrace :: (Base a ~ f, BasicBase f, StuckBase f, AbortBase f, IndexedInputBase f, SuperBase f, UnsizedBase f, Traversable f, ShallowEq1 f
             , Recursive a, Corecursive a, PrettyPrintable a, Show a) => a -> a
evalTrace x = debugTrace ("evalTrace:\n" <> prettyPrint (transformNoDefer evalStepT x)) x where
          unhandledGate x = error ("findInputLimitStepM evalT unhandled gate input: " <> show x)
          gateResult = gateBasicResult (gateAbortResult (gateIndexedResult (gateSuperResult gateResult unhandledGate)))
          testZ = Set.singleton $ toEnum 127
          evalError z = error $ "findInputLimitStepM evalT unexpected:\n" <> prettyPrint (embed z)
          -- evalStepT = basicStep (stuckStep (abortStep (indexAbortIfUnboundStep testZ (indexedSuperStep (superAbortStep evalStepT (superStep gateResult evalStepT evalError))))))
          evalStepT = basicStep (stuckStep (abortStep (indexedInputStep testZ (indexedSuperStep (superAbortStep evalStepT (superStep gateResult evalStepT (traceRefinement evalStepT evalError)))))))
-}

-- inputtest zero: 59 L - 60 L actual
abortPossibilities :: Int -> UnsizedExpr -> Set IExpr
abortPossibilities maxSize x = tidyUp . ($ []) . runReaderT . transformNoDeferM evalStep $ cm where
  failConvert x = error $ "abortPossibilities convert, unhandled:\n" <> prettyPrint x
  -- zeros = (\x -> debugTrace ("sizeTerm zeros are " <> show x) x) $ getInputLimits x
  forceType :: StuckExpr -> StuckExpr
  forceType = id
  showZeros z = "\nabortPossibilities zeros are: " <> show z <> "\nzeros are:\n" <> concatMap (prettyPrint . forceType . zeroToBranch) z
  -- zeros = (\x -> debugTrace ("sizeTerm inital term is\n" <> prettyPrint cm <> showZeros x) x) $ getInputLimits x
  zeros = getInputLimits x
  -- cm = removeRefinementWrappers . evalTrace $ capMain (indexedEE $ IVarF 0) x -- traceRefinement
  cm = removeRefinementWrappers $ capMain (indexedEE $ IVarF 0) x
  tidyUp (StrictAccum (SizedRecursion sm) r) = debugTrace ("sizes are: " <> show sm <> "\nand result is:\n" <> prettyPrint r) $ foldAborted r
  clean :: UnsizedExpr -> AbortExpr
  clean = cata (convertBasic (convertStuck (convertAbort failConvert)))
  setSizes :: Map UnsizedRecursionToken (Maybe Int) -> UnsizedExpr -> UnsizedExpr
  setSizes sizeMap = cata $ \case
    UnsizedFW sw@(SizingWrapperF loc tok sx) -> sx
    UnsizedFW us@(UnsizedStubF tok _) -> case Map.lookup tok sizeMap of
      Just (Just n) -> debugTrace ("abortPossibilities setting size: " <> show (tok, n)) iterate (basicEE . SetEnvSF) (basicEE EnvSF) !! n
      _      ->  basicEE . SetEnvSF $ basicEE EnvSF
    x -> embed x
  foldAborted = cata f where
    f = \case
      AbortFW (AbortedF x) -> Set.singleton x
      x                                 -> Data.Foldable.fold x
  unhandledMerge x y = error ("abortPossibilities unhandledMerge: " <> show (x,y))
  unhandledGate x = error ("abortPossibilities unhandled gate input: " <> show x)
  gateResult = gateBasicResult (gateAbortResult (gateIndexedResult (gateSuperResult gateResult unhandledGate)))
  unsizedTest :: UnsizedRecursionToken -> UnsizedExpr -> UnsizedExpr
  unsizedTest ri = unsizedTestIndexed zeros (unsizedTestSuper (unsizedTest ri) (const id)) ri
  -- unsizedTest' ri = (\x -> debugTrace ("unsizedTest value of\n" <> prettyPrint x) x) . unsizedTest ri
  unsizedTest' ri = unsizedTest ri . (\x -> debugTrace ("unsizedTest value of\n" <> prettyPrint x) x)
  unhandledError x = error ("abortPossibilities unhandled case\n" <> prettyPrint x)
  -- evalStep = basicStepM (stuckStepWithTrace (abortStepM (indexedAbortStepM (indexedInputStepM zeros (indexedSuperStepM (superStepM gateResult evalStep (superAbortStepM evalStep (unsizedStepM maxSize unsizedTest failAndPrintStack))))))))
  -- evalStep = basicStepM (stuckStepDebugM (abortStepM (indexedAbortStepM (indexedInputStepM zeros (indexedSuperStepM (superStepM gateResult evalStep (superAbortStepM evalStep (unsizedStepM''' maxSize zeros unsizedTest unhandledError))))))))
  evalStep = basicStepM (stuckStepWithTrace (abortStepM (indexedAbortStepM (indexedInputStepM zeros (indexedSuperStepM (superStepM gateResult evalStep (superAbortStepM evalStep (unsizedStepM''' maxSize zeros unsizedTest failAndPrintStack))))))))

getSizesM :: Int -> UnsizedExpr -> Either UnsizedRecursionToken SizedRecursion
getSizesM maxSize x = tidyUp . ($ []) . runReaderT . transformNoDeferM evalStep $ cm where
  failConvert x = error $ "getSizesM convert, unhandled:\n" <> prettyPrint x
  -- zeros = (\x -> debugTrace ("sizeTerm zeros are " <> show x) x) $ getInputLimits x
  -- zeros = (\x -> debugTrace ("sizeTerm inital term is\n" <> prettyPrint cm <> "\nsizeTerm zeros are " <> show x) x) $ getInputLimits x
  zeros = getInputLimits x
  cm = removeRefinementWrappers $ capMain (indexedEE $ IVarF 0) x
  tidyUp (StrictAccum sr@(SizedRecursion sm) r) = debugTrace ("sizes are: " <> show sm <> "\nand result is:\n" <> prettyPrint r) $ case foldAborted r of
    Just (UnsizableSR i) -> Left i
    _                    -> pure sr
  foldAborted = cata f where
    f = \case
      AbortFW (AbortedF (AbortRecursion _)) -> Just . UnsizableSR $ toEnum (-2)
      AbortFW (AbortedF AbortAny) -> Just . UnsizableSR $ toEnum (-1)
      AbortFW (AbortedF (AbortUnsizeable t)) -> Just . UnsizableSR . toEnum . g2i $ t
      x                                 -> Data.Foldable.fold x
  unhandledMerge x y = error ("getSizesM unhandledMerge: " <> show (x,y))
  unhandledGate x = error ("getSizesM unhandled gate input: " <> show x)
  gateResult = gateBasicResult (gateAbortResult (gateIndexedResult (gateSuperResult gateResult unhandledGate)))
  unsizedTest :: UnsizedRecursionToken -> UnsizedExpr -> UnsizedExpr
  unsizedTest ri = unsizedTestIndexed zeros (unsizedTestSuper (unsizedTest ri) (const id)) ri
  -- unsizedTest' ri = (\x -> debugTrace ("unsizedTest value of\n" <> prettyPrint x) x) . unsizedTest ri
  unsizedTest' ri = unsizedTest ri . (\x -> debugTrace ("getSizesM value of\n" <> prettyPrint x) x)
  unhandledError x = error ("getSizesM unhandled case\n" <> prettyPrint x)
  -- evalStep = basicStepM (stuckStepWithTrace (abortStepM (indexedAbortStepM (indexedInputStepM zeros (indexedSuperStepM (superStepM gateResult evalStep (superAbortStepM evalStep (unsizedStepM maxSize unsizedTest failAndPrintStack))))))))
  -- evalStep = basicStepM (stuckStepDebugM (abortStepM (indexedAbortStepM (indexedInputStepM zeros (indexedSuperStepM (superStepM' gateResult evalStep (superAbortStepM evalStep (unsizedStepM''' maxSize zeros unsizedTest unhandledError))))))))
  evalStep = basicStepM (stuckStepWithTrace (abortStepM (indexedAbortStepM (indexedInputStepM zeros (indexedSuperStepM (superStepM gateResult evalStep (superAbortStepM evalStep (unsizedStepM''' maxSize zeros unsizedTest' failAndPrintStack))))))))

buildUnsizedLocMap :: UnsizedExpr -> Map UnsizedRecursionToken LocTag
buildUnsizedLocMap = cata f where
  f = \case
    UnsizedFW (SizingWrapperF loc tok x) -> x <> Map.singleton tok loc
    x -> Data.Foldable.fold x

removeRefinementWrappers :: (Base g ~ f, BasicBase f, StuckBase f, AbortBase f, UnsizedBase f, Recursive g, Corecursive g) => g -> g
removeRefinementWrappers = cata f where
  f = \case
    UnsizedFW (RefinementWrapperF lt tc c) ->
      let innerTC = appB (leftB envB) (rightB envB)
          performTC = deferB removeRefinementWrappersTC . setEnvB $ pairB (setEnvB $ pairB (abortEE AbortF) innerTC) (rightB envB)
      in setEnvB $ pairB performTC (pairB tc c)
      -- in unsizedEE . TraceF "refinement eval" . setEnvB $ pairB performTC (pairB tc c)
    x -> embed x
{-
traceRefinement :: (Base g ~ f, BasicBase f, StuckBase f, AbortBase f, UnsizedBase f, Recursive g, Corecursive g, PrettyPrintable g)
  => (f g -> g) -> (f g -> g) -> f g -> g
traceRefinement step handleOther = \case
    UnsizedFW (RefinementWrapperF lt tc c) ->
      let innerTC = appB (leftB envB) (rightB envB)
          performTC = deferB removeRefinementWrappersTC . setEnvB $ pairB (setEnvB $ pairB (abortEE AbortF) innerTC) (rightB envB)
          dt x = debugTrace ("traceRefinement:\n" <> prettyPrint x) x
          dta x = debugTrace ("traceRefinement result:\n" <> prettyPrint x) x
      in dta . step . project . dt . setEnvB $ pairB performTC (pairB tc c)
    x -> handleOther x
-}

regularEval :: forall f g. (Base g ~ f, BasicBase f, StuckBase f, AbortBase f, IndexedInputBase f, UnsizedBase f
               , Recursive g, Corecursive g, PrettyPrintable g) => g -> g
regularEval = transformNoDefer f . cata ss where
  -- f :: f g -> g
  f = basicStep (stuckStepDebug (abortStep (indexedInputStep Set.empty unhandledError)))
  unhandledError z = error ("regularEval unhandled case\n" <> prettyPrint (embed z))
  ss :: f g -> g
  ss = \case
    UnsizedFW (RefinementWrapperF lt tc c) ->
      let innerTC = appB (leftB envB) (rightB envB)
          performTC = deferB removeRefinementWrappersTC . setEnvB $ pairB (setEnvB $ pairB (abortEE AbortF) innerTC) (rightB envB)
      in setEnvB $ pairB performTC (pairB tc c)
    UnsizedFW (SizingWrapperF _ _ x) -> x
    UnsizedFW (UnsizedStubF _ _) -> iterate setEnvB envB !! 255
    x -> embed x
    -- z -> error ("regularEval unhandled case\n" <> prettyPrint (embed z))

evalBU :: IExpr -> Either RunTimeError IExpr
evalBU = pure . toIExpr . ebu . fromTelomare where
  toIExpr = unwrapMaybe . toTelomare
  unwrapMaybe = \case
    Just x -> x
    Nothing -> error "evalBU: could not convert back to IExpr"
  ebu :: StuckExpr -> StuckExpr
  ebu = transformNoDefer (basicStep (stuckStep undefined)) . (\x -> debugTrace ("evalBU starting expr:\n" <> prettyPrint x) x)

evalBU' :: IExpr -> IO IExpr
evalBU' = rewrap . evalBU where
  rewrap = \case
    Left e -> print e >> pure Zero
    Right x -> pure x

term4toAbortExpr :: (Base g ~ f, BasicBase f, StuckBase f, AbortBase f, Corecursive g) => Term4 -> g
term4toAbortExpr (Term4 termMap') =
  let termMap = forget <$> termMap'
      convertFrag' = embed . convertFrag
      convertFrag = \case
        ZeroFrag      -> embedB ZeroSF
        PairFrag a b  -> embedB $ PairSF (convertFrag' a) (convertFrag' b)
        EnvFrag       -> embedB EnvSF
        SetEnvFrag x  -> embedB . SetEnvSF $ convertFrag' x
        DeferFrag ind -> embedS . DeferSF (toEnum . fromEnum $ ind) . convertFrag' $ termMap Map.! ind
        AbortFrag     -> embedA AbortF
        GateFrag l r  -> embedB $ GateSF (convertFrag' l) (convertFrag' r)
        LeftFrag x    -> embedB . LeftSF $ convertFrag' x
        RightFrag x   -> embedB . RightSF $ convertFrag' x
        TraceFrag     -> embedB EnvSF
        z             -> error ("term4toAbortExpr'' unexpected " <> show z)
  in convertFrag' (rootFrag termMap)

abortExprToTerm4 :: (Base g ~ f, BasicBase f, StuckBase f, AbortBase f, Foldable f, Recursive g) => g -> Either IExpr Term4
abortExprToTerm4 x =
  let
    dl = (DummyLoc :<)
    pv = pure . dl
    findAborted = cata $ \case
      AbortFW (AbortedF e) -> Just e
      x                    -> asum x
    convert = \case
      BasicFW ZeroSF        -> pv ZeroFragF
      BasicFW (PairSF a b)  -> dl <$> (PairFragF <$> a <*> b)
      BasicFW EnvSF         -> pv EnvFragF
      BasicFW (SetEnvSF x)  -> dl . SetEnvFragF <$> x
      StuckFW (DeferSF _ x) -> deferF x
      AbortFW AbortF        -> pv AbortFragF
      BasicFW (GateSF l r)  -> dl <$> (GateFragF <$> l <*> r)
      BasicFW (LeftSF x)    -> dl . LeftFragF <$> x
      BasicFW (RightSF x)   -> dl . RightFragF <$> x
      z                     -> error "abortExprToTerm4 unexpected thing "
  in case findAborted x of
    Just e -> Left e
    _      -> pure . Term4 . buildFragMap . cata convert $ x

newtype PPOut a = PPOut a
--   deriving Functor

instance {-# OVERLAPPING #-} PrettyPrintable (PPOut CompiledExpr) where
  showP (PPOut x) = f x where
    f = \case
      BasicEE ZeroSF -> pure ""
      BasicEE (PairSF a b) -> liftA2 (<>) (doLet a) (f b)
      z -> indentWithTwoChildren' "#!#" (pure "") (showP z)
    doLet x = case cata lf x of
      Just n -> pure $ chr n : []
      _ -> indentWithTwoChildren' "#/#" (pure "") (showP x)
    lf = \case
      BasicFW ZeroSF -> Just 0
      BasicFW (PairSF n (Just 0)) -> succ <$> n
      _ -> Nothing

instance AbstractRunTime CompiledExpr where
  eval = checkError . (\x -> debugTrace ("CompiledExpr eval " <> dumpEval x) x) . transformNoDefer step where
    dumpEval = \case
      BasicEE (PairSF o s) -> "output:\n" <> prettyPrint (PPOut o) <> "\nnew state:\n" <> prettyPrint s
      z -> "unexpected eval state:\n" <> prettyPrint z
    step = basicStep (stuckStepDebug (abortStep unhandledError))
    unhandledError x = error $ "CompiledExpr eval unhandled case " <> prettyPrint x
    findError = \case
      AbortFW (AbortedF e) -> Just e
      x -> asum x
    checkError x = case cata findError x of
      Just e -> Left $ AbortRunTime e
      _      -> pure x

evalStaticCheck :: Bool -> StaticCheckExpr -> Maybe IExpr
evalStaticCheck doCap t =
  let unhandledError x = error ("evalA unhandled case " <> prettyPrint x)
      runResult = let aStep :: StaticCheckExprF StaticCheckExpr -> StaticCheckExpr
                      aStep = basicStep (stuckStep (abortStep (deferredEvalStep' unhandledError)))
                      eval' :: StaticCheckExpr -> StaticCheckExpr
                      eval' = transformNoDefer aStep
                      inp = deferredEE $ BarrierF envB
                      x = (\x' -> debugTrace ("evalA starting expr:\n" <> prettyPrint x') x') $ if doCap then capMain inp t else t
                  in eval' x
      getAborted = \case
        AbortFW (AbortedF e) -> Just e
        DeferredFW (BarrierF _) -> Nothing
        x                    -> foldr (<|>) Nothing x
  in cata getAborted runResult

evalPartial :: (Base g ~ f, Traversable f, BasicBase f, StuckBase f, DeferredEvalBase f, Recursive g, Corecursive g, PrettyPrintable g)
  => g -> g
evalPartial = cata removeBarriers . transformNoDefer step where
  step = deferStep (basicStep (stuckStep (deferredEvalStep' wrapUnknownStep)))
  deferStep handleOther = \case
    StuckFW (DeferSF id x) -> deferB (fromEnum id) . cata removeBarriers $ transformNoDefer (step . addBarrier) x
    x -> handleOther x
  addBarrier = \case
    BasicFW EnvSF -> embedD $ BarrierF envB
    x -> x
  removeBarriers = \case
    DeferredFW (BarrierF x) -> x
    x -> seq x $ embed x -- does seq have any performance consequence here?
  wrapUnknownStep = deferredEE . BarrierF . embed

evalPartial' :: IExpr -> IExpr
evalPartial' = toIExpr . ep . fromTelomare where
  toIExpr = unwrapMaybe . toTelomare
  unwrapMaybe = \case
    Just x -> x
    Nothing -> error "evalPartial': could not convert back to IExpr"
  ep :: DeferredExpr -> DeferredExpr
  ep = evalPartial

evalPartialUnsized :: Set Integer -> InputSizingExpr -> SizedRecursion
evalPartialUnsized zeroes = cata gatherLimits . transformNoDefer step where
  unsizedTest = unsizedTestIndexed zeroes (unsizedTestDeferred (\_ x -> error ("evalPartialUnsized unsizedTest unhandled:\n" <> prettyPrint x)))
  step = deferStep (basicStep (stuckStep (deferredEvalStep' (indexedInputStep zeroes (abortStep (abortDeferredStep (unsizedStep 255 unsizedTest step wrapUnknownStep)))))))
  -- dof id =  debugTrace ("doing function " <> show id)
  dof _ =  id
  deferStep handleOther = \case
    StuckFW (DeferSF id x) -> dof id deferB (fromEnum id) . cata removeBarriers $ transformNoDefer (step . addBarrier) x
    x -> handleOther x
  addBarrier = \case
    BasicFW EnvSF -> embedD $ BarrierF envB
    x -> x
  removeBarriers = \case
    DeferredFW (BarrierF x) -> x
    x -> embed x
  -- wrapUnknownStep = deferredEE . BarrierF . embed . (\x -> debugTrace ("unknown dump:\n" <> prettyPrint x) x)
  wrapUnknownStep = deferredEE . BarrierF . embed
  gatherLimits = \case
    UnsizedFW (RecursionTestF ri x) -> SizedRecursion $ Map.singleton ri Nothing
    UnsizedFW (SizeStageF sm x) -> sm <> x
    x -> Data.Foldable.fold x

-- >>> 4 + 5
-- 9

fullyResolve :: (Int -> Maybe PartialType) -> PartialType -> PartialType
fullyResolve resolve = convert where
    convert = transform endo
    endo = \case
      TypeVariable anno i -> case resolve i of
        Nothing -> TypeVariable anno i
        Just t  -> convert t
      x -> x

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

partiallyAnnotate :: (Base g ~ f, Annotatable1 f, Annotatable g)
  => g -> Either TypeCheckError (PartialType, Int -> Maybe PartialType)
partiallyAnnotate term =
  let runner :: State (PartialType, Set TypeAssociation, Int) (Either TypeCheckError PartialType)
      runner = runExceptT $ anno term
      initState = (TypeVariable DummyLoc 0, Set.empty, 0)
      (rt, (_, s, _)) = State.runState runner initState
  in (,) <$> rt <*> (flip Map.lookup <$> buildTypeMap s)

annotateTree :: forall g f. (Base g ~ f, Traversable f, Annotatable1 f, Recursive g, Annotatable g)
  => g -> Either TypeCheckError (Cofree f PartialType)
annotateTree term = do
  (rt, resolver) <- partiallyAnnotate term
  let fResolve = fullyResolve resolver
      ca x = anno1 x >>= \a -> pure (fResolve a :< x)
      f = ca <=< sequence
      initState = (TypeVariable DummyLoc 0, Set.empty, 0)
  flip State.evalState initState . runExceptT $ cata f term

matchType :: PartialType -> PartialType -> Bool
matchType a b = case (a,b) of
  (ZeroTypeP, ZeroTypeP)         -> True
  (AnyType, _)                   -> True
  (_, AnyType)                   -> True
  (TypeVariable _ _, _)          -> True
  (_, TypeVariable _ _)          -> True
  (ArrTypeP a b, ArrTypeP c d)   -> matchType a c && matchType b d
  (PairTypeP a b, PairTypeP c d) -> matchType a c && matchType b d
  _                              -> False

matchTypeHead :: (Annotatable1 f, Annotatable g) => PartialType -> f g -> Bool
matchTypeHead t x =
  let initState = (TypeVariable DummyLoc 0, Set.empty, 0)
  in case State.evalState (runExceptT $ anno1 x) initState of
    Left _   -> False
    Right t' -> matchType t' t

instance Validity a => Validity (PartExprF a)
instance Validity a => Validity (StuckF a)
instance Validity a => Validity (SuperPositionF a)
instance Validity a => Validity (AbortableF a)
instance Validity a => Validity (UnsizedRecursionF a)
instance Validity a => Validity (IndexedInputF a)
instance Validity a => Validity (UnsizedExprF a)
instance Validity (Cofree UnsizedExprF PartialType) where
  validate x = let startVar = succ . getMax $ cata mv x
                   mv (a CofreeT.:< x) = mv' a <> Data.Foldable.fold x
                   mv' = \case
                     TypeVariable _ n -> Max n
                     ArrTypeP a b -> mv' a <> mv' b
                     PairTypeP a b -> mv' a <> mv' b
                     _ -> Max 0
                   initState = (TypeVariable DummyLoc startVar, Set.empty, startVar)
                   etb = \case
                     Right True -> True
                     _ -> False
                   getTypeLevel = flip State.evalState initState . runExceptT . liftAnno anno
                   matchLevel (a CofreeT.:< fx) = All (etb $ matchType a <$> getTypeLevel (fst <$> fx))
                     <> Data.Foldable.fold (snd <$> fx)
               in declare "grammar matches type annotations" . getAll $ para matchLevel x

instance GenValid a => GenValid (PartExprF a) where
instance GenValid FunctionIndex
instance GenValid a => GenValid (StuckF a) where
instance GenValid a => GenValid (SuperPositionF a) where
instance GenValid a => GenValid (AbortableF a) where
instance GenValid UnsizedRecursionToken
instance GenValid SizedRecursion where
instance GenValid a => GenValid (UnsizedRecursionF a) where
instance GenValid a => GenValid (IndexedInputF a) where
instance GenValid a => GenValid (UnsizedExprF a) where

class GenValidAdj g where
  type Gennable g
  toGennable :: g -> Gennable g
  fromGennable :: Gennable g -> g

instance GenValid (Cofree UnsizedExprF PartialType) where
  genValid = genValid >>= (sized . genTypedTree Nothing . toPartialType)
  shrinkValid (a :< x) = (a :<) <$> filter (matchTypeHead a) (shrinkValidStructurally x)

instance GenValidAdj UnsizedExpr where
  type Gennable UnsizedExpr = Cofree UnsizedExprF PartialType
  toGennable x = case annotateTree x of
    Left z -> error ("UnsizedExpr toGennable mistyped expression: " <> show z <> "\nfrom\n" <> ppax) where
      annoTerm :: UnsizedExpr -> Either TypeCheckError (Gennable UnsizedExpr)
      annoTerm term = do
        (rt, resolver) <- partiallyAnnotate term
        let ca x = anno1 x >>= \a -> pure (resolve a :< x)
            resolve = \case
              t@(TypeVariable _ i) -> (fromMaybe t (resolver i))
            f = ca <=< sequence
            initState = (TypeVariable DummyLoc 0, Set.empty, 0)
        flip State.evalState initState . runExceptT $ cata f term
      ppax = case annoTerm x of
        Left z   -> "toGennable ppax bad: " <> show z
        Right x' -> prettyPrint x
    Right x -> x
  fromGennable x = cata f x where
    f (_ CofreeT.:< x) = embed x


genTypedTree :: Maybe PartialType -> PartialType -> Int -> Gen (Cofree UnsizedExprF PartialType)
genTypedTree ti t i = -- TODO generate UnsizedF sections?
  let optionEnv = if ti == Just t
                  then (pure (t :< embedB EnvSF) :)
                  else id
      optionGate = case t of
        ArrTypeP ZeroTypeP to -> ((ta . embedB <$> (GateSF <$> genTypedTree ti to half <*> genTypedTree ti to half)) : )
        _ -> id
      optionAbort = case t of
        ArrTypeP ZeroTypeP (ArrTypeP _ _) -> ((pure . ta $ embedA AbortF) : )
        _                                 -> id
      ta = (t :<)
      half = div i 2
      setEnvOption = genValid >>= makeSetEnv where
        makeSetEnv ti' = ta . embedB . SetEnvSF <$> genTypedTree ti (PairTypeP (ArrTypeP ti' t) ti') (i - 1)
      leftOption = genValid >>= makeLeft where
        makeLeft ti' = ta . embedB . LeftSF <$> genTypedTree ti (PairTypeP t ti') (i - 1)
      rightOption = genValid >>= makeRight where
        makeRight ti' = ta . embedB . RightSF <$> genTypedTree ti (PairTypeP ti' t) (i - 1)
      eitherOption = ta . embedP <$> (EitherPF <$> genValid <*> genTypedTree ti t half <*> genTypedTree ti t half)
      abortedOption = pure . ta . embedA . AbortedF . AbortUser $ s2g "Arbitrary Test Data"
      addZeroPair = if t == ZeroTypeP
        then ((ta . embedB <$> (PairSF <$> genTypedTree ti ZeroTypeP half <*> genTypedTree ti ZeroTypeP half)) :)
        else id
      addBranches l = if i < 2 then l else leftOption : rightOption : setEnvOption : eitherOption : addZeroPair l
  in oneof . optionEnv . (abortedOption :) . addBranches $ case t of
    PairTypeP tl tr ->
      [ ta . embedB <$> (PairSF <$> genTypedTree ti tl half <*> genTypedTree ti tr half)
      ]
    ArrTypeP ti' to -> optionGate . optionAbort $
      [ ta . embedS . DeferSF (toEnum 0) <$> genTypedTree ti to (i - 1)
      ]
    _ ->
      [ pure . ta $ embedB ZeroSF
      , ta . embedI . IVarF <$> arbitrary
      , pure . ta $ embedI AnyF
      ]

tcAnnotatedProp :: Cofree UnsizedExprF PartialType -> Bool
tcAnnotatedProp exp = validate . pa $ cata f exp where
  pa :: UnsizedExpr -> Either TypeCheckError (PartialType, Int -> Maybe PartialType)
  pa = partiallyAnnotate
  f (_ CofreeT.:< x) = embed x
  validate = \case
    Right _ -> True
    _ -> False
