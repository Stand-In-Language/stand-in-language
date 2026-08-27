{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

-- |The shared small-step abstract machine: composable step algebras over
-- any IR built from the base functors. Each @*Step@ handles one functor
-- (basic pairs, stuck/defer forms, aborts, superpositions, indexed
-- inputs, unsized-recursion markers) and defers the rest to the next
-- handler, so the sizing pass, the reference evaluator and the partial
-- evaluators all assemble their interpreters from the same parts.
module Telomare.Machine where

import Control.Applicative
import Control.Monad
import Data.Functor.Foldable
import qualified Data.Map.Strict as Map
-- import Data.SBV ((.<), (.>))
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace
import Telomare.IR.Base
import Telomare.PrettyPrint
import Telomare.Size.IR

debug :: Bool
debug = False

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

basicStep :: (Base g ~ f, BasicBase f, Corecursive g, Recursive g) => (f g -> g) -> f g -> g
basicStep handleOther = \case
  -- stuck values
  x@(BasicFW ZeroSF)                       -> embed x
  x@(BasicFW (PairSF _ _))                 -> embed x
  x                                        -> handleOther x

{-# INLINABLE basicStepM #-}
basicStepM :: (Base g ~ f, BasicBase f, Traversable f, Corecursive g, Recursive g, PrettyPrintable g, Monad m) => (f g -> m g) -> f g -> m g
basicStepM handleOther x = f x where
  f = \case
    -- stuck values
    x'@(BasicFW ZeroSF)                      -> pure $ embed x'
    x'@(BasicFW (PairSF _ _))                -> pure $ embed x'

    _                                        -> handleOther x

transformNoDefer :: (Base g ~ f, StuckBase f, Recursive g) => (f g -> g) -> g -> g
transformNoDefer f = c where
  c = f . c' . project
  c' = \case
    s@(StuckFW (DeferSF _ _)) -> s
    x                         -> fmap c x

{-# INLINABLE transformNoDeferM #-}
transformNoDeferM :: (Base g ~ f, StuckBase f, Traversable f, Monad m, Recursive g) => (f g -> m g) -> g -> m g
transformNoDeferM f = c where
  c = f <=< (c' . project)
  c' = \case
    s@(StuckFW (DeferSF _ _)) -> pure s
    x                         -> mapM c x

doLeft :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
doLeft = deferB leftGateInd $ LeftB EnvB

doRight :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
doRight = deferB rightGateInd $ RightB EnvB

-- | matches the branch-selector functions a gate evaluates to (doLeft/doRight)
isGateSelector :: (Base g ~ f, StuckBase f, Recursive g) => g -> Bool
isGateSelector x = case project x of
  StuckFW (DeferSF fi _) -> fi == toEnum leftGateInd || fi == toEnum rightGateInd
  _ -> False

stuckStep :: (Base a ~ f, StuckBase f, BasicBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
stuckStep handleOther = \case
  ff@(FillFunction (StuckEE (DeferSF _fid d)) e) -> db $ transformNoDefer (basicStep (stuckStep handleOther) . replaceEnv) d where
    e' = project e
    db = if False -- fid == toEnum 74
      then debugTrace ("stuckstep dumping output:\n" <> prettyPrint (embed ff))
      -- then debugTrace ("function " <> show fid)
      else id
    replaceEnv = \case
      StuckFW EnvSF -> e'
      x             -> x
  StuckFW (LeftSF z@(BasicEE ZeroSF))      -> z
  StuckFW (LeftSF (BasicEE (PairSF l _)))  -> l
  StuckFW (RightSF z@(BasicEE ZeroSF))     -> z
  StuckFW (RightSF (BasicEE (PairSF _ r))) -> r
  FillFunction GateB ZeroB                 -> doLeft
  FillFunction GateB (PairB _ _)           -> doRight
  -- stuck values
  x@(StuckFW (DeferSF _ _)) -> embed x
  x@(StuckFW GateSF )                 -> embed x
  x -> handleOther x


{-# INLINABLE stuckStepM #-}
stuckStepM :: (Base a ~ f, Traversable f, StuckBase f, BasicBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (f a -> m a) -> f a -> m a
stuckStepM handleOther x = f x where
  f = \case
    FillFunction (StuckEE (DeferSF _fid d)) e -> transformNoDeferM runStuck d where
      runStuck = basicStepM (stuckStepM handleOther) . replaceEnv
      e' = project e
      replaceEnv = \case
        StuckFW EnvSF -> e'
        x'            -> x'
    StuckFW (LeftSF z@(BasicEE ZeroSF))      -> pure z
    StuckFW (LeftSF (BasicEE (PairSF l _)))  -> pure l
    StuckFW (RightSF z@(BasicEE ZeroSF))     -> pure z
    StuckFW (RightSF (BasicEE (PairSF _ r))) -> pure r
    FillFunction GateB ZeroB                 -> pure doLeft
    FillFunction GateB (PairB _ _)           -> pure doRight
    -- stuck value
    x'@(StuckFW (DeferSF _ _)) -> pure $ embed x'
    x'@(StuckFW GateSF)                 -> pure $ embed x'
    _ -> handleOther x



{-# INLINABLE gateBasicResult #-}
gateBasicResult :: (Base g ~ f, BasicBase f, Recursive g, Corecursive g) => (g -> GateResult g) -> g -> GateResult g
gateBasicResult handleOther = \case
  BasicEE ZeroSF -> GateResult True False Nothing
  BasicEE (PairSF _ _) -> GateResult False True Nothing
  x -> handleOther x

{-# INLINABLE gateSuperResult #-}
gateSuperResult :: (Base g ~ f, SuperBase f, Recursive g, Corecursive g) => (g -> GateResult g) -> (g -> GateResult g) -> g -> GateResult g
gateSuperResult step handleOther = \case
  SuperEE (EitherPF n a b) -> let GateResult la ra ba = step a
                                  GateResult lb rb bb = step b
                                  co = case (ba, bb) of
                                    (Just ba', Just bb') -> pure . superEE $ EitherPF n ba' bb'
                                    _ -> ba <|> bb
                              in GateResult (la || lb) (ra || rb) co
  x -> handleOther x

{-# INLINABLE gateAbortResult #-}
gateAbortResult :: (Base g ~ f, AbortBase f, Recursive g, Corecursive g) => (g -> GateResult g) -> g -> GateResult g
gateAbortResult handleOther = \case
  a@(AbortEE (AbortedF _)) -> GateResult False False $ Just a
  x -> handleOther x

{-# INLINABLE gateIndexedResult #-}
gateIndexedResult :: (Base g ~ f, IndexedInputBase f, Recursive g, Corecursive g) => (g -> GateResult g) -> g -> GateResult g
gateIndexedResult handleOther = \case
  -- IndexedEE (IVarF n) -> GateResult True False Nothing -- wait, why lb but no rb?
  IndexedEE (IVarF _n) -> GateResult True True Nothing
  x -> handleOther x

{-# INLINABLE mergeShallow #-}
mergeShallow :: (Base g ~ f, SuperBase f, ShallowEq1 f, Recursive g, Corecursive g, PrettyPrintable g) => Maybe Integer -> g -> g -> g
mergeShallow n a b = if shallowEq1 (project a) (project b)
  then debugTrace ("mergeShallow found same pair\n" <> prettyPrint a <> "\nand\n" <> prettyPrint b) a
  else superEE $ EitherPF n a b

{-# INLINABLE foldGateResult #-}
foldGateResult :: forall g f. (Base g ~ f, SuperBase f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => Maybe Integer -> GateResult g -> g
foldGateResult n (GateResult doL doR o) =
  let branchPart = case (doL, doR) of
        (True, True) -> pure . superEE $ EitherPF n doLeft doRight
        (True, _)    -> pure doLeft
        (_, True)    -> pure doRight
        _            -> Nothing
  in case (o, branchPart) of
    (Just o', Just bp) -> superEE $ EitherPF Nothing o' bp
    (Just x, _)        -> x
    (_, Just x)        -> x
    _                  -> error "foldGateResult: no results"

superStep :: forall a f. (Base a ~ f, BasicBase f, StuckBase f, SuperBase f, ShallowEq1 f, Recursive a, Corecursive a, PrettyPrintable a)
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
    StuckFW (LeftSF (SuperEE (EitherPF n a b))) -> mergeShallow n (step . embedS . LeftSF $ a) (step . embedS . LeftSF $ b)
    StuckFW (RightSF (SuperEE (EitherPF n a b))) -> mergeShallow n (step . embedS . RightSF $ a) (step . embedS . RightSF $ b)
    StuckFW (SetEnvSF (SuperEE (EitherPF n a b))) -> mergeShallow n (step . embedS . SetEnvSF $ a) (step . embedS . SetEnvSF $ b)
    FillFunction GateB x@(SuperEE (EitherPF n _ _)) -> foldGateResult n $ gateResult x
    FillFunction (SuperEE (EitherPF n sca scb)) e | isGateSelector sca && isGateSelector scb -> mergeShallow n
      (step . embedS . SetEnvSF . BasicEE $ PairSF sca e)
      (step . embedS . SetEnvSF . BasicEE $ PairSF scb e)
    (FillFunction (SuperEE (EitherPF n sca scb)) e) -> mergeShallow n
      (step . embedS . SetEnvSF . BasicEE . PairSF sca $ if null n then e else cata (filterLeft n) e)
      (step . embedS . SetEnvSF . BasicEE . PairSF scb $ if null n then e else cata (filterRight n) e)
    -- stuck values
    x@(SuperFW (EitherPF _ _ _)) -> embed x
    x -> handleOther x

{-# INLINABLE superStepM #-}
superStepM :: forall a f m. (Base a ~ f, Traversable f, BasicBase f, StuckBase f, SuperBase f, ShallowEq1 f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (a -> GateResult a) -> (f a -> m a) -> (f a -> m a) -> f a -> m a
superStepM gateResult step handleOther x = f x where
  pbStep bf = step . embedS . bf
  filterLeft :: Maybe Integer -> f a -> a
  filterLeft n = \case
        _s@(SuperFW (EitherPF nt a _)) | (decendant <$> nt <*> n) == Just True -> a
        x' -> embed x'
  filterRight :: Maybe Integer -> f a -> a
  filterRight n = \case
        _s@(SuperFW (EitherPF nt _ b)) | (decendant <$> n <*> nt) == Just True -> b
        x' -> embed x'
  f = \case
    StuckFW (LeftSF (SuperEE (EitherPF n a b))) ->  mergeShallow n <$> pbStep LeftSF a <*> pbStep LeftSF b
    StuckFW (RightSF (SuperEE (EitherPF n a b))) ->  mergeShallow n <$> pbStep RightSF a <*> pbStep RightSF b
    StuckFW (SetEnvSF (SuperEE (EitherPF n a b))) -> mergeShallow n <$> pbStep SetEnvSF a <*> pbStep SetEnvSF b
    FillFunction GateB x'@(SuperEE (EitherPF n _ _)) -> pure . foldGateResult n $ gateResult x'
    FillFunction (SuperEE (EitherPF n sca scb)) e ->
      let fl = if null n || isGateSelector sca then id else cata (filterLeft n)
          fr = if null n || isGateSelector scb then id else cata (filterRight n)
      in mergeShallow n
       <$> (pbStep SetEnvSF . BasicEE . PairSF sca $ fl e)
       <*> (pbStep SetEnvSF . BasicEE . PairSF scb $ fr e)
    -- stuck values
    x'@(SuperFW (EitherPF _ _ _)) -> pure $ embed x'

    _ -> handleOther x

superAbortStep :: (Base g ~ f, Traversable f, BasicBase f, StuckBase f, SuperBase f, AbortBase f, ShallowEq1 f, Recursive g, Corecursive g, PrettyPrintable g)
  => (f g -> g) -> (f g -> g) -> f g -> g
superAbortStep step handleOther x = f x where
  pbStep bf = step . bf
  f = \case
    FillFunction (AbortEE AbortF) (SuperEE (EitherPF n a b)) ->
      mergeShallow n (pbStep (FillFunction (AbortEE AbortF)) a) (pbStep (FillFunction (AbortEE AbortF)) b)
    _ -> handleOther x

{-# INLINABLE superAbortStepM #-}
superAbortStepM :: (Base g ~ f, Traversable f, BasicBase f, StuckBase f, SuperBase f, AbortBase f, ShallowEq1 f, Recursive g, Corecursive g, PrettyPrintable g, Monad m)
  => (f g -> m g) -> (f g -> m g) -> f g -> m g
superAbortStepM step handleOther x = f x where
  pbStep bf = step . bf
  f = \case
    FillFunction (AbortEE AbortF) (SuperEE (EitherPF n a b)) ->
      liftM2 (mergeShallow n) (pbStep (FillFunction (AbortEE AbortF)) a) (pbStep (FillFunction (AbortEE AbortF)) b)
    _ -> handleOther x

indexedAbortStep :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, AbortBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
indexedAbortStep handleOther = \case
  FillFunction (AbortEE AbortF) (IndexedEE (IVarF _n)) -> AbortEE $ AbortedF AbortAny
  x -> handleOther x

{-# INLINABLE indexedAbortStepM #-}
indexedAbortStepM :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, AbortBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (f a -> m a) -> f a -> m a
indexedAbortStepM handleOther = \case
  FillFunction (AbortEE AbortF) (IndexedEE (IVarF _n)) -> pure . AbortEE $ AbortedF AbortAny
  x -> handleOther x

indexedSuperStep :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, SuperBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
indexedSuperStep handleOther = \case
  FillFunction GateB (IndexedEE (IVarF n)) -> superEE $ EitherPF (pure n) doLeft doRight
  x -> handleOther x

{-# INLINABLE indexedSuperStepM #-}
indexedSuperStepM :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, SuperBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => (f a -> m a) -> f a -> m a
indexedSuperStepM handleOther = \case
  FillFunction GateB (IndexedEE (IVarF n)) -> pure . superEE $ EitherPF (pure n) doLeft doRight

  x -> handleOther x

abortStep :: (Base a ~ f, BasicBase f, StuckBase f, AbortBase f, Recursive a, Corecursive a, PrettyPrintable a) => (f a -> a) -> f a -> a
abortStep handleOther =
  \case
    StuckFW (LeftSF a@(AbortEE (AbortedF _))) -> a
    StuckFW (RightSF a@(AbortEE (AbortedF _))) -> a
    StuckFW (SetEnvSF a@(AbortEE (AbortedF _))) -> a
    FillFunction a@(AbortEE (AbortedF _)) _ -> a
    FillFunction GateB a@(AbortEE (AbortedF _)) -> a
    FillFunction (AbortEE AbortF) a@(AbortEE (AbortedF _)) -> a
    FillFunction (AbortEE AbortF) (BasicEE ZeroSF) -> deferB abortInd . StuckEE $ EnvSF
    FillFunction (AbortEE AbortF) e@(BasicEE (PairSF _ _)) -> (\x -> debugTrace ("aborted with value: " <> prettyPrint x) x) . AbortEE $ AbortedF m where
      m = cata truncF e
      truncF = \case
        BasicFW ZeroSF       -> ZeroB
        BasicFW (PairSF a b) -> PairB a b
        _                    -> ZeroB -- consider generating a warning?
    -- stuck values
    x@(AbortFW (AbortedF _)) -> embed x
    x@(AbortFW AbortF) -> embed x
    x -> handleOther x

{-# INLINABLE abortStepM #-}
abortStepM :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, AbortBase f, Recursive a, Corecursive a, Monad m)
  => (f a -> m a) -> f a -> m a
abortStepM handleOther x = f x where
  f = \case
    StuckFW (LeftSF a@(AbortEE (AbortedF _))) -> pure a
    StuckFW (RightSF a@(AbortEE (AbortedF _))) -> pure a
    StuckFW (SetEnvSF a@(AbortEE (AbortedF _))) -> pure a
    FillFunction a@(AbortEE (AbortedF _)) _ -> pure a
    FillFunction GateB a@(AbortEE (AbortedF _)) -> pure a
    FillFunction (AbortEE AbortF) a@(AbortEE (AbortedF _)) -> pure a
    FillFunction (AbortEE AbortF) (BasicEE ZeroSF) -> pure . deferB abortInd . StuckEE $ EnvSF
    FillFunction (AbortEE AbortF) e@(BasicEE (PairSF _ _)) -> pure . AbortEE $ AbortedF m where
      m = cata truncF e
      truncF = \case
        BasicFW ZeroSF       -> ZeroB
        BasicFW (PairSF a b) -> PairB a b
        _                    -> ZeroB -- consider generating a warning?
    -- stuck values
    x'@(AbortFW (AbortedF _)) -> pure $ embed x'
    x'@(AbortFW AbortF) -> pure $ embed x'
    _ -> handleOther x

-- list of defer indexes for functions generated during eval. Need to be unique (grammar under defer n should always be the same)
twiddleInd, leftGateInd, rightGateInd, unsizedStepMEInd, unsizedStepMTInd, unsizedStepMa, unsizedStepMrfa, unsizedStepMrfb, unsizedStepMw, removeRefinementWrappersTC, abortInd :: Int
twiddleInd = -1
leftGateInd = -2
rightGateInd = -3
unsizedStepMEInd = -4
unsizedStepMTInd = -5
unsizedStepMa = -6
unsizedStepMrfa = -7
unsizedStepMrfb = -8
unsizedStepMw = -9
removeRefinementWrappersTC = -10
abortInd = -11

deferB :: (Base g ~ f, StuckBase f, Recursive g, Corecursive g) => Int -> g -> g
deferB n = StuckEE . DeferSF (toEnum n)

lamB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => Int -> g -> g
lamB n x = PairB (deferB n x) EnvB

twiddleB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
twiddleB = deferB twiddleInd $ PairB (LeftB (RightB EnvB)) (PairB (LeftB EnvB) (RightB (RightB EnvB)))

appB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> g -> g
appB c i = SetEnvB (SetEnvB (PairB twiddleB (PairB i c)))

-- only intended for use inside of unsizedStep
iteB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> g -> g -> g
iteB i t e = FillFunctionEE (FillFunctionEE (FillFunctionEE GateB i) (PairB (deferB unsizedStepMEInd e) (deferB unsizedStepMTInd t))) EnvB -- TODO THIS IS HOW TO DO LAZY IF/ELSE, COPY!

argOneB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
argOneB = LeftB EnvB
argTwoB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
argTwoB = LeftB (RightB EnvB)
argThreeB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
argThreeB = LeftB (RightB (RightB EnvB))
argFourB :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g
argFourB = LeftB (RightB (RightB (RightB EnvB)))

unsizedTestIndexed :: (Base g ~ f, BasicBase f, AbortBase f, IndexedInputBase f, Recursive g, Corecursive g)
  => Set Integer -> (UnsizedRecursionToken -> g -> g) -> UnsizedRecursionToken -> g -> g
unsizedTestIndexed zeroes handleOther ri = \case
  iv@(IndexedEE (IVarF n)) -> debugTrace ("evalRecursionTest ivar " <> show n) $ if isUnbounded zeroes n
    then debugTrace ("evalRecursion punted to abort on " <> show n) AbortEE . AbortedF . AbortUnsizeable . i2B . fromEnum $ ri
    else if Set.member n zeroes
    then debugTrace ("unsizedTestIndexed resolved to zero for var " <> show n) ZeroB
    else iv
  x -> handleOther ri x

unsizedTestSuper :: (Base g ~ f, SuperBase f, AbortBase f, Recursive g, Corecursive g, PrettyPrintable g)
  => (g -> g) -> (UnsizedRecursionToken -> g -> g) -> UnsizedRecursionToken -> g -> g
unsizedTestSuper reTest handleOther ri = \case
  SuperEE (EitherPF n a b) -> let getAU = \case
                                    a'@(AbortEE (AbortedF (AbortUnsizeable _))) -> Just a'
                                    _ -> Nothing
                                  na = reTest a
                                  nb = reTest b
                                  r = case getAU na <|> getAU nb <|> (Just . superEE $ EitherPF n na nb) of
                                    Just r' -> r'
                                    Nothing -> error "Telomare.Machine.unsizedTestSuper: unexpected Nothing"
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
unsizedStep _maxSize recursionTest fullStep handleOther =
  let combineSizes :: SizedRecursion -> a -> a
      combineSizes sm = \case
        UnsizedEE (SizeStageF smb x) -> unsizedEE $ SizeStageF (smb <> sm) x
        x -> unsizedEE $ SizeStageF sm x
  in \case
    UnsizedFW (SizeStepStubF tok n (BasicEE (PairSF _ e))) ->
      PairB (deferB unsizedStepMrfa (unsizedEE . SizeStageF (SizedRecursion . Map.singleton tok $ pure (n + 1)) $ iteB (appB argFourB argOneB)
                                                (appB (appB argThreeB (unsizedEE $ SizeStepStubF tok (n + 1) EnvB)) argOneB)
                                                (appB argTwoB argOneB))) e
    UnsizedFW (RecursionTestF ri x) -> recursionTest ri x
    StuckFW (LeftSF (UnsizedEE (SizeStageF sm x))) -> combineSizes sm . fullStep . embedS $ LeftSF x
    StuckFW (RightSF (UnsizedEE (SizeStageF sm x))) -> combineSizes sm . fullStep . embedS $ RightSF x
    StuckFW (SetEnvSF (UnsizedEE (SizeStageF sm x))) -> combineSizes sm . fullStep . embedS $ SetEnvSF x
    FillFunction (UnsizedEE (SizeStageF sm x)) e -> combineSizes sm . fullStep $ FillFunction x e
    FillFunction GateB (UnsizedEE (SizeStageF sm x)) -> combineSizes sm . fullStep $ FillFunction GateB x
    -- stuck value
    ss@(UnsizedFW (SizeStageF _ _)) -> embed ss
    t@(UnsizedFW (RecursionTestF _ _)) -> embed t
    x -> handleOther x

{-# INLINABLE unsizedStepM''' #-}
unsizedStepM''' :: forall a f m. (Base a ~ f, Traversable f, BasicBase f, StuckBase f, AbortBase f, UnsizedBase f, Recursive a, Corecursive a
                                   , Eq a, PrettyPrintable a, m ~ StrictAccum SizedRecursion)
  => Int -> Set Integer -> (UnsizedRecursionToken -> a -> a) -> (f a -> m a) -> f a -> m a
unsizedStepM''' maxSize _zeros recursionTest handleOther x = f x where
  argOne = LeftB EnvB
  argTwo = LeftB (RightB EnvB)
  argThree = LeftB (RightB (RightB EnvB))
  argFour = LeftB (RightB (RightB (RightB EnvB)))
  f = \case
    UnsizedFW (UnsizedStubF tok (BasicEE (PairSF _ (BasicEE (PairSF _ (BasicEE (PairSF _ (BasicEE (PairSF _ env))))))))) -> case env of
      BasicEE (PairSF b (BasicEE (PairSF r (BasicEE (PairSF tp (BasicEE ZeroSF)))))) -> case tp of
        BasicEE (PairSF (StuckEE (DeferSF sid tf)) e) ->
          let nt = PairB (StuckEE . DeferSF sid . unsizedEE $ RecursionTestF tok tf) e
              trb = PairB b (PairB r (PairB nt ZeroB))
              dbti = id
              -- \t r b i ->
              rf = deferB unsizedStepMrfa (iteB (dbti $ appB argFour argOne)
                                          (appB (appB argThree (unsizedEE $ SizeStepStubF tok 1 EnvB)) argOne)
                                          (unsizedEE . SizeStageF (SizedRecursion . Map.singleton tok $ pure 1) $ appB argTwo argOne))
              result = PairB ZeroB (PairB ZeroB (PairB ZeroB (PairB (PairB rf trb) ZeroB)))
          in pure result
        _ -> error "Telomare.Machine.unsizedStepM''': unexpected test pair"
      _ -> error "Telomare.Machine.unsizedStepM''': unexpected env"
    -- The payload names the recursion that ran out of budget, matching the
    -- runtime `AbortRecursion` built by `repeaterAndAbort`. The depth reached
    -- is always `maxSize + 1`, so the caller reconstructs it from its settings.
    UnsizedFW (SizeStepStubF tok n _) | n > maxSize -> pure . AbortEE . AbortedF . AbortRecursion . i2B $ fromEnum tok
    UnsizedFW (SizeStepStubF tok n e@(BasicEE (PairSF _ es))) ->
      let dbti = id
      in pure $ PairB (deferB unsizedStepMrfa (iteB (dbti $ appB argFour argOne)
                                                (appB (appB argThree (unsizedEE $ SizeStepStubF tok (n + 1) e)) argOne)
                                                (unsizedEE . SizeStageF (SizedRecursion . Map.singleton tok $ pure (n + 1)) $ appB argTwo argOne))) es
    UnsizedFW (RecursionTestF ri x') -> pure . recursionTest ri $ x'
    UnsizedFW (SizeStageF sr x') -> debugTrace ("Hit SizeStage: " <> show sr) $ StrictAccum sr x'
    UnsizedFW (TraceF s x') -> pure $ debugTrace ("Hit TraceF: " <> s <> "\n" <> prettyPrint x') x'
    _ -> handleOther x

zeroedInputStepM :: (Base a ~ g, Traversable f, IndexedInputBase f, BasicBase g, Recursive a, Corecursive a, Monad m)
  => Set Integer -> (f a -> m a) -> f a -> m a
zeroedInputStepM zeros handleOther = f where
  f = \case
    IndexedFW (IVarF n) | Set.member n zeros -> pure $ BasicEE ZeroSF
    x -> handleOther x

indexedInputStep :: (Base a ~ f, BasicBase f, StuckBase f, IndexedInputBase f, Recursive a, Corecursive a) => Set Integer -> (f a -> a) -> f a -> a
indexedInputStep zeroes handleOther =
  let res n = if Set.member n zeroes then ZeroB else indexedEE $ IVarF n
  in \case
  StuckFW (LeftSF (IndexedEE (IVarF n))) -> res $ n * 2 + 1
  StuckFW (RightSF (IndexedEE (IVarF n))) -> res $ n * 2 + 2
  StuckFW (LeftSF (IndexedEE AnyF)) -> indexedEE AnyF
  StuckFW (RightSF (IndexedEE AnyF)) -> indexedEE AnyF
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

indexedInputStep' :: (Base a ~ f, BasicBase f, StuckBase f, IndexedInputBase f, Recursive a, Corecursive a) => Set Integer -> (f a -> a) -> f a -> a
indexedInputStep' zeroes handleOther =
  let res n = if Set.member n zeroes then ZeroB else indexedEE $ IVarF n
  in \case
  StuckFW (LeftSF (IndexedEE (IVarF n))) -> res $ n * 2 + 1
  StuckFW (RightSF (IndexedEE (IVarF n))) -> res $ n * 2 + 2
  StuckFW (LeftSF (IndexedEE AnyF)) -> indexedEE AnyF
  StuckFW (RightSF (IndexedEE AnyF)) -> indexedEE AnyF
  IndexedFW (IVarF n) -> res n
  -- stuck values
  i@(IndexedFW _) -> embed i

  x -> handleOther x

indexAbortIfUnboundStep :: (Base a ~ f, BasicBase f, StuckBase f, AbortBase f, IndexedInputBase f, Recursive a, Corecursive a, Show a)
  => Set Integer -> (f a -> a) -> f a -> a
indexAbortIfUnboundStep zeroes handleOther =
  let res _s n = case (Set.member n zeroes, isUnbounded zeroes n) of
        (True, _) -> ZeroB
        (_, True) -> AbortEE $ AbortedF AbortAny
        _ -> PairB (indexedEE . IVarF $ n * 2 + 1) (indexedEE . IVarF $ n * 2 + 2)
      leftI = \case
        BasicEE (PairSF l _) -> l
        x -> x
      rightI = \case
        BasicEE (PairSF _ r) -> r
        x -> x
  in \case
  StuckFW (LeftSF (IndexedEE (IVarF n))) -> leftI $ res "left" n
  StuckFW (RightSF (IndexedEE (IVarF n))) -> rightI $ res "right" n
  IndexedFW (IVarF n) -> res "bare" n
  x -> handleOther x

{-# INLINABLE indexedInputStepM #-}
indexedInputStepM :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => Set Integer -> (f a -> m a) -> f a -> m a
indexedInputStepM zeroes handleOther x = f x where
  res n = if Set.member n zeroes then ZeroB else indexedEE $ IVarF n
  f = \case
    StuckFW (LeftSF (IndexedEE (IVarF n))) -> pure . res $ n * 2 + 1
    StuckFW (RightSF (IndexedEE (IVarF n))) -> pure . res $ n * 2 + 2
    StuckFW (LeftSF (IndexedEE AnyF)) -> pure $ indexedEE AnyF
    StuckFW (RightSF (IndexedEE AnyF)) -> pure $ indexedEE AnyF
    StuckFW (SetEnvSF (IndexedEE AnyF)) -> pure $ indexedEE AnyF
    FillFunction (IndexedEE AnyF) _ -> pure $ indexedEE AnyF
    FillFunction GateB (IndexedEE AnyF) -> pure $ indexedEE AnyF
    IndexedFW (IVarF n) -> pure $ res n
    -- stuck values
    i@(IndexedFW _) -> pure $ embed i

    _ -> handleOther x

indexedInputStepM' :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, IndexedInputBase f, Recursive a, Corecursive a, PrettyPrintable a, Monad m)
  => Set Integer -> (f a -> m a) -> f a -> m a
indexedInputStepM' zeroes handleOther x = f x where
  res n = if Set.member n zeroes then ZeroB else indexedEE $ IVarF n
  f = \case
    StuckFW (LeftSF (IndexedEE (IVarF n))) -> pure . res $ n * 2 + 1
    StuckFW (RightSF (IndexedEE (IVarF n))) -> pure . res $ n * 2 + 2
    StuckFW (LeftSF (IndexedEE AnyF)) -> pure $ indexedEE AnyF
    StuckFW (RightSF (IndexedEE AnyF)) -> pure $ indexedEE AnyF
    StuckFW (SetEnvSF (IndexedEE AnyF)) -> pure $ indexedEE AnyF
    FillFunction (IndexedEE AnyF) _ -> pure $ indexedEE AnyF
    FillFunction GateB (IndexedEE AnyF) -> pure $ indexedEE AnyF
    IndexedFW (IVarF n) -> pure $ res n
    -- stuck values
    i@(IndexedFW _) -> pure $ embed i

    _ -> handleOther x

{-# INLINABLE indexedInputIgnoreSwitchStepM #-}
indexedInputIgnoreSwitchStepM :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, IndexedInputBase f, Recursive a, Corecursive a, Monad m)
  => (f a -> m a) -> f a -> m a
indexedInputIgnoreSwitchStepM handleOther x = f x where
  f = \case
    FillFunction GateB (IndexedEE (IVarF _)) -> pure $ indexedEE AnyF
    _ -> handleOther x

indexSwitchSuperSplitStep :: (Base a ~ f, BasicBase f, StuckBase f, IndexedInputBase f, SuperBase f, Recursive a, Corecursive a) => (f a -> a) -> f a -> a
indexSwitchSuperSplitStep handleOther = \case
  FillFunction GateB (IndexedEE AnyF) -> superEE $ EitherPF Nothing doLeft doRight

  x -> handleOther x

deferredEvalStep :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, DeferredEvalBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
deferredEvalStep handleOther = \case
    -- combine
    StuckFW (LeftSF (DeferredEE (BarrierF (DeferredEE (ManyLefts n x))))) -> deferredEE . BarrierF . deferredEE $ ManyLefts (n + 1) x
    StuckFW (RightSF (DeferredEE (BarrierF (DeferredEE (ManyRights n x))))) -> deferredEE . BarrierF . deferredEE $ ManyRights (n + 1) x
    StuckFW (LeftSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . deferredEE $ ManyLefts 1 x
    StuckFW (RightSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . deferredEE $ ManyRights 1 x
    StuckFW (SetEnvSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . StuckEE $ SetEnvSF x
    FillFunction (DeferredEE (BarrierF c)) e -> deferredEE . BarrierF $ FillFunctionEE c e
    FillFunction GateB (DeferredEE (BarrierF s)) -> deferredEE . BarrierF . embed $ FillFunction GateB s
    -- stuck values
    d@(DeferredFW _) -> embed d

    x -> handleOther x

deferredEvalStep' :: (Base a ~ f, Traversable f, BasicBase f, StuckBase f, DeferredEvalBase f, Recursive a, Corecursive a, PrettyPrintable a)
  => (f a -> a) -> f a -> a
deferredEvalStep' handleOther = \case
    StuckFW (LeftSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . StuckEE $ LeftSF x
    StuckFW (RightSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . StuckEE $ RightSF x
    StuckFW (SetEnvSF (DeferredEE (BarrierF x))) -> deferredEE . BarrierF . StuckEE $ SetEnvSF x
    FillFunction (DeferredEE (BarrierF c)) e -> deferredEE . BarrierF $ FillFunctionEE c e
    FillFunction GateB (DeferredEE (BarrierF s)) -> deferredEE . BarrierF . embed $ FillFunction GateB s
    -- stuck values
    d@(DeferredFW _) -> embed d

    x -> handleOther x

abortDeferredStep :: (Base a ~ f, BasicBase f, StuckBase f, AbortBase f, DeferredEvalBase f, Recursive a, Corecursive a)
  => (f a -> a) -> f a -> a
abortDeferredStep handleOther = \case
  FillFunction a@(AbortEE AbortF) (DeferredEE (BarrierF e)) -> deferredEE . BarrierF $ FillFunctionEE a e

  x -> handleOther x

-- is a variable limited in value or unbounded?
isUnbounded :: Set Integer -> Integer -> Bool
isUnbounded s n = f s where
  f s'
    | null s' = True
    | Set.member n s' = False
    | otherwise = (f . Set.map (flip div 2 . pred)) $ Set.filter (>= n) s'


-- NOTE this considers a node to be its own decendant
decendant :: Integer -> Integer -> Bool
decendant x d = case compare x d of
  GT -> decendant (flip div 2 $ pred x) d
  EQ -> True
  LT -> False
