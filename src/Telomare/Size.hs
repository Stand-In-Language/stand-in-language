{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

-- |The sizing pass: telomare's totality checker. 'sizeTermM' abstractly
-- interprets the program over a symbolic input ('initialInput', bounded by
-- the refinement-derived 'InputRestrictions' from 'getInputLimits') and
-- infers, per unsized recursion site, an iteration count that holds for
-- every input - then bakes those counts into the term as church towers.
-- A program that cannot be sized does not compile ('SizingFailure').
module Telomare.Size where

import Control.Applicative
import Control.Comonad.Cofree (Cofree ((:<)), hoistCofree)
import qualified Control.Comonad.Trans.Cofree as CofreeT (CofreeF (..))
import Control.Lens.Plated (transform)
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader (Reader, ReaderT, ask, local, runReaderT)
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.State.Lazy as StateL
import Control.Monad.State.Strict (State, StateT)
import qualified Control.Monad.State.Strict as State
import Control.Monad.Trans.Class
import Data.Bifunctor
import Data.Char (chr)
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
import Control.Comonad.Trans.Cofree (CofreeF, headF)
import Control.Exception (Exception)
import Control.Exception.Base (throw)
import Control.Monad.Reader.Class
import Data.Functor.Identity (Identity (Identity), runIdentity)
import Data.Semigroup (Max (..))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void
import Debug.Trace
import GHC.Generics (Generic)
import Telomare.Error
import Telomare.IR.Base
import Telomare.IR.Builder
import Telomare.IR.Core
import Telomare.IR.Loc
import Telomare.IR.Surface
import Telomare.IR.Types
import Telomare.Machine hiding (debug, debugTrace)
import Telomare.PrettyPrint
import Telomare.PrettyPrint.Indent (indentWithChildren', indentWithOneChild,
                                    indentWithOneChild', indentWithTwoChildren,
                                    indentWithTwoChildren', sindent)
import Telomare.Size.IR

debug :: Bool
debug = False

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

data SizingSettings = SizingSettings
  { maxSizingSize :: Int
  , doCap         :: Bool
  } deriving (Eq, Ord, Show)

data InputRestrictions
  = InputRestrictions {zeroes :: Set Integer, pairs :: Set Integer}
  deriving Show

instance Semigroup InputRestrictions where
  (<>) (InputRestrictions za pa) (InputRestrictions zb pb) = InputRestrictions (za <> zb) (pa <> pb)
instance Monoid InputRestrictions where
  mempty = InputRestrictions mempty mempty

extractInputRestrictions :: InputSizingExpr -> InputRestrictions
extractInputRestrictions = cleanup . f Nothing where
  f expected = f' expected . project
  irIntersection (InputRestrictions za pa) (InputRestrictions zb pb) = InputRestrictions (za <> zb) (pa <> pb)
  f' :: Maybe Bool -> InputSizingExprF InputSizingExpr -> Maybe (StrictAccum InputRestrictions InputSizingExpr)
  f' expected = \case
    z@(BasicFW ZeroSF) -> case expected of
      Just True -> Nothing
      _         -> pure . pure $ embed z
    p@(BasicFW (PairSF _ _)) -> case expected of
      Just False -> Nothing
      _          -> pure . pure $ embed p
    IndexedFW (IVarF n) -> case expected of
      Just False -> Just (StrictAccum (InputRestrictions (Set.singleton n) mempty) ZeroB)
      Just True  -> Just (StrictAccum (InputRestrictions mempty (Set.singleton n)) $ PairB ZeroB ZeroB)
      _          -> Just (StrictAccum mempty ZeroB) -- is this ok?
    FillFunction (AbortEE AbortF) i -> f (Just False) i
    GateSwitch l r s ->
      let nl = f expected l
          nr = f expected r
          pf = \case
            Just (StrictAccum s _) -> s
            _ -> Set.empty
      in case (nl, nr) of
        (Nothing, Nothing) -> debugTrace "extractZeroes gate nothing" Nothing
        (Just (StrictAccum sta x), Just (StrictAccum stb _)) -> debugTrace "extractZeroes gate both" $ case f Nothing s of
          Nothing -> Nothing
          Just (StrictAccum st _) -> pure $ StrictAccum (st <> irIntersection sta stb) x
        (Just (StrictAccum sta x), _) -> case f (Just False) s of
          Nothing                  -> Nothing
          Just (StrictAccum stb _) -> pure $ StrictAccum (sta <> stb) x
        (_, Just (StrictAccum sta x)) -> case f (Just True) s of
          Nothing                  -> Nothing
          Just (StrictAccum stb _) -> pure $ StrictAccum (sta <> stb) x
    _ -> Nothing
  cleanup = \case
    Just (StrictAccum s _) -> s
    _ -> mempty

findInputLimitStepM :: (InputSizingExprF InputSizingExpr -> StrictAccum InputRestrictions InputSizingExpr)
  -> InputSizingExprF InputSizingExpr -> StrictAccum InputRestrictions InputSizingExpr
findInputLimitStepM handleOther x = f x where
  f = \case
    UnsizedFW (RefinementWrapperF lt tc c) ->
      let
          performTC = SetEnvB $ PairB (AbortEE AbortF) (appB tc c)
          wrapDefer = \case
            FillFunction GateB i@(IndexedEE _) -> deferredEE . BarrierF . embed $ FillFunction GateB i
            x -> error $ "findInputLimitStepM eval unexpected:\n" <> prettyPrint x
          evalStep = basicStep (stuckStep (abortStep (deferredEvalStep (abortDeferredStep (indexedInputStep' Set.empty wrapDefer)))))
          convertIL :: InputSizingExpr -> UnsizedExpr
          convertIL = validate . cata f where
            f = convertBasic (convertStuck (convertAbort (convertIndexed convertFail)))
            -- convertFail z = Left ("findInputLimitStepM convert failed on unexpected\n" <> prettyPrint z)
            convertFail z = Left "findInputLimitStepM convert failed on something unexpected"
          validate = \case
            Left e -> error e
            Right x -> x
          ev = transformNoDefer evalStep
          stripBarrier = \case
            DeferredFW (BarrierF x) -> x
            x -> embed x
          s = extractInputRestrictions . cata stripBarrier . transformNoDefer evalStep $ performTC
      in StrictAccum s c
    _ -> handleOther x

unsized2abortExpr :: UnsizedExpr -> CompiledExpr
unsized2abortExpr = validate . cata (convertBasic (convertStuck (convertAbort unexpected))) where
  unexpected x = Left $ "unsized2abortExpr unexpected unsized bit: " <> prettyPrint (fmap (const ' ') x)
  validate = \case
    Left e -> error e
    Right x -> x

term3ToUnsizedExpr :: Term3 -> UnsizedExpr
term3ToUnsizedExpr = runIdentity . cata conv where
  conv :: CofreeT.CofreeF Term3F LocTag (Identity UnsizedExpr) -> Identity UnsizedExpr
  conv = convertBasic (convertStuck (convertAbort convertOther))
  convertOther (_ CofreeT.:< g) = case g of
    Term3Unsized urt -> pure . unsizedEE . UnsizedStubF urt $ EnvB
    Term3CheckingWrapper loc tc c -> unsizedEE <$> (RefinementWrapperF loc <$> tc <*> c)
    z -> error "term3ToUnsizedExpr could not convert"

-- get simple input limits derived from refinements
-- returns a set of guaranteed Zeros, where the Integer is the encoded path from root of intput
getInputLimits :: UnsizedExpr -> InputRestrictions
getInputLimits = getAccum . transformNoDeferM evalStep . convertIS where
  convertU = \case
    UnsizedFW (UnsizedStubF _ _) -> pure $ indexedEE AnyF
    UnsizedFW (RecursionTestF _ x) -> x
    UnsizedFW rw@(RefinementWrapperF _ _ _) -> unsizedEE <$> sequence rw
    x -> error $ "getInputLimits convert, unhandled:\n" <> prettyPrint (runIdentity $ sequence x)
  convertIS :: UnsizedExpr -> InputSizingExpr
  convertIS = runIdentity . cata (convertBasic (convertStuck (convertAbort (convertIndexed convertU))))
  unexpectedI x = error $ "getInputLimits eval, unexpected:\n" <> prettyPrint x
  evalStep = basicStepM (stuckStepM (abortStepM (indexedInputStepM Set.empty (indexedInputIgnoreSwitchStepM (findInputLimitStepM unexpectedI)))))

capMain :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> g -> g
capMain i c = appB c i


isClosure :: (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g) => g -> Bool
isClosure = \case
  BasicEE (PairSF (StuckEE (DeferSF _ _)) _) -> True
  _                                          -> False

newtype UnexpectedGrammarException = UGException String

instance Show UnexpectedGrammarException where
  show (UGException e) = "UnexpectedGrammarException: " <> e

instance Exception UnexpectedGrammarException


initialInput :: (Base a ~ f, BasicBase f, IndexedInputBase f, Recursive a, Corecursive a) => InputRestrictions -> a
initialInput irs = f 0 where
  f n = if any (`decendant` n) $ pairs irs
    then PairB (f $ n * 2 + 1) (f $ n * 2 + 2)
    else indexedEE $ IVarF n

-- |Size every recursion site, returning the iteration counts alongside the
-- compiled term. The counts are the numbers the compiler already relies on to
-- claim the program is total; handing them back costs nothing, and re-running
-- this pass to recover them would cost minutes.
--
-- The failure carries no location — `UnsizedExpr` has none. Callers holding
-- the `Term3` fill it in (see `Telomare.Eval.locateSizingFailure`).
sizeTermM :: SizingSettings -> UnsizedExpr -> Either SizingFailure (SizedRecursion, CompiledExpr)
sizeTermM sizingSettings x = tidyUp . ($ []) . runReaderT . transformNoDeferM evalStep $ mx where
  unlocated tok kind = SizingFailure
    { sizingFailureToken = tok
    , sizingFailureKind = kind
    , sizingFailureLoc = Nothing
    }
  failConvert x = (>>= Left) $ ("sizeTermM convert, unhandled:\n" <>) .  prettyPrint <$> sequence x
  forceType :: StuckExpr -> StuckExpr
  forceType = id
  inputRestrictions = (\x -> debugTrace ("sizeTermM zeros are\n" <> show x) x) $ getInputLimits cm'
  zeros = zeroes inputRestrictions
  convertNakedEnvs = \case
    StuckFW EnvSF -> ZeroB
    x -> embed x
  dtt :: UnsizedExpr -> UnsizedExpr
  dtt t = debugTrace ("sizeTermM initial term is\n" <> prettyPrint t) t
  cm' = dtt $ if doCap sizingSettings
    then capMain (indexedEE $ IVarF 0) x
    else x
  cm = removeRefinementWrappers cm'
  mx = removeRefinementWrappers $ if doCap sizingSettings
    then capMain (initialInput inputRestrictions) x
    else transformNoDefer convertNakedEnvs x
  tidyUp (StrictAccum sr@(SizedRecursion sm) r) = debugTrace ("sizes are: " <> show sm <> "\nand result is:\n" <> prettyPrint r) $ case foldAborted r of
    Just (UnsizableSR i) -> debugTrace "sizeTermM hit unsizable" Left $ unlocated i UnboundedInput
    Just (OverfueledSR i) -> debugTrace "sizeTermM ran out of budget" Left
      . unlocated i . FuelExhausted . succ $ maxSizingSize sizingSettings
    _ -> let sized = setSizes sm cm
         in debugTrace "sizeTermM found all sizes" pure . (,) sr . clean $ if doCap sizingSettings
            then uncap sized
            else sized
      where uncap = \case
              AppEE c _ -> c
              z -> error ("sizeTermM tidyUp trying to uncap something that isn't a main function:\n" <> prettyPrint z)
  clean :: UnsizedExpr -> CompiledExpr
  clean = verify . cata (convertBasic (convertStuck (convertAbort failConvert)))
  verify = \case
    Left e -> error e
    Right x -> x
  setSizes :: Map UnsizedRecursionToken (Maybe Int) -> UnsizedExpr -> UnsizedExpr
  setSizes sizeMap = cata $ \case
    UnsizedFW us@(UnsizedStubF tok _) -> case Map.lookup tok sizeMap of
      Just (Just n) -> debugTrace ("sizeTermM setting size: " <> show (tok, n)) iterate (StuckEE . SetEnvSF) EnvB !! (n + 1)
      _      -> debugTrace ("no size found for " <> show tok) SetEnvB EnvB
    UnsizedFW (TraceF _ x) -> x
    x -> embed x
  foldAborted = cata f where
    f = \case
      AbortFW (AbortedF (AbortRecursion i)) -> case b2i i of
        Just i' -> Just . OverfueledSR $ toEnum i'
        _ -> error $ "sizeTermM foldAborted unexpected AbortRecursion value:\n" <> prettyPrint i
      AbortFW (AbortedF AbortAny) -> error "sizeTermM AbortAny hit"
      AbortFW (AbortedF (AbortUnsizeable t)) -> case b2i t of
        Just i' -> Just . UnsizableSR $ toEnum i'
        _ -> error $ "sizeTermM foldAborted unexpected AbortUnsizeable value:\n" <> prettyPrint t
      x                                 -> Data.Foldable.fold x
  unhandledMerge x y = error ("sizeTermM unhandledMerge: " <> show (x,y))
  unhandledGate x = error ("sizeTermM unhandled gate input: " <> show x)
  gateResult = gateBasicResult (gateAbortResult (gateIndexedResult (gateSuperResult gateResult unhandledGate)))
  unsizedTest :: UnsizedRecursionToken -> UnsizedExpr -> UnsizedExpr
  unsizedTest ri = unsizedTestIndexed zeros (unsizedTestSuper (unsizedTest ri) (const id)) ri
  unsizedTest' ri = (\x -> debugTrace ("unsizedTest evaluated to value of\n" <> prettyPrint x) x) . unsizedTest ri
  unhandledError x = throw $ UGException ("sizeTermM unhandled case\n" <> prettyPrint x)
  evalStep = basicStepM (stuckStepM (abortStepM (indexedAbortStepM (indexedInputStepM zeros (indexedSuperStepM (superStepM gateResult evalStep (superAbortStepM evalStep (unsizedStepM''' (maxSizingSize sizingSettings) zeros unsizedTest' unhandledError))))))))


getSizesM :: Int -> UnsizedExpr -> Either SizingFailure SizedRecursion
getSizesM maxSize x = tidyUp . ($ []) . runReaderT . transformNoDeferM evalStep $ cm where
  unlocated tok kind = SizingFailure
    { sizingFailureToken = tok
    , sizingFailureKind = kind
    , sizingFailureLoc = Nothing
    }
  failConvert x = error $ "getSizesM convert, unhandled:\n" <> prettyPrint x
  inputRestrictions = getInputLimits x
  zeros = zeroes inputRestrictions
  cm = removeRefinementWrappers $ capMain (initialInput inputRestrictions) x
  tidyUp (StrictAccum sr@(SizedRecursion sm) r) = debugTrace ("sizes are: " <> show sm <> "\nand result is:\n" <> prettyPrint r) $ case foldAborted r of
    Just (UnsizableSR i)  -> Left $ unlocated i UnboundedInput
    Just (OverfueledSR i) -> Left . unlocated i . FuelExhausted $ succ maxSize
    _                     -> pure sr
  foldAborted = cata f where
    f = \case
      AbortFW (AbortedF (AbortRecursion t)) -> case b2i t of
        Just i' -> Just . OverfueledSR $ toEnum i'
        _ -> error $ "getSizesM foldAborted AbortRecursion unexpected value:\n" <> prettyPrint t
      AbortFW (AbortedF AbortAny) -> error "getSizesM AbortAny hit"
      AbortFW (AbortedF (AbortUnsizeable t)) -> case b2i t of
        Just i' -> Just . UnsizableSR $ toEnum i'
        _ -> error $ "getSizesM foldAborted AbortUnsizeable unexpected value:\n" <> prettyPrint t
      x                                 -> Data.Foldable.fold x
  unhandledMerge x y = error ("getSizesM unhandledMerge: " <> show (x,y))
  unhandledGate x = error ("getSizesM unhandled gate input: " <> show x)
  gateResult = gateBasicResult (gateAbortResult (gateIndexedResult (gateSuperResult gateResult unhandledGate)))
  unsizedTest :: UnsizedRecursionToken -> UnsizedExpr -> UnsizedExpr
  unsizedTest ri = unsizedTestIndexed zeros (unsizedTestSuper (unsizedTest ri) (const id)) ri
  unsizedTest' ri = unsizedTest ri . (\x -> debugTrace ("getSizesM value of\n" <> prettyPrint x) x)
  unhandledError x = error ("getSizesM unhandled case\n" <> prettyPrint x)
  evalStep = basicStepM (stuckStepM (abortStepM (indexedAbortStepM (indexedInputStepM zeros (indexedSuperStepM (superStepM gateResult evalStep (superAbortStepM evalStep (unsizedStepM''' maxSize zeros unsizedTest' failAndPrintStack))))))))

removeRefinementWrappers :: (Base g ~ f, BasicBase f, StuckBase f, AbortBase f, UnsizedBase f, Recursive g, Corecursive g) => g -> g
removeRefinementWrappers = cata f where
  f = \case
    UnsizedFW (RefinementWrapperF lt tc c) ->
      let innerTC = appB (LeftB EnvB) (RightB EnvB)
          performTC = deferB removeRefinementWrappersTC . SetEnvB $ PairB (SetEnvB $ PairB (AbortEE AbortF) innerTC) (RightB EnvB)
      in SetEnvB $ PairB performTC (PairB tc c)
    x -> embed x

evalStaticCheck :: Bool -> StaticCheckExpr -> Maybe BasicExpr
evalStaticCheck doCap t =
  let unhandledError x = error ("evalA unhandled case " <> prettyPrint x)
      runResult = let aStep :: StaticCheckExprF StaticCheckExpr -> StaticCheckExpr
                      aStep = basicStep (stuckStep (abortStep (deferredEvalStep' unhandledError)))
                      eval' :: StaticCheckExpr -> StaticCheckExpr
                      eval' = transformNoDefer aStep
                      inp = deferredEE $ BarrierF EnvB
                      x = (\x' -> debugTrace ("evalA starting expr:\n" <> prettyPrint x') x') $ if doCap then capMain inp t else t
                  in eval' x
      getAborted = \case
        AbortFW (AbortedF e) -> Just e
        DeferredFW (BarrierF _) -> Nothing
        x                    -> foldr (<|>) Nothing x
  in cata getAborted runResult

evalPartialUnsized :: Set Integer -> InputSizingExpr -> SizedRecursion
evalPartialUnsized zeroes = cata gatherLimits . transformNoDefer step where
  unsizedTest = unsizedTestIndexed zeroes (unsizedTestDeferred (\_ x -> error ("evalPartialUnsized unsizedTest unhandled:\n" <> prettyPrint x)))
  step = deferStep (basicStep (stuckStep (deferredEvalStep' (indexedInputStep zeroes (abortStep (abortDeferredStep (unsizedStep 255 unsizedTest step wrapUnknownStep)))))))
  dof _ =  id
  deferStep handleOther = \case
    StuckFW (DeferSF id x) -> dof id deferB (fromEnum id) . cata removeBarriers $ transformNoDefer (step . addBarrier) x
    x -> handleOther x
  addBarrier = \case
    StuckFW EnvSF -> embedD $ BarrierF EnvB
    x -> x
  removeBarriers = \case
    DeferredFW (BarrierF x) -> x
    x -> embed x
  wrapUnknownStep = deferredEE . BarrierF . embed
  gatherLimits = \case
    UnsizedFW (RecursionTestF ri x) -> SizedRecursion $ Map.singleton ri Nothing
    UnsizedFW (SizeStageF sm x) -> sm <> x
    x -> Data.Foldable.fold x


-- |What the sizing pass learned, kept rather than discarded. These iteration
-- counts are the numbers the compiler already relies on to claim a program is
-- total; reporting them asserts nothing new.
data SizingReport = SizingReport
  { sizingReportCounts :: SizedRecursion
  -- ^Per recursion site, the iteration count inferred over every input.
  , sizingReportLocs   :: Map UnsizedRecursionToken LocTag
  -- ^Where each site is in the source.
  , sizingReportBudget :: Int
  -- ^The unrolling budget the search was allowed.
  }

-- |Every recursion site's source location, recovered from the `Term3`
-- annotations that `term3ToUnsizedExpr` drops on its way to `UnsizedExpr`.
buildUnsizedLocMap :: Term3 -> Map UnsizedRecursionToken LocTag
buildUnsizedLocMap = cata f where
  f (anno CofreeT.:< g) = case g of
    Term3Unsized tok -> Map.singleton tok anno
    x                -> Data.Foldable.fold x

-- |`sizeTermM` names the recursion that failed but cannot say where it is.
locateSizingFailure :: Map UnsizedRecursionToken LocTag -> SizingFailure -> SizingFailure
locateSizingFailure locs failure =
  failure { sizingFailureLoc = Map.lookup (sizingFailureToken failure) locs }


-- |Every recursion site in the program, where it is, and how many times it can
-- iterate. The counts hold for every input: the sizing pass finds them by
-- running the program over a symbolic input, and takes the worst case across
-- the paths it explores.
--
-- Nothing here is a new claim. These are the very numbers the compiler bakes
-- into the program to make it total; a program that does not size does not
-- compile at all.
renderSizingCertificate :: SizingReport -> String
renderSizingCertificate report = unlines $
  "recursion sites (iterations, over every input):"
    : (if null sites then ["  none - this program has no unsized recursion"] else sites)
    <> ["", "sizing budget in force: " <> show (sizingReportBudget report) <> " unrollings"]
  where
    counts = Map.toAscList . unSizedRecursion $ sizingReportCounts report
    sites = fmap site counts
    site (tok, size) = "  " <> pad (place tok) <> "  <= " <> maybe "?" show size
    place tok =
      let named = "#" <> show (unUnsizedRecursionToken tok)
      in case Map.lookup tok (sizingReportLocs report) >>= renderLocTagCompact of
           Just spot -> spot <> " (" <> named <> ")"
           Nothing   -> named
    width = maximum (0 : fmap (length . place . fst) counts)
    pad s = s <> replicate (width - length s) ' '

