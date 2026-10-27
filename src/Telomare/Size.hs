{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

-- |The sizing pass: telomare's totality checker. 'sizeTermM' abstractly
-- interprets the program over a symbolic input ('initialInput', bounded by
-- the refinement-derived 'InputRestrictions' from 'getInputLimits') and
-- infers, per unsized recursion site, an iteration count that holds for
-- every input - then bakes those counts into the term as church towers.
-- A program that cannot be sized does not compile ('SizingFailure').
module Telomare.Size where

import Control.Applicative
import qualified Control.Comonad.Trans.Cofree as CofreeT (CofreeF (..))
import Data.Foldable
import Data.Functor.Foldable
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (isNothing)
-- import Data.SBV ((.<), (.>))
import Control.Exception (Exception)
import Control.Exception.Base (throw)
import Data.Functor.Identity (Identity, runIdentity)
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace
import Telomare.Error
import Telomare.IR.Base
import Telomare.IR.Core
import Telomare.IR.Loc
import Telomare.Machine hiding (debug, debugTrace)
import Telomare.PrettyPrint
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
    -- a function value is neither impossible nor restricting
    d@(StuckFW (DeferSF _ _)) | isNothing expected -> pure . pure $ embed d
    GateSwitch l r s ->
      let nl = f expected l
          nr = f expected r
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
    -- an abort never yields a value, so a gate path ending in one is ruled
    -- out: a refinement check @if r then abort r else c@ restricts @r@ to Zero
    AbortFW _ -> Nothing
    _ -> Nothing
  cleanup = \case
    Just (StrictAccum s _) -> s
    _ -> mempty

findInputLimitStepM :: (InputSizingExprF InputSizingExpr -> StrictAccum InputRestrictions InputSizingExpr)
  -> InputSizingExprF InputSizingExpr -> StrictAccum InputRestrictions InputSizingExpr
findInputLimitStepM handleOther x = f x where
  f = \case
    UnsizedFW (RefinementWrapperF o tc c) ->
      let
          -- only whether the check passes matters here, not the value it guards
          checked = refinementGate o (transformNoDefer refinementCheckStep $ appB tc c) ZeroB
          stripBarrier = \case
            DeferredFW (BarrierF inner) -> inner
            other -> embed other
          s = extractInputRestrictions $ cata stripBarrier checked
      in StrictAccum s c
    _ -> handleOther x

-- |@if r then abort r else c@ over an evaluated check result @r@ and value
-- @c@: what a refinement check reduces to once its check function has run.
--
-- An undecided @r@ leaves a barrier-wrapped gate switch with @r@ itself as
-- the scrutinee. Gating on @r@ the usual way would push the gate into
-- @r@'s own residual gates, copying @c@ onto every path that passes, and
-- nested checks would multiply the copies. Left whole, @c@ appears once,
-- and whatever is done to the guarded value later goes into just its two
-- branches, one of which stays an abort.
refinementGate :: AbortOrigin -> InputSizingExpr -> InputSizingExpr -> InputSizingExpr
refinementGate o r c = case r of
  BasicEE ZeroSF       -> c
  a@(AbortEE _)        -> a
  BasicEE (PairSF _ _) -> aborted
  _                    -> deferredEE . BarrierF $ GateSwitchEE c aborted r
  where aborted = refinementCheckStep . AbortFW $ AbortF o r

-- |Evaluates a refinement check function against symbolic input, leaving
-- input-dependent gates as barrier-wrapped residuals for
-- 'extractInputRestrictions'.
--
-- A refinement nested inside the check (e.g. a check calling a Prelude
-- function whose arguments are refined) is evaluated in place: a decided
-- check reduces to its value or an abort, an undecided one to a gate
-- switch with an abort branch, so its restrictions apply only on the gate
-- paths where the nested check actually runs.
refinementCheckStep :: InputSizingExprF InputSizingExpr -> InputSizingExpr
refinementCheckStep = basicStep (stuckStep (abortStep (gateSwitchStep (deferredEvalStep (indexedInputStep Set.empty handleOther))))) where
  step = refinementCheckStep
  barrier = deferredEE . BarrierF
  -- an undecided gate yields one of its branches, so anything always done to
  -- its result can be done to each branch instead, keeping the result
  -- analyzable (e.g. Bool's @left vv@ when vv is @toBool x@). An abort
  -- branch stays an abort, since aborts propagate.
  gateSwitchStep handleOther' = \case
    StuckFW (LeftSF (DeferredEE (BarrierF (GateSwitchEE l r s)))) ->
      barrier $ GateSwitchEE (step . StuckFW $ LeftSF l) (step . StuckFW $ LeftSF r) s
    StuckFW (RightSF (DeferredEE (BarrierF (GateSwitchEE l r s)))) ->
      barrier $ GateSwitchEE (step . StuckFW $ RightSF l) (step . StuckFW $ RightSF r) s
    StuckFW (SetEnvSF (DeferredEE (BarrierF (GateSwitchEE l r s)))) ->
      barrier $ GateSwitchEE (step . StuckFW $ SetEnvSF l) (step . StuckFW $ SetEnvSF r) s
    FillFunction GateB (DeferredEE (BarrierF (GateSwitchEE l r s))) ->
      barrier $ GateSwitchEE (step $ FillFunction GateB l) (step $ FillFunction GateB r) s
    FillFunction (DeferredEE (BarrierF (GateSwitchEE l r s))) e ->
      barrier $ GateSwitchEE (step $ FillFunction l e) (step $ FillFunction r e) s
    other -> handleOther' other
  handleOther = \case
    FillFunction GateB i@(IndexedEE _) -> deferredEE . BarrierF . embed $ FillFunction GateB i
    UnsizedFW (RefinementWrapperF o tc c) -> refinementGate o (app tc c) c
    other -> error $ "refinementCheckStep eval unexpected:\n" <> prettyPrint other
  -- 'appB' over already-evaluated operands: tc is a closure, so twiddle it
  -- into (function, (input, env)) before applying
  app tc c = step . StuckFW . SetEnvSF . step $ FillFunction twiddleB (PairB c tc)

term3ToUnsizedExpr :: Term3 -> UnsizedExpr
term3ToUnsizedExpr = runIdentity . cata conv where
  conv :: CofreeT.CofreeF Term3F LocTag (Identity UnsizedExpr) -> Identity UnsizedExpr
  conv = convertBasic (convertStuck (convertAbort convertOther))
  convertOther (_ CofreeT.:< g) = case g of
    Term3Unsized urt -> pure . unsizedEE . UnsizedStubF urt $ EnvB
    Term3CheckingWrapper o tc c -> unsizedEE <$> (RefinementWrapperF o <$> tc <*> c)
    _z -> error "term3ToUnsizedExpr could not convert"

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
sizeTermM sizingSettings x = tidyUp . transformNoDeferM evalStep $ mx where
  unlocated tok kind = SizingFailure
    { sizingFailureToken = tok
    , sizingFailureKind = kind
    , sizingFailureLoc = Nothing
    }
  failConvert unhandled = (>>= Left) $ ("sizeTermM convert, unhandled:\n" <>) .  prettyPrint <$> sequence unhandled
  inputRestrictions = (\ir -> debugTrace ("sizeTermM zeros are\n" <> show ir) ir) $ getInputLimits cm'
  zeros = zeroes inputRestrictions
  convertNakedEnvs = \case
    StuckFW EnvSF -> ZeroB
    other -> embed other
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
    Right converted -> converted
  setSizes :: Map UnsizedRecursionToken (Maybe Int) -> UnsizedExpr -> UnsizedExpr
  setSizes sizeMap = cata $ \case
    UnsizedFW _us@(UnsizedStubF tok _) ->
      let n = chainLinks (SizedRecursion sizeMap) tok
      in debugTrace ("sizeTermM setting size: " <> show (tok, n)) sizedRecursionChain tok n
    UnsizedFW (TraceF _ inner) -> inner
    other -> embed other
  -- only the sizing analysis's own aborts say anything about sizing; the
  -- program's aborts are just one of the outcomes some inputs have
  foldAborted = para f where
    f = \case
      AbortFW (AbortF o (m, _)) | abortKind o == SizingAbort -> case messageData m of
        AbortRecursion i -> case b2i i of
          Just i' -> Just . OverfueledSR $ toEnum i'
          _ -> error $ "sizeTermM foldAborted unexpected AbortRecursion value:\n" <> prettyPrint i
        AbortAny -> error "sizeTermM AbortAny hit"
        AbortUnsizeable t -> case b2i t of
          Just i' -> Just . UnsizableSR $ toEnum i'
          _ -> error $ "sizeTermM foldAborted unexpected AbortUnsizeable value:\n" <> prettyPrint t
        other -> error $ "sizeTermM foldAborted unexpected sizing abort:\n" <> prettyPrint other
      other -> Data.Foldable.fold (snd <$> other)
  unhandledGate g = error ("sizeTermM unhandled gate input: " <> show g)
  gateResult = gateBasicResult (gateAbortResult (gateIndexedResult (gateSuperResult gateResult unhandledGate)))
  unsizedTest :: UnsizedRecursionToken -> UnsizedExpr -> UnsizedExpr
  unsizedTest ri = unsizedTestIndexed zeros (unsizedTestSuper (unsizedTest ri) (const id)) ri
  unsizedTest' ri = (\v -> debugTrace ("unsizedTest evaluated to value of\n" <> prettyPrint v) v) . unsizedTest ri
  unhandledError err = throw $ UGException ("sizeTermM unhandled case\n" <> prettyPrint err)
  evalStep = basicStepM (stuckStepM (abortStepM (indexedInputStepM zeros (indexedSuperStepM (superStepM gateResult evalStep (unsizedStepM''' (maxSizingSize sizingSettings) zeros unsizedTest' unhandledError))))))

removeRefinementWrappers :: (Base g ~ f, BasicBase f, StuckBase f, AbortBase f, UnsizedBase f, Recursive g, Corecursive g) => g -> g
removeRefinementWrappers = cata f where
  f = \case
    UnsizedFW (RefinementWrapperF o tc c) -> refinementCheckB o tc c
    x -> embed x

evalStaticCheck :: Bool -> StaticCheckExpr -> Maybe (AbortOrigin, BasicExpr)
evalStaticCheck shouldCap t =
  let unhandledError x = error ("evalA unhandled case " <> prettyPrint x)
      runResult = let aStep :: StaticCheckExprF StaticCheckExpr -> StaticCheckExpr
                      aStep = basicStep (stuckStep (abortStep (deferredEvalStep' unhandledError)))
                      eval' :: StaticCheckExpr -> StaticCheckExpr
                      eval' = transformNoDefer aStep
                      inp = deferredEE $ BarrierF EnvB
                      x = (\x' -> debugTrace ("evalA starting expr:\n" <> prettyPrint x') x') $ if shouldCap then capMain inp t else t
                  in eval' x
      -- a fired abort: not under a defer (code that has not run) or a
      -- barrier (code waiting on input)
      getAborted = \case
        AbortFW (AbortF o (m, im)) -> im <|> Just (o, messageData m)
        DeferredFW (BarrierF _)    -> Nothing
        StuckFW (DeferSF _ _)      -> Nothing
        x                          -> foldr ((<|>) . snd) Nothing x
  in para getAborted runResult

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

