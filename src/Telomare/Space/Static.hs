{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase   #-}

-- |The static space bound: `Telomare.Eval.Space`'s machine run at compile
-- time, over an abstract input. The program it runs is the /sized/ term, so
-- every recursion is a church tower the walk unrolls exactly its inferred
-- count of times; per-iteration growth and retained accumulators are then
-- measured on the abstract run by reachability, exactly as the concrete meter
-- measures them — not modelled by per-combinator rules, which is the dead end
-- @design/SPACE.md@ records.
--
-- The abstract input mirrors the sizing pass's `Telomare.Size.initialInput`:
-- refinement-guaranteed pairs are expanded, refinement-guaranteed zeroes are
-- concrete, and everything else is a symbolic node `AInputN p` whose cell
-- bound is the input-size variable @|p|@ of `Telomare.SpaceBound`. A gate on
-- a symbolic value takes both branches and joins their values in a
-- superposition (`ASupN`), the same shape the sizing pass's @superStepM@
-- uses; the peak simply sees both branches' allocations, which can only
-- overcount.
--
-- What keeps that from exploding is the discipline the sizing pass carries
-- in its superposition tags: a fork is /about/ something — whether the input
-- part at path p is zero or a pair — and the superposition it joins into
-- remembers it. While a fork's branch runs, that commitment is in force (the
-- world), so a later test of the same part — the same `AInputN`, or a
-- superposition tagged with it — dispatches to the committed side instead of
-- forking again. Without this, k tests of one unknown cost 2^k worlds; with
-- it they cost two.
--
-- Where the concrete machine's every figure is a number, here it is a
-- `SpaceBound`. A node's bound is fixed at allocation: one cell for concrete
-- constructors, @|p|@ for a symbolic input, and for a superposition the
-- maximum of its sides' reachable subgraphs, frozen — the store is immutable,
-- so the sides never change. A sweep then sums the bounds of the distinct
-- reachable nodes without entering superpositions. Sharing that crosses a
-- superposition boundary is counted on both sides; documented looseness, not
-- a soundness hole.
--
-- Superpositions nest as unknown-driven choices pile up; shallow-equal sides
-- collapse (as the sizing pass's @mergeShallow@ does), and past a nesting
-- depth cap a superposition is widened to an opaque node that keeps only its
-- bound. An opaque value can still be projected (a part is no larger than the
-- whole) and gated on (both branches), but not applied or entered — that
-- reports `SpaceUnsupported` rather than guessing.
module Telomare.Space.Static where

import Data.Functor.Foldable (cata, project)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Telomare.Eval.Meter (identityFunction)
import Telomare.IR.Base
import Telomare.IR.Core
import Telomare.Machine (appB, decendant, doLeft, doRight)
import Telomare.Size (InputRestrictions (..))
import Telomare.SpaceBound

-- |Why no bound came out. Neither is a compile failure; the certificate
-- reports the bound as unknown and says why.
data StaticSpaceFailure
  = SpaceFuelExhausted
  | SpaceUnsupported String
  deriving (Eq, Show)

renderStaticSpaceFailure :: StaticSpaceFailure -> String
renderStaticSpaceFailure = \case
  SpaceFuelExhausted -> "the abstract run did not finish in its fuel"
  SpaceUnsupported why -> why

-- |Machine transitions the abstract run is allowed. The run is finite anyway
-- (every recursion is a baked tower); the fuel guards against a pathological
-- superposition blowup taking the compiler with it.
defaultStaticSpaceFuel :: Int
defaultStaticSpaceFuel = 4194304

type NodeId = Int

-- |Which side of a split the current world has committed to: True when the
-- input part a tag names is zero, False when it is a pair.
type World = Map Integer Bool

-- |An abstract value. The concrete constructors mirror
-- `Telomare.Eval.Space.Node`; the rest is what "abstract" adds.
data ANode
  = AZeroN
  | APairN !NodeId !NodeId
  | ADeferN !FunctionIndex CompiledExpr
  | AGateN
  | AAbortN
  | AAbortedN
  -- ^The payload's size is in the stored bound.
  | AInputN !Integer
  -- ^The input part at a path, unexamined: @|p|@ cells.
  | ASupN !Int !(Maybe Integer) !NodeId !NodeId
  -- ^Either side, from a fork: nesting depth, what the fork was about (the
  -- input path whose zero/pair split chose between them, when it was about
  -- one), the zero-world side, the pair-world side.
  | AOpaqueN
  -- ^A widened superposition: only its bound remains.
  | ADeadN
  -- ^An impossible world. A typechecked, sized program never gets stuck, so
  -- a stuck configuration can only come from an over-approximated fork whose
  -- two worlds were crossed; it costs nothing and vanishes from joins.
  deriving (Eq, Show)

-- |Sides of a superposition are alternatives, not parts: a sweep must not
-- walk into them, their cost is the frozen bound.
aChildren :: ANode -> [NodeId]
aChildren = \case
  APairN a b -> [a, b]
  _          -> []

-- |How deep superpositions may nest before widening.
supDepthCap :: Int
supDepthCap = 4

-- |What the machine still has to do with the value it is returning. The
-- first seven mirror `Telomare.Eval.Space.Frame`; the last three are how an
-- unknown forks. Forking frames carry the world to come back to, since the
-- branch in front of them runs under a commitment.
data AFrame
  = FPairRight CompiledExpr
  | FPairLeft !NodeId
  | FGate CompiledExpr CompiledExpr
  | FLeft
  | FRight
  | FSetEnv
  | FRestoreEnv !(Maybe NodeId)
  | FBothRight !(Maybe Integer) !World CompiledExpr
  -- ^A gate could not choose: its zero branch's value is coming back,
  -- evaluate the pair branch next, under the other commitment.
  | FJoinSup !(Maybe Integer) !World !NodeId
  -- ^The zero-world value, held while the pair world finishes; restore the
  -- world and join into a superposition.
  | FOpFork !PendOp !(Maybe Integer) !World !NodeId
  -- ^An operation over a superposed operand: the zero side's result is
  -- coming back, run the same operation on the held pair side.

-- |The operation `FOpFork` repeats on the second side.
data PendOp
  = OpGate CompiledExpr CompiledExpr
  | OpApply !NodeId
  -- ^Apply the side, as a function, to this argument.
  | OpArgOf !NodeId
  -- ^Apply this function to the side.
  | OpSetEnv
  | OpProj !Bool
  -- ^True for the left part.

aFrameRoots :: AFrame -> [NodeId]
aFrameRoots = \case
  FPairLeft a          -> [a]
  FRestoreEnv (Just e) -> [e]
  FJoinSup _ _ a       -> [a]
  FOpFork op _ _ a     -> a : opRoots op
  _                    -> []
  where
    opRoots = \case
      OpApply e -> [e]
      OpArgOf f -> [f]
      _         -> []

data AState = AState
  { aStore     :: !(IntMap (ANode, SpaceBound, Bool))
  -- ^Per node: its shape, its frozen cell bound, and whether a function
  -- (defer, gate or abort) is anywhere inside it — what decides if a
  -- superposition over it may ever be widened.
  , aNext      :: !NodeId
  , aEnv       :: !(Maybe NodeId)
  , aFrames    :: ![AFrame]
  , aWorld     :: !World
  , aPeak      :: !SpaceBound
  , aFuel      :: !Int
  , aLastLive  :: !SpaceBound
  -- ^The live bound at the last sweep.
  , aLiveCount :: !Int
  -- ^How many nodes that live set had; what the sweep cadence is scaled by.
  , aDebt      :: !SpaceBound
  -- ^Bounds of the nodes allocated since the last sweep — fresh content
  -- only: a join-produced node, whose frozen bound subsumes structure that
  -- is already alive, sweeps on the spot instead of entering the debt. The
  -- store grows by at most the debt between sweeps, so last live plus debt
  -- bounds any intermediate live set — that is what keeps the amortized
  -- cadence sound.
  , aDebtCount :: !Int
  , aLastPrune :: !Int
  -- ^`aNext` at the last store prune; pruning is rare so the join memo
  -- keeps earning its keep between prunes.
  , aPins      :: ![NodeId]
  -- ^Ids held in machine internals mid-transition (a join's first half, a
  -- two-part allocation) that no frame roots yet; sweeps must keep them.
  , aJoinMemo  :: !(Map (Maybe Integer, NodeId, NodeId) NodeId)
  -- ^Joins already made: the store is immutable, so the same two sides
  -- under the same tag always join to the same node. Loops re-joining the
  -- same alternatives hit this instead of re-walking their subgraphs.
  }

-- |Bound the peak live heap of the sized program applied to the abstract
-- input, or say why that could not be done.
evalSpaceStatic :: Int -> InputRestrictions -> CompiledExpr
                -> Either StaticSpaceFailure SpaceBound
evalSpaceStatic fuel irs prog = (\(b, _, _) -> b) <$> evalSpaceStatic' fuel irs prog

-- |`evalSpaceStatic` with the run's transition and allocation counts, for
-- calibrating against the concrete meter.
evalSpaceStatic' :: Int -> InputRestrictions -> CompiledExpr
                 -> Either StaticSpaceFailure (SpaceBound, Int, Int)
evalSpaceStatic' fuel irs prog =
  let (inputId, st0) = buildInput irs
      st1 = st0 { aEnv = Just inputId }
      settle (st, root) =
        let final = sweep [root] st
        in (aPeak final, fuel - aFuel final, aNext final)
  in settle <$> evalC st1 (appB prog EnvB)
  where
    look st i = let (n, _, _) = aStore st IntMap.! i in n
    boundOf st i = let (_, b, _) = aStore st IntMap.! i in b
    hasFun st i = let (_, _, h) = aStore st IntMap.! i in h

    -- The input graph, before the run: sweeps reach it through the
    -- environment root for as long as the program can still use it.
    buildInput irs' =
      let go n st
            | Set.member n (zeroes irs') = ins AZeroN (sbConst 1) st
            | any (`decendant` n) (pairs irs') =
                let (l, st1) = go (n * 2 + 1) st
                    (r, st2) = go (n * 2 + 2) st1
                in ins (APairN l r) (sbConst 1) st2
            | otherwise = ins (AInputN n) (sbInput n) st
          ins node b st =
            (aNext st, st { aStore = IntMap.insert (aNext st) (node, b, False) (aStore st)
                          , aNext = aNext st + 1 })
      in go 0 (AState IntMap.empty 0 Nothing [] Map.empty mempty fuel (sbConst 0) 0 (sbConst 0) 0 0 [] Map.empty)

    -- What the current world already knows about the input part at a path:
    -- committed zero (a zero has only zeroes under it, so an ancestor's zero
    -- commitment covers it), committed pair, or nothing.
    worldSide st p = case Map.lookup p (aWorld st) of
      Just s -> Just s
      Nothing
        | any (\(t, s) -> s && p `decendant` t) (Map.toList (aWorld st)) -> Just True
        | otherwise -> Nothing

    commitW t s st = case t of
      Just p  -> st { aWorld = Map.insert p s (aWorld st) }
      Nothing -> st

    -- The reachable bound from some roots: distinct nodes, superpositions
    -- contributing their frozen bound and not their sides. Concrete cells
    -- are counted in one Int; only symbolic nodes pay bound arithmetic.
    reachBound st = fst . reachBoundCounted st

    reachBoundCounted st = go IntSet.empty (0 :: Int) [] where
      go visited !plain specials = \case
        [] -> ( foldr sbAdd (sbConst (fromIntegral plain)) specials
              , IntSet.size visited )
        (i : rest)
          | IntSet.member i visited -> go visited plain specials rest
          | otherwise ->
              let (node, b, _) = aStore st IntMap.! i
                  visited' = IntSet.insert i visited
                  next = aChildren node <> rest
              in case node of
                AZeroN      -> go visited' (plain + 1) specials next
                APairN _ _  -> go visited' (plain + 1) specials next
                ADeferN _ _ -> go visited' (plain + 1) specials next
                AGateN      -> go visited' (plain + 1) specials next
                AAbortN     -> go visited' (plain + 1) specials next
                _           -> go visited' plain (b : specials) next

    sweep extra st =
      let roots = extra <> aPins st <> foldMap pure (aEnv st)
            <> concatMap aFrameRoots (aFrames st)
          (live0, liveCount) = reachBoundCounted st roots
          -- Forced here and now: an unforced accumulation retains the store
          -- it was measured over, and the walk's memory grows with every
          -- allocation it ever made instead of with its live set.
          !live = sbForce live0
          -- What the store could have held at its worst since the last look.
          !upper = sbForce (sbAdd (aLastLive st) (aDebt st))
          !peak = sbForce (sbMax (sbMax (aPeak st) upper) live)
          st' = st { aPeak = peak
                   , aLastLive = live
                   , aLiveCount = liveCount
                   , aDebt = sbConst 0
                   , aDebtCount = 0
                   }
      in if aNext st' - aLastPrune st' > 500000
         then pruneStore roots st'
         else st'

    -- Now and then, drop what nothing can reach and the memo entries that
    -- pointed into it; without this the store and memo grow without bound
    -- and garbage-collection pressure grinds a long walk down. Rare, so the
    -- memo keeps earning between prunes. The measuring walk stops at
    -- superpositions, but a live superposition's sides can still be read,
    -- so the keep-walk goes through them.
    pruneStore roots st =
      let keep = markAll st IntSet.empty roots
          keepK i = IntSet.member i keep
      in st { aStore = IntMap.restrictKeys (aStore st) keep
            , aJoinMemo = Map.filterWithKey
                (\(_, a, b) i -> keepK a && keepK b && keepK i)
                (aJoinMemo st)
            , aLastPrune = aNext st
            }

    markAll st visited = \case
      [] -> visited
      (i : rest)
        | IntSet.member i visited -> markAll st visited rest
        | otherwise ->
            let (node, _, _) = aStore st IntMap.! i
                kids = case node of
                  APairN a b    -> [a, b]
                  ASupN _ _ a b -> [a, b]
                  _             -> []
            in markAll st (IntSet.insert i visited) (kids <> rest)

    alloc node b0 st =
      let i = aNext st
          -- Stored bounds are folded at every sweep; keeping each one a
          -- single affine (the pointwise maximum of its alternatives) makes
          -- that fold one cheap merge per node instead of a cross product.
          !b = sbForce (sbWiden 1 b0)
          -- A join-produced node's frozen bound subsumes structure that is
          -- mostly already alive; letting it into the debt would double
          -- count wildly, so those measure on the spot. A concrete cell or
          -- a symbolic input part is genuinely fresh content.
          subsuming = case node of
            ASupN {}  -> True
            AOpaqueN  -> True
            AAbortedN -> True
            _         -> False
          !funInside = case node of
            ADeferN _ _   -> True
            AGateN        -> True
            AAbortN       -> True
            APairN x y    -> hasFun st x || hasFun st y
            ASupN _ _ x y -> hasFun st x || hasFun st y
            _             -> False
          !debt = if subsuming then aDebt st else sbForce (sbAdd (aDebt st) b)
          st1 = st { aStore = IntMap.insert i (node, b, funInside) (aStore st)
                   , aNext = i + 1
                   , aDebt = debt
                   , aDebtCount = aDebtCount st + 1
                   }
          due = subsuming
            || aDebtCount st1 > max 256 (aLiveCount st1 `div` 2)
      in (i, if due then sweep [i] st1 else st1)

    allocRet st node b = let (i, st') = alloc node b st in retC st' i

    -- Allocate while some loose ids must survive the sweep.
    allocPinned pins node b st =
      let (i, st') = alloc node b (st { aPins = pins <> aPins st })
      in (i, st' { aPins = drop (length pins) (aPins st') })

    -- Run a step while some loose ids must survive its sweeps.
    pinned pins act st = do
      (st1, r) <- act (st { aPins = pins <> aPins st })
      pure (st1 { aPins = drop (length pins) (aPins st1) }, r)

    spend st
      | aFuel st <= 0 = Left SpaceFuelExhausted
      | otherwise = pure st { aFuel = aFuel st - 1 }

    unsupported why = Left (SpaceUnsupported ("space bound: " <> why))

    push f st = st { aFrames = f : aFrames st }

    pop st = st { aFrames = drop 1 (aFrames st) }

    aDefer x = case project x of
      StuckFW (DeferSF fi body) -> ADeferN fi body
      _ -> error "Telomare.Space.Static: expected a function"

    -- As in the concrete machine, the gate-switch shape comes first: taken
    -- apart generically it would evaluate both branches even on a known
    -- scrutinee.
    evalC st0' whole = spend st0' >>= \st -> case project whole of
      GateSwitch l r s     -> evalC (push (FGate l r) st) s
      BasicFW ZeroSF       -> allocRet st AZeroN (sbConst 1)
      BasicFW (PairSF a b) -> evalC (push (FPairRight b) st) a
      StuckFW (DeferSF fi body) -> allocRet st (ADeferN fi body) (sbConst 1)
      StuckFW GateSF       -> allocRet st AGateN (sbConst 1)
      StuckFW (LeftSF x)   -> evalC (push FLeft st) x
      StuckFW (RightSF x)  -> evalC (push FRight st) x
      StuckFW (SetEnvSF x) -> evalC (push FSetEnv st) x
      StuckFW EnvSF -> case aEnv st of
        Just i  -> retC st i
        Nothing -> unsupported "unapplied environment reference"
      AbortFW AbortF       -> allocRet st AAbortN (sbConst 1)
      AbortFW (AbortedF e) ->
        allocRet st AAbortedN (sbConst (1 + basicCells e))
      _ -> unsupported "unexpected expression"

    basicCells = cata $ \case
      ZeroSF     -> 1
      PairSF a b -> 1 + a + b

    retC st0' v = spend st0' >>= \st -> case aFrames st of
      [] -> pure (st, v)
      FPairRight b : k
        | isDead st v -> retC (st { aFrames = k }) v
        | otherwise -> evalC (st { aFrames = FPairLeft v : k }) b
      FPairLeft a : k
        | isDead st v -> retC (st { aFrames = k }) v
        | otherwise -> allocRet (st { aFrames = k }) (APairN a v) (sbConst 1)
      FGate l r : _ -> gateD (pop st) l r v
      FLeft : _  -> projD (pop st) True v
      FRight : _ -> projD (pop st) False v
      FSetEnv : _ -> setEnvD (pop st) v
      FRestoreEnv saved : k ->
        retC (st { aEnv = saved, aFrames = k }) v
      FBothRight t w r : k ->
        evalC (commitW t False (st { aFrames = FJoinSup t w v : k, aWorld = w })) r
      FJoinSup t w a : k ->
        joinSup (st { aFrames = k, aWorld = w }) t a v >>= uncurry retC
      FOpFork op t w b : k ->
        let st1 = commitW t False
              (st { aFrames = FJoinSup t w v : k, aWorld = w })
        in case op of
          OpGate l r -> gateD st1 l r b
          OpApply e  -> applyD st1 b e
          OpArgOf f  -> applyD st1 f b
          OpSetEnv   -> setEnvD st1 b
          OpProj tl  -> projD st1 tl b

    -- Run an operation over a superposition's sides — or, when the world
    -- has already committed on what the superposition is about, over just
    -- the committed side. Dispatch-not-fork is what keeps repeated tests of
    -- one unknown from multiplying worlds.
    onSup st t a b op perform = case t >>= worldSide st of
      Just True  -> perform st a
      Just False -> perform st b
      Nothing ->
        perform (commitW t True (push (FOpFork op t (aWorld st) b) st)) a

    -- A gate with its scrutinee: choose, or take both and superpose. A
    -- non-data scrutinee cannot happen in a typechecked program, so it marks
    -- an impossible fork world.
    gateD st l r v = case look st v of
      AZeroN      -> evalC st l
      APairN _ _  -> evalC st r
      AAbortedN   -> retC st v
      ADeadN      -> retC st v
      AInputN p -> case worldSide st p of
        Just True  -> evalC st l
        Just False -> evalC st r
        Nothing    -> forkGate (Just p)
      AOpaqueN -> forkGate Nothing
      ASupN _ t a b -> onSup st t a b (OpGate l r) (\st' side -> gateD st' l r side)
      _ -> dead st
      where
        forkGate t =
          evalC (commitW t True (push (FBothRight t (aWorld st) r) st)) l

    -- A projection. In a world where the part is committed zero, the part's
    -- parts are zero too.
    projD st takeLeft v = case look st v of
      APairN a b  -> retC st (if takeLeft then a else b)
      AZeroN      -> retC st v
      AAbortedN   -> retC st v
      AInputN p
        | worldSide st p == Just True -> allocRet st AZeroN (sbConst 1)
        | otherwise ->
            let c = if takeLeft then p * 2 + 1 else p * 2 + 2
            in if Set.member c (zeroes irs)
               then allocRet st AZeroN (sbConst 1)
               else allocRet st (AInputN c) (sbInput c)
      ADeadN      -> retC st v
      AOpaqueN    -> allocRet st AOpaqueN (boundOf st v)
      ASupN _ t a b -> onSup st t a b (OpProj takeLeft) (`projD` takeLeft)
      _           -> dead st

    setEnvD st v = case look st v of
      AAbortedN     -> retC st v
      ADeadN        -> retC st v
      APairN f e    -> applyD st f e
      ASupN _ t a b -> onSup st t a b OpSetEnv setEnvD
      -- A widened pair has lost its function; that is a real limitation,
      -- not an impossible world.
      AOpaqueN      -> unsupported "SetEnv of a widened value"
      _             -> dead st

    applyD st f e = case (look st f, look st e) of
      (ADeadN, _) -> retC st f
      (_, ADeadN) -> retC st e
      (AAbortedN, _) -> retC st f
      (_, AAbortedN) -> retC st e
      (AAbortN, AZeroN) -> allocRet st (aDefer identityFunction) (sbConst 1)
      (AAbortN, APairN _ _) ->
        allocRet st AAbortedN (sbAdd (sbConst 1) (reachBound st [e]))
      -- The assert fires exactly when the part is a pair, so the fork is
      -- about the part and carries its tag.
      (AAbortN, AInputN p) -> case worldSide st p of
        Just True  -> allocRet st (aDefer identityFunction) (sbConst 1)
        Just False -> allocRet st AAbortedN (sbAdd (sbConst 1) (reachBound st [e]))
        Nothing -> do
          let (i1, st1) = allocPinned [e] (aDefer identityFunction) (sbConst 1) st
              (i2, st2) = allocPinned [i1] AAbortedN (sbAdd (sbConst 1) (reachBound st1 [e])) st1
          joinSup st2 (Just p) i1 i2 >>= uncurry retC
      (AAbortN, ASupN _ t a b) -> onSup st t a b (OpArgOf f) (applyTo f)
      (AAbortN, _) -> do
        let (i1, st1) = allocPinned [e] (aDefer identityFunction) (sbConst 1) st
            (i2, st2) = allocPinned [i1] AAbortedN (sbAdd (sbConst 1) (reachBound st1 [e])) st1
        joinSup st2 Nothing i1 i2 >>= uncurry retC
      (AGateN, AZeroN) -> allocRet st (aDefer doLeft) (sbConst 1)
      (AGateN, APairN _ _) -> allocRet st (aDefer doRight) (sbConst 1)
      -- A gate selector splits on the same zero-or-pair question.
      (AGateN, AInputN p) -> case worldSide st p of
        Just True  -> allocRet st (aDefer doLeft) (sbConst 1)
        Just False -> allocRet st (aDefer doRight) (sbConst 1)
        Nothing -> do
          let (i1, st1) = alloc (aDefer doLeft) (sbConst 1) st
              (i2, st2) = allocPinned [i1] (aDefer doRight) (sbConst 1) st1
          joinSup st2 (Just p) i1 i2 >>= uncurry retC
      (AGateN, ASupN _ t a b) -> onSup st t a b (OpArgOf f) (applyTo f)
      (AGateN, _) -> do
        let (i1, st1) = alloc (aDefer doLeft) (sbConst 1) st
            (i2, st2) = allocPinned [i1] (aDefer doRight) (sbConst 1) st1
        joinSup st2 Nothing i1 i2 >>= uncurry retC
      (ADeferN _ body, _) ->
        evalC ((push (FRestoreEnv (aEnv st)) st) { aEnv = Just e }) body
      (ASupN _ t a b, _) -> onSup st t a b (OpApply e) (\st' side -> applyD st' side e)
      -- A widened value may well have held a function; refusing is honest,
      -- inventing a body is not.
      (AOpaqueN, _) -> unsupported "application of a widened value"
      _ -> dead st
      where
        applyTo g st' = applyD st' g

    isDead st i = case look st i of
      ADeadN -> True
      _      -> False

    dead st = allocRet st ADeadN (sbConst 0)

    -- Join two alternatives: same id or same shallow shape collapse, a dead
    -- world vanishes, two pairs join pointwise, past the depth cap only the
    -- bound survives.
    joinSup st t a b
      | a == b = pure (st, a)
      | isDead st a = pure (st, b)
      | isDead st b = pure (st, a)
      | shallowEqA (look st a) (look st b) = pure (st, a)
      -- A remembered join may have been pruned since; verify before using.
      | Just i <- Map.lookup (t, a, b) (aJoinMemo st)
      , IntMap.member i (aStore st) =
          pure (st, i)
      -- The pointwise merge: a superposition of two pairs is a pair of
      -- superpositions. Sound for a bound, since a maximum of sums is never
      -- above the sum of maxima, and structurally decisive: a superposition
      -- of closures (code, env) collapses to one closure over superposed
      -- environments, function positions meet and cancel, and nesting depth
      -- resets at every pair. Under the same tag the selection stays
      -- consistent, so no precision is lost to world-crossing where it
      -- matters.
      | APairN a1 b1 <- look st a, APairN a2 b2 <- look st b = do
          (st1, l) <- pinned [a, b] (\s -> joinSup s t a1 a2) st
          (st2, r) <- pinned [a, b, l] (\s -> joinSup s t b1 b2) st1
          let (i, st3) = allocPinned [l] (APairN l r) (sbConst 1) st2
          pure (remember st3 i, i)
      | otherwise =
          let depth = 1 + max (depthOf (look st a)) (depthOf (look st b))
              joined = sbMax (reachBound st [a]) (reachBound st [b])
              -- Widening keeps only the bound, and a bound cannot be
              -- applied; data can afford that, functions cannot.
              widen = depth > supDepthCap
                && not (hasFun st a) && not (hasFun st b)
          in if widen
             then let (i, st') = alloc AOpaqueN joined st in pure (remember st' i, i)
             else let (i, st') = alloc (ASupN depth t a b) joined st in pure (remember st' i, i)
      where
        remember st' i = st' { aJoinMemo = Map.insert (t, a, b) i (aJoinMemo st') }

    depthOf = \case
      ASupN d _ _ _ -> d
      _             -> 0

    shallowEqA a b = case (a, b) of
      (AZeroN, AZeroN)           -> True
      (APairN x y, APairN x' y') -> x == x' && y == y'
      (ADeferN i _, ADeferN j _) -> i == j
      (AGateN, AGateN)           -> True
      (AAbortN, AAbortN)         -> True
      (AInputN n, AInputN m)     -> n == m
      _                          -> False
