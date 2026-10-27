{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE PatternSynonyms  #-}

-- | An interaction-combinator runtime for 'CompiledExpr'.
--
-- This is the \"abstract algorithm\" flavor of sharing-graph reduction:
-- duplicator nodes carry labels minted fresh at every template
-- instantiation, there are no boxes or brackets at runtime, and dup pairs
-- annihilate only with themselves. That rule set is not sound for arbitrary
-- terms — a duplicator reaching a copy of itself through a term that
-- duplicates its own duplicator computes garbage — and EAL typability
-- ('Telomare.EAL') is the classical sufficient condition under which it is
-- correct. The EAL pass is therefore this runtime's admission certificate:
-- the only analysis output the runtime's *correctness* depends on is that
-- verdict (no levels, no sharing plan). Templates are keyed by the same
-- content hash that keys the DeferMap ('Telomare.Resolve.deferLift'), so
-- per-hash 'Telomare.EAL.CodeGuidance' addresses templates directly;
-- guidance-driven choices must remain advisory (strategy, never meaning).
--
-- Telomare maps onto interaction agents unusually cleanly because it has no
-- binders: Env is the only variable, so a compiled Defer body is a static
-- net template whose env interface is a single wire. That wire fans out
-- through a splitter tree built from the body's projection-path usage —
-- the same fact 'Telomare.EAL.CodeGuidance' publishes as 'cgUsage': each
-- used env component is delivered on its own wire ('ICSplit' takes a pair
-- apart in one interaction), unused components are erased at the highest
-- point, and duplication happens only where a path is genuinely used more
-- than once — exactly where the analyzer charges contraction.
-- Every Defer becomes a 'Template' plus an 'ICRef' pointer node; copying a
-- ref is copying a pointer (the code table exists at runtime), and only the
-- instantiated body's wiring is ever duplicated structurally.
--
-- The semantics mirror the reference evaluator ('Telomare.Machine'
-- 'basicStep'\/'stuckStep'\/'abortStep') rule for rule:
--
--   * @SetEnv (Pair (Defer d) e)@ instantiates d's template with env e.
--   * A gate applied to a scrutinee yields one of the reserved selector
--     defers ('doLeft'\/'doRight'); branch selection is then ordinary
--     application of a projection body, and the unselected branch is erased.
--   * Abort applied to Zero yields the reserved identity defer; applied to
--     a pair it becomes an Aborted value that consumers propagate. Aborted
--     values surface as 'AbortRunTime' only if they survive into the
--     result, matching the reference checkError.
--
-- Interaction nets are confluent, so although this runtime fires redexes in
-- worklist order rather than the reference's evaluation order, final
-- results agree on terminating programs; termination itself is what the EAL
-- certificate promises. Bodies that are exactly equal share one template
-- (the content hash narrows candidates; an exact 'Eq' check decides, since
-- the hash is blind to the FunctionIndexes of nested defers). Each 'ICRef'
-- node carries its own site's FunctionIndex, so readback reconstructs the
-- defer value the reference evaluator would produce — defer equality is by
-- index, which makes naive whole-value dedup observable.
--
-- One discovered subtlety governs the error rules: the reference
-- evaluator, being ordinary lazy Haskell, is effectively call-by-need — a
-- stuck redex sitting in a discarded gate branch is never forced, and
-- compiled sizing machinery really does leave ill-shaped applications in
-- dead branches. The net instead fires the redexes it instantiates, so an
-- ill-shaped interaction must produce an 'ICStuckV' poison value rather
-- than abort the run: erasure discards it silently (the net's analogue of
-- an unforced thunk), and only a stuck value surviving into demanded
-- output reports 'ICStuck'. Instantiation itself — the one step whose
-- cost is unbounded — is held back from that speculation: an apply
-- meeting code is parked (FIFO) and fired only when no other work
-- remains, after checking whether an eraser has meanwhile arrived at the
-- application's result; a dead application then collapses without ever
-- instantiating ('fireParked'), so a discarded branch's applications —
-- a diverging one included — cost a few collapse interactions instead of
-- their whole evaluation (or the fuel supply). The check is local, so
-- dead work hidden behind a still-pending consumer chain can fire before
-- its discard becomes visible — a residual cost, never a correctness
-- issue.
module Telomare.IC where

import Control.Comonad.Cofree (Cofree ((:<)), unwrap)
import Control.Monad (forM, forM_, unless, when)
import Control.Monad.Except
import Control.Monad.State.Strict (State)
import qualified Control.Monad.State.Strict as State
import Crypto.Hash (Digest, SHA256)
import Data.Foldable (asum, toList)
import Data.Functor.Foldable (cata, project)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Debug.Trace (trace)
import Telomare.EAL (CapShape (..), Step (..), showSteps)
import qualified Telomare.EnvUsage as Usage
import Telomare.IR.Base (AbortableF (..), BasicExpr, BasicExprF (..),
                         FunctionIndex, StuckF (..), forget, pattern AbortB,
                         pattern AbortEE, pattern AbortFW, pattern EnvB,
                         pattern GateB, pattern PairB, pattern StuckEE,
                         pattern StuckFW, pattern ZeroB)
import Telomare.IR.Core (CompiledExpr, CompiledExprF (..), RunTimeError (..))
import Telomare.Machine (abortInd, appB, deferB, doLeft, doRight, leftGateInd,
                         rightGateInd)
import Telomare.Resolve (DeferKeys (..), KeyedExpr, keyDefers)

-- | Temporary debugging switch: trace every interaction and instantiation.
debugIC :: Bool
debugIC = False

dbg :: Monad m => String -> m ()
dbg s = when debugIC $ trace s (pure ())

-- * Net representation

-- | Duplicator label: fresh per instantiated dup, so distinct dups always
-- commute and only the two halves of one dup annihilate.
type Label = Int

type TemplateId = Int

-- | Agent kinds. Slot 0 is always the principal port; value kinds face
-- their consumer with it, consumer kinds face the value they demand.
data ICKind
  = ICRoot             -- ^ 1 port: receives the final result; never interacts
  | ICExt              -- ^ 2 ports: template boundary (0 env in, 1 result
                       --   out); exists only inside templates
  | ICEra              -- ^ 1 port: eraser (affine discard)
  | ICZero             -- ^ 1 port
  | ICGate             -- ^ 1 port
  | ICAbort            -- ^ 1 port
  | ICRef TemplateId FunctionIndex
                       -- ^ 1 port: pointer into the template table, copied
                       --   freely by dups. Carries its own site's defer
                       --   index: templates are shared between sites whose
                       --   bodies are equal, but defer equality is by
                       --   index, so readback needs the per-site identity
  | ICPair             -- ^ 3 ports: value, left component, right component
  | ICAborted          -- ^ 2 ports: value, message
  | ICDup Label        -- ^ 3 ports: value to copy, copy, copy
  | ICSplit            -- ^ 3 ports: pair to take apart, left component,
                       --   right component — a projection pair fused into
                       --   one agent, so destructuring neither duplicates
                       --   nor erases what both sides need
  | ICSetEnv           -- ^ 2 ports: operand (awaits a pair), result
  | ICApply            -- ^ 3 ports: function head, env, result
  | ICScrut            -- ^ 2 ports: gate scrutinee, result
  | ICScrutAbort       -- ^ 2 ports: abort message, result
  | ICLeft             -- ^ 2 ports: projection target, result
  | ICRight            -- ^ 2 ports: projection target, result
  | ICStuckV String    -- ^ 1 port: an ill-shaped interaction's result. The
                       --   reference evaluator is lazy, so a stuck redex in
                       --   a discarded branch is silently skipped there;
                       --   the net fires it eagerly, so stuckness must be a
                       --   value that erasure discards and only demanded
                       --   output reports.
  | ICData DataSrc     -- ^ 1 port: a data value held whole, not yet taken
                       --   apart: an iteration's input, or a part of one.
                       --   Copying and erasing it take one interaction; a
                       --   consumer that needs its shape first turns it into
                       --   the Zero or Pair it is ('revealData').
  deriving (Eq, Show)

-- | What an 'ICData' node holds: a known value when the net runs, or, when
-- 'Telomare.IC.Space' walks the net for every input at once, the part of the
-- input at a path (the whole input is path 0; the parts of the pair at path
-- @p@ are at @2p+1@ and @2p+2@).
data DataSrc
  = DataKnown BasicExpr
  | DataPart Integer
  deriving (Eq, Show)

data Port = Port
  { portNode :: !Int
  , portSlot :: !Int
  } deriving (Eq, Ord, Show)

-- | A node's kind plus, per slot, the port at the far end of its wire.
data Node = Node
  { nodeKind  :: ICKind
  , nodePorts :: IntMap Port
  } deriving Show

-- | One compiled Defer body: its nodes (boundary included), how many local
-- dup labels it mints, the body term (for reading refs back), and its
-- content hash — the shared key under which 'Telomare.EAL.CodeGuidance'
-- addresses this code.
data Template = Template
  { tplNodes  :: IntMap Node
  , tplExt    :: Int
  , tplLabels :: Int
  , tplBody   :: CompiledExpr
  , tplHash   :: Digest SHA256
  }

data ICError
  -- | A stuck value (data applied as a function, projection of a function,
  -- ...) survived into demanded output. Raised only at readback: a stuck
  -- redex whose result is discarded is not an error, matching the
  -- reference evaluator's laziness.
  = ICStuck String
  -- | The interaction budget ran out; carries interactions performed.
  | ICFuelExhausted Int
  -- | A net invariant was violated: a bug in this module, never a fact
  -- about the program.
  | ICInternal String
  deriving (Eq, Show)

data ICState = ICState
  { icNodes     :: IntMap Node
  , icNextNode  :: !Int
  , icNextLabel :: !Int
  , icActive    :: [(Int, Int)] -- ^ candidate active pairs (may go stale)
  , icParked    :: Seq (Int, Int)
                                -- ^ instantiation-bound pairs (an apply
                                -- meeting code), FIFO: fired one at a time
                                -- only when no eager work remains, after
                                -- the demand check of 'fireParked'
  , icEnvQueue  :: Map [Step] [Port]
                                -- ^ compile-time: env component wires per
                                -- projection path, to be consumed by the
                                -- body's occurrences
  , icTemplates :: IntMap Template
  , icNextTpl   :: !Int
  , icTplByKey  :: Map (Digest SHA256) TemplateId
                                -- ^ dedup index, by exact key ('dkExact'):
                                -- the content hash alone is index-blind,
                                -- and index-blind sharing would be visible
                                -- to readback
  , icFuel      :: !Int
  , icSpent     :: !Int         -- ^ interactions performed
  , icStats     :: Map String Int
  , icGuidance  :: Map (Digest SHA256) CapShape
    -- ^ per-hash capture layouts from the EAL pass ('ealCaptureLayouts'),
    -- consumed by the guided closure duplication and erasure rules; empty
    -- means every strategy keeps to its generic default
  , icResident  :: !Resources   -- ^ what the net holds now
  , icPeak      :: !Resources   -- ^ the most it has held, per component
  , icConstants :: !Resources
    -- ^ the cells of every constant compiled to one 'ICData' node, as if
    -- built node by node; held once, with the code, not in the net
  }

-- | The net's storage, counted in its own units: resident agents, stored
-- port entries (a wire is two entries, one per end; a dangling half is
-- one) and pending pairs (eager and parked, stale entries included until
-- they are popped). The counters change at exactly the primitive
-- mutations, so they are measurements, not estimates. Templates live in
-- their own table and are not part of the net ('templateStorage').
data Resources = Resources
  { resAgents :: !Int
  , resPorts  :: !Int
  , resWork   :: !Int
  } deriving (Eq, Show)

noResources :: Resources
noResources = Resources 0 0 0

-- | Componentwise maximum: each component's own peak. The components need
-- not peak at the same moment.
maxResources :: Resources -> Resources -> Resources
maxResources (Resources a p w) (Resources a' p' w') =
  Resources (max a a') (max p p') (max w w')

-- | Count a change in what the net holds, raising the peak if needed.
account :: (Resources -> Resources) -> ICState -> ICState
account f st =
  let now = f (icResident st)
  in st { icResident = now, icPeak = maxResources now (icPeak st) }

-- | A recount from scratch, for checking the incremental counters.
residentResources :: ICState -> Resources
residentResources st = Resources
  (IntMap.size (icNodes st))
  (sum (IntMap.size . nodePorts <$> icNodes st))
  (length (icActive st) + Seq.length (icParked st))

-- | The template table: agents and port entries of every compiled body,
-- plus every constant held whole, counted as the nodes and wires it would
-- take built node by node ('icConstants').
templateStorage :: ICState -> Resources
templateStorage st = Resources
  (sum (IntMap.size . tplNodes <$> tpls) + resAgents consts)
  (sum [ IntMap.size (nodePorts nd) | t <- tpls, nd <- IntMap.elems (tplNodes t) ]
     + resPorts consts)
  0
  where
    tpls = IntMap.elems (icTemplates st)
    consts = icConstants st

-- | What a data value takes built node by node: a node per cell, three
-- port entries per pair and one per zero.
dataStorage :: BasicExpr -> Resources
dataStorage = cata $ \case
  PairSF a b -> Resources (resAgents a + resAgents b + 1)
                          (resPorts a + resPorts b + 3) 0
  _zero      -> Resources 1 1 0

type ICM = ExceptT ICError (State ICState)

emptyState :: Map (Digest SHA256) CapShape -> Int -> ICState
emptyState guidance fuel = ICState IntMap.empty 0 0 [] Seq.empty Map.empty
  IntMap.empty 0 Map.empty fuel 0 Map.empty guidance noResources noResources
  noResources

-- * Primitive net operations

newNode :: ICKind -> ICM Int
newNode k = do
  n <- State.gets icNextNode
  State.modify' $ \st -> account (\r -> r { resAgents = resAgents r + 1 }) st
    { icNextNode = n + 1
    , icNodes = IntMap.insert n (Node k IntMap.empty) (icNodes st) }
  pure n

nodeAt :: Int -> ICM Node
nodeAt n = State.gets (IntMap.lookup n . icNodes) >>= \case
  Just nd -> pure nd
  Nothing -> throwError . ICInternal $ "no node " <> show n

kindOf :: Int -> ICM ICKind
kindOf = fmap nodeKind . nodeAt

peer :: Port -> ICM Port
peer (Port n s) = do
  nd <- nodeAt n
  case IntMap.lookup s (nodePorts nd) of
    Just q  -> pure q
    Nothing -> throwError . ICInternal $
      "unwired port " <> show n <> "/" <> show s

setHalf :: Port -> Port -> ICM ()
setHalf (Port n s) q = State.modify' $ \st ->
  case IntMap.lookup n (icNodes st) of
    Nothing -> st
    Just nd ->
      let ports = nodePorts nd
          st' = st { icNodes = IntMap.insert n
                       nd { nodePorts = IntMap.insert s q ports } (icNodes st) }
      in if IntMap.member s ports then st'
         else account (\r -> r { resPorts = resPorts r + 1 }) st'

-- | Wire two ports together. A principal-principal wiring between
-- interacting kinds is enqueued as an active pair — except an
-- instantiation-bound pair (an apply meeting code), which is parked for
-- the demand-checked firing of 'fireParked'.
connect :: Port -> Port -> ICM ()
connect p q = do
  setHalf p q
  setHalf q p
  case (p, q) of
    (Port a 0, Port b 0) -> do
      ka <- kindOf a
      kb <- kindOf b
      when (interactive ka && interactive kb) $
        if instantiating ka kb
          then State.modify' $ \st -> pending
            st { icParked = icParked st Seq.|> (a, b) }
          else State.modify' $ \st -> pending
            st { icActive = (a, b) : icActive st }
    _notPrincipals -> pure ()
  where
    interactive = \case
      ICRoot -> False
      ICExt  -> False
      _      -> True
    pending = account (\r -> r { resWork = resWork r + 1 })
    instantiating a b = case (a, b) of
      (ICApply, ICRef {}) -> True
      (ICRef {}, ICApply) -> True
      _notInstantiation   -> False

deleteNode :: Int -> ICM ()
deleteNode n = State.modify' $ \st ->
  case IntMap.lookup n (icNodes st) of
    Nothing -> st
    Just nd -> account (\r -> r { resAgents = resAgents r - 1
                                , resPorts = resPorts r - IntMap.size (nodePorts nd) })
      st { icNodes = IntMap.delete n (icNodes st) }

freshLabel :: ICM Label
freshLabel = do
  l <- State.gets icNextLabel
  State.modify' $ \st -> st { icNextLabel = l + 1 }
  pure l

-- | Record a statistic without spending fuel (compile-time events).
note :: String -> ICM ()
note name = State.modify' $ \st ->
  st { icStats = Map.insertWith (+) name 1 (icStats st) }

-- | Count one interaction against the fuel budget and the per-rule stats.
spend :: String -> ICM ()
spend name = do
  f <- State.gets icFuel
  when (f <= 0) $ do
    used <- State.gets icSpent
    throwError $ ICFuelExhausted used
  State.modify' $ \st -> st { icFuel = f - 1, icSpent = icSpent st + 1 }
  note name

-- * Compilation

-- | Env occurrences of a body per projection path (outside nested defers,
-- which are closed over their own env). The keys mirror the analyzer's
-- usage view ('Telomare.EAL.envUsageL') and its guidance ('cgUsage'):
-- the steps directly applied to the occurrence, innermost first — the
-- order they descend the env value.
envUsage :: CompiledExpr -> Map [Step] Int
envUsage = fmap fst . Usage.usage envView

envView :: CompiledExpr -> Usage.UsageView Step () CompiledExpr
envView t = case project t of
  StuckFW EnvSF         -> Usage.Occurrence ()
  StuckFW (LeftSF x)    -> Usage.Projection SL x
  StuckFW (RightSF x)   -> Usage.Projection SR x
  StuckFW (DeferSF _ _) -> Usage.Closed
  x                     -> Usage.Children (toList x)

-- | The projection path this term applies directly to Env, when it is
-- nothing but a projection chain over Env; Nothing as soon as anything
-- else intervenes. The Just cases are exactly the occurrences 'envUsage'
-- counts, so producer and consumer of the env wiring agree by
-- construction.
envPathOf :: CompiledExpr -> Maybe [Step]
envPathOf = Usage.envPath envView

-- | Run a net-building action against a fresh empty net, restoring the
-- current one afterwards; returns the built nodes and their label count.
isolatedNet :: ICM a -> ICM (a, IntMap Node, Int)
isolatedNet act = do
  saved <- State.get
  State.modify' $ \st -> st
    { icNodes = IntMap.empty, icNextNode = 0, icNextLabel = 0
    , icActive = [], icParked = Seq.empty, icEnvQueue = Map.empty
    , icResident = noResources, icPeak = noResources }
  r <- act
  built <- State.get
  -- a scratch net becomes a template; it never counts as part of the net
  State.modify' $ \st -> st
    { icNodes = icNodes saved, icNextNode = icNextNode saved
    , icNextLabel = icNextLabel saved
    , icActive = icActive saved, icParked = icParked saved
    , icEnvQueue = icEnvQueue saved
    , icResident = icResident saved, icPeak = icPeak saved }
  pure (r, icNodes built, icNextLabel built)

-- | The content hash of a defer value: its 'DeferMap' key, computed by
-- the hashing 'Telomare.Resolve.deferLift' uses, so templates and
-- per-hash 'Telomare.EAL.CodeGuidance' share one namespace by
-- construction. The hash names the lifted body (nested defers appear as
-- refs), so it is blind to FunctionIndexes.
deferHash :: CompiledExpr -> Either String (Digest SHA256)
deferHash d = case keyDefers d of
  Just keys :< _ -> Right (dkHash keys)
  _notDefer      -> Left "deferHash: not a defer value"

-- | Compile one Defer value into a template, or reuse the template of an
-- equal body already compiled. Equality is by exact key: the content hash
-- ignores nested defer indexes, and index-blind sharing would be visible
-- to readback. The site's own FunctionIndex is returned for the caller to
-- keep on its ref node.
compileDefer :: KeyedExpr -> ICM (TemplateId, FunctionIndex)
compileDefer = \case
  Just keys :< CompiledExprS (DeferSF fi body) ->
    State.gets (Map.lookup (dkExact keys) . icTplByKey) >>= \case
      Just tid -> do
        note "template-reused"
        pure (tid, fi)
      Nothing -> do
        (ext, nodes, labels) <- isolatedNet (compileBody body)
        tid <- State.gets icNextTpl
        State.modify' $ \st -> st
          { icNextTpl = tid + 1
          , icTemplates = IntMap.insert tid
              (Template nodes ext labels (forget body) (dkHash keys))
              (icTemplates st)
          , icTplByKey = Map.insert (dkExact keys) tid (icTplByKey st) }
        note "template-compiled"
        pure (tid, fi)
  _notDefer -> throwError $ ICInternal "compileDefer: not a keyed defer value"

-- | Build a body's net: allocate its env splitter tree, walk the term,
-- and wire the result to the boundary node.
compileBody :: KeyedExpr -> ICM Int
compileBody body = do
  ext <- newNode ICExt
  wires <- envWiring (Port ext 0) (envUsage (forget body))
  State.modify' $ \st -> st { icEnvQueue = wires }
  root <- compileTerm body
  State.gets icEnvQueue >>= \q ->
    unless (all null (Map.elems q)) . throwError $
      ICInternal "compileBody: env wires left over"
  connect (Port ext 1) root
  pure ext

-- | The ports producing each copy of one value. The incoming value is
-- delivered at @src@: to an eraser when no copy is needed, straight
-- through for one, through a dup chain otherwise.
envCopies :: Port -> Int -> ICM [Port]
envCopies src = \case
  0 -> do
    e <- newNode ICEra
    connect src (Port e 0)
    pure []
  1 -> pure [src]
  n -> do
    d <- newNode . ICDup =<< freshLabel
    connect src (Port d 0)
    rest <- envCopies (Port d 2) (n - 1)
    pure (Port d 1 : rest)

-- | Build the env splitter tree for one usage map: each used projection
-- path gets its own delivery wires, produced by descending the env value
-- through 'ICSplit' agents. Duplication happens only where a path is
-- directly used more than once, or used and also descended past (the
-- analyzer's whole-and-part contraction); components no used path needs
-- are erased at the highest point.
envWiring :: Port -> Map [Step] Int -> ICM (Map [Step] [Port])
envWiring src usage = do
  let direct = Map.findWithDefault 0 [] usage
      sub s = Map.fromList
        [ (ps, c) | (s' : ps, c) <- Map.toList usage, s' == s ]
      subL = sub SL
      subR = sub SR
      descending = not (Map.null subL && Map.null subR)
  copies <- envCopies src (direct + if descending then 1 else 0)
  let (directWires, rest) = splitAt direct copies
      here = if direct > 0
        then Map.singleton [] directWires
        else Map.empty
  if not descending
    then pure here
    else case rest of
      [descendWire] -> do
        sp <- newNode ICSplit
        connect (Port sp 0) descendWire
        wl <- envWiring (Port sp 1) subL
        wr <- envWiring (Port sp 2) subR
        pure $ Map.unions
          [here, Map.mapKeys (SL :) wl, Map.mapKeys (SR :) wr]
      _ -> throwError $ ICInternal "envWiring: descend wire missing"

-- | Take the next delivery wire for one env path.
takeEnvWire :: [Step] -> ICM Port
takeEnvWire path = State.gets (Map.lookup path . icEnvQueue) >>= \case
  Just (c : rest) -> do
    State.modify' $ \st ->
      st { icEnvQueue = Map.insert path rest (icEnvQueue st) }
    pure c
  _exhausted -> throwError . ICInternal $
    "compileTerm: no env wire for path " <> showSteps path

-- | Compile one term, returning the port its value is delivered from.
-- Projection chains applied directly to Env compile to nothing: their
-- component arrives pre-split on its path's wire.
compileTerm :: KeyedExpr -> ICM Port
compileTerm t = case unwrap t of
  CompiledExprB ZeroSF -> value ICZero
  CompiledExprB (PairSF a b)
    | Just d <- constData t -> do
        note "const-data"
        State.modify' $ \st -> st { icConstants =
          let Resources n m _ = icConstants st
              Resources n' m' _ = dataStorage d
          in Resources (n + n') (m + m') 0 }
        value (ICData (DataKnown d))
    | otherwise -> do
    p <- newNode ICPair
    connect (Port p 1) =<< compileTerm a
    connect (Port p 2) =<< compileTerm b
    pure (Port p 0)
  CompiledExprS EnvSF -> takeEnvWire []
  CompiledExprS (SetEnvSF x) -> consumer ICSetEnv x
  CompiledExprS (LeftSF x) -> case envPathOf (forget t) of
    Just path -> takeEnvWire path
    Nothing   -> consumer ICLeft x
  CompiledExprS (RightSF x) -> case envPathOf (forget t) of
    Just path -> takeEnvWire path
    Nothing   -> consumer ICRight x
  CompiledExprS GateSF -> value ICGate
  CompiledExprS (DeferSF _ _) -> do
    (tid, fi) <- compileDefer t
    value (ICRef tid fi)
  CompiledExprA AbortF -> value ICAbort
  CompiledExprA (AbortedF m) -> do
    a <- newNode ICAborted
    connect (Port a 1) =<< compileData m
    pure (Port a 0)
  where
    value k = (`Port` 0) <$> newNode k
    consumer k x = do
      n <- newNode k
      connect (Port n 0) =<< compileTerm x
      pure (Port n 1)

-- | A closed constant: a subterm made only of pairs and zeros. Held as
-- one 'ICData' node, so copying or erasing it costs one interaction and
-- only the parts something takes apart are ever built.
constData :: KeyedExpr -> Maybe BasicExpr
constData t = case unwrap t of
  CompiledExprB ZeroSF       -> Just ZeroB
  CompiledExprB (PairSF a b) -> PairB <$> constData a <*> constData b
  _notConst                  -> Nothing

compileData :: BasicExpr -> ICM Port
compileData = cata $ \case
  ZeroSF -> (`Port` 0) <$> newNode ICZero
  PairSF ma mb -> do
    p <- newNode ICPair
    connect (Port p 1) =<< ma
    connect (Port p 2) =<< mb
    pure (Port p 0)

-- | Splice a fresh copy of a template into the net: @envSrc@ produces the
-- env value, @resultDst@ awaits the body's value. Dup labels are offset by
-- a fresh base, so every instantiation's dups are distinct from every
-- other's — the discipline the EAL certificate makes sound.
instantiate :: TemplateId -> Port -> Port -> ICM ()
instantiate tid envSrc resultDst = do
  tpl <- State.gets (IntMap.lookup tid . icTemplates) >>= \case
    Just tpl -> pure tpl
    Nothing  -> throwError . ICInternal $ "no template " <> show tid
  base <- State.gets icNextLabel
  dbg $ "instantiate tpl" <> show tid <> " labels@" <> show base
  State.modify' $ \st -> st { icNextLabel = base + tplLabels tpl }
  copies <- fmap IntMap.fromList
    . forM [ (n, nd) | (n, nd) <- IntMap.toList (tplNodes tpl)
                     , n /= tplExt tpl ] $ \(n, nd) ->
      (,) n <$> newNode (relabel base (nodeKind nd))
  let translate (Port n s)
        | n == tplExt tpl = pure $ if s == 0 then envSrc else resultDst
        | otherwise = case IntMap.lookup n copies of
            Just m  -> pure (Port m s)
            Nothing -> throwError $ ICInternal "instantiate: unmapped node"
  -- copy each template wire once (each wire appears from both ends)
  forM_ (IntMap.toList (tplNodes tpl)) $ \(n, nd) ->
    forM_ (IntMap.toList (nodePorts nd)) $ \(s, q) ->
      when (Port n s < q) $ do
        p' <- translate (Port n s)
        q' <- translate q
        connect p' q'
  where
    relabel base = \case
      ICDup l -> ICDup (base + l)
      k       -> k

-- * Reduction

-- | Fire active pairs until quiescence. Entries whose nodes were consumed
-- by earlier interactions are skipped. Parked instantiations fire one at
-- a time, and only when no eager work remains, so erasure has drained as
-- far as it can before each demand check; the FIFO order keeps a
-- diverging dead application from starving the parked pair whose firing
-- would place the eraser that kills it.
reduce :: ICM ()
reduce = nextPair >>= \case
  Nothing -> pure ()
  Just next -> popNext next >> fireNext next >> reduce

-- | A pair the scheduler has chosen to fire: eager, or a parked
-- instantiation.
data Next = Eager Int Int | Parked Int Int
  deriving (Eq, Show)

-- | The pair 'reduce' fires next, left at the head of its queue: eager
-- pairs first, newest first; parked ones only once no eager work remains,
-- oldest first. Entries gone stale on the way, because other interactions
-- consumed their nodes, are dropped here exactly as 'reduce' drops them.
-- 'Telomare.IC.Space' schedules through this too, so its walk fires pairs
-- in the runtime's order by construction.
nextPair :: ICM (Maybe Next)
nextPair = State.gets icActive >>= \case
  ((a, b) : _) -> livePair a b >>= \case
    True  -> pure (Just (Eager a b))
    False -> popNext (Eager a b) >> nextPair
  [] -> State.gets (Seq.viewl . icParked) >>= \case
    Seq.EmptyL -> pure Nothing
    (a, b) Seq.:< _ -> livePair a b >>= \case
      True  -> pure (Just (Parked a b))
      False -> popNext (Parked a b) >> nextPair

-- | Take the chosen pair off the head of its queue.
popNext :: Next -> ICM ()
popNext = \case
  Eager _ _ -> State.modify' $ \st -> popped st { icActive = drop 1 (icActive st) }
  Parked _ _ -> State.modify' $ \st -> popped st { icParked = Seq.drop 1 (icParked st) }
  where popped = account (\r -> r { resWork = resWork r - 1 })

fireNext :: Next -> ICM ()
fireNext = \case
  Eager a b  -> fire a b
  Parked a b -> fireParked a b

-- | Whether both nodes still exist and still face each other principally;
-- queue entries go stale when other interactions consume their nodes.
livePair :: Int -> Int -> ICM Bool
livePair a b = do
  live <- State.gets $ \st ->
    IntMap.member a (icNodes st) && IntMap.member b (icNodes st)
  if not live then pure False else do
    pa <- peer (Port a 0)
    pb <- peer (Port b 0)
    pure (pa == Port b 0 && pb == Port a 0)

-- | Fire a parked instantiation. Parking exists to give erasure time to
-- reach a dead application before its template is spliced in: by the
-- time no eager work remains, a discarded result has materialized as an
-- eraser sitting on the apply's result wire, and the application then
-- collapses without instantiating — the code pointer and the demanding
-- eraser are consumed, and the operand is handed to erasure, which
-- proceeds by the ordinary rules (the guided 'eraRegion' path included).
-- The check is demand-negative (collapse only what is provably dead),
-- not demand-positive: an apply whose result faces anything else still
-- fires speculatively. That residual speculation is safe for every body
-- this runtime can run — 'Telomare.EAL.cgSpeculatable' is False only for
-- bodies still carrying unsized recursion oracles, and sizing has
-- resolved those before any code reaches 'CompiledExpr'.
fireParked :: Int -> Int -> ICM ()
fireParked a b = do
  ka <- kindOf a
  let (n, m) = case ka of
        ICApply   -> (a, b)
        _refFirst -> (b, a)
  r <- peer (Port n 2)
  discarded <- case r of
    Port e 0 -> kindOf e >>= \case
      ICEra      -> pure (Just e)
      _notEraser -> pure Nothing
    _auxPort -> pure Nothing
  case discarded of
    Just e -> do
      spend "apply-erased"
      opnd <- peer (Port n 1)
      deleteNode n >> deleteNode m
      connect (Port e 0) opnd
    Nothing -> fire n m

fire :: Int -> Int -> ICM ()
fire a b = demandedData a b >>= \case
  Just (n, DataKnown e) -> revealData n (knownParts e) >> fire a b
  Just (_, DataPart p) -> throwError . ICInternal $
    "a symbolic input part (path " <> show p <> ") reached a concrete run"
  Nothing -> fireRule a b

-- | The data node of this pair whose shape its consumer needs before the
-- pair can fire. Erasing or copying data needs no shape.
demandedData :: Int -> Int -> ICM (Maybe (Int, DataSrc))
demandedData a b = do
  ka <- kindOf a
  kb <- kindOf b
  pure $ case (ka, kb) of
    (ICData s, k) | demandsShape k -> Just (a, s)
    (k, ICData s) | demandsShape k -> Just (b, s)
    _noDemand                      -> Nothing
  where
    demandsShape = \case
      ICSetEnv     -> True
      ICApply      -> True
      ICScrut      -> True
      ICScrutAbort -> True
      ICLeft       -> True
      ICRight      -> True
      ICSplit      -> True
      _noShape     -> False

-- | The parts of a known data value: Nothing for Zero.
knownParts :: BasicExpr -> Maybe (DataSrc, DataSrc)
knownParts = \case
  PairB a b -> Just (DataKnown a, DataKnown b)
  _zero     -> Nothing

-- | Take a data node apart one layer, in place: it becomes the Zero or the
-- Pair it is, and a pair's parts become data nodes of their own. Its
-- principal wire is untouched, so the consumer that demanded it then fires
-- by the ordinary rules. Not an interaction: the rule that follows is.
revealData :: Int -> Maybe (DataSrc, DataSrc) -> ICM ()
revealData n parts = do
  note "data-reveal"
  State.modify' $ \st -> st { icNodes = IntMap.adjust
    (\nd -> nd { nodeKind = maybe ICZero (const ICPair) parts }) n (icNodes st) }
  forM_ parts $ \(l, r) -> forM_ [(1, l), (2, r)] $ \(slot, src) -> do
    c <- newNode (ICData src)
    connect (Port n slot) (Port c 0)

fireRule :: Int -> Int -> ICM ()
fireRule a b = do
  ka <- kindOf a
  kb <- kindOf b
  dbg $ "fire " <> show a <> ":" <> show ka <> " ~ " <> show b <> ":" <> show kb
  case rule a ka b kb of
    Just act -> act
    Nothing -> case rule b kb a ka of
      Just act -> act
      Nothing -> throwError . ICInternal $
        "no interaction rule for " <> show ka <> " meeting " <> show kb

valueKind :: ICKind -> Bool
valueKind = \case
  ICZero    -> True
  ICPair    -> True
  ICRef {}  -> True
  ICGate    -> True
  ICAbort   -> True
  ICAborted -> True
  ICStuckV _ -> True
  ICData _  -> True
  _notValue -> False

-- | An ill-shaped interaction: the consumer's result becomes a stuck value
-- and the listed leftover operands are erased. Stuckness must be a value
-- rather than a thrown error because the reference evaluator is lazy — a
-- stuck redex whose result is discarded is no error at all there, and the
-- eager net must agree observationally.
stuckAt :: String -> String -> Port -> [Port] -> ICM ()
stuckAt name msg r extras = do
  spend name
  sv <- newNode (ICStuckV msg)
  connect (Port sv 0) r
  forM_ extras $ \p -> do
    era <- newNode ICEra
    connect (Port era 0) p

-- | The oriented rule table: @rule n nk m mk@ fires the interaction with
-- @n@ in the first role, or Nothing if this orientation has no rule (the
-- caller then tries the flip). Every rule gathers the peers it needs
-- before deleting or rewiring anything.
rule :: Int -> ICKind -> Int -> ICKind -> Maybe (ICM ())
rule n nk m mk = case (nk, mk) of
  -- SetEnv x: x has become a (function, env) pair; go apply the function
  (ICSetEnv, ICPair) -> Just $ do
    spend "setenv-pair"
    f <- peer (Port m 1)
    e <- peer (Port m 2)
    r <- peer (Port n 1)
    deleteNode n >> deleteNode m
    ap <- newNode ICApply
    connect (Port ap 0) f
    connect (Port ap 1) e
    connect (Port ap 2) r
  (ICSetEnv, ICAborted) -> Just $ passThrough "setenv-aborted" n 1 m
  (ICSetEnv, ICStuckV _) -> Just $ passThrough "setenv-stuck" n 1 m
  (ICSetEnv, _) | valueKind mk -> Just $ do
    r <- peer (Port n 1)
    deleteNode n >> deleteNode m
    stuckAt "setenv-nonpair"
      ("SetEnv operand is " <> show mk <> ", not a pair") r []
  -- function dispatch, one rule per applicable head
  (ICApply, ICRef tid _) -> Just $ do
    spend "apply-ref"
    e <- peer (Port n 1)
    r <- peer (Port n 2)
    deleteNode n >> deleteNode m
    instantiate tid e r
  (ICApply, ICGate) -> Just $ awaitShape "apply-gate" n m ICScrut
  (ICApply, ICAbort) -> Just $ awaitShape "apply-abort" n m ICScrutAbort
  (ICApply, ICAborted) -> Just $ passApplication "apply-aborted" n m
  (ICApply, ICStuckV _) -> Just $ passApplication "apply-stuck" n m
  (ICApply, _) | valueKind mk -> Just $ do
    shape <- describeValue 6 m
    e <- peer (Port n 1)
    r <- peer (Port n 2)
    comps <- case mk of
      ICPair -> traverse (peer . Port m) [1, 2]
      _      -> pure []
    deleteNode n >> deleteNode m
    stuckAt "apply-nonfunction"
      ("applied value is " <> show mk <> ", not a function: " <> shape)
      r (e : comps)
  -- gate scrutinee arrived: yield the matching selector defer
  (ICScrut, ICZero) -> Just $
    selectZero "scrut-zero" n m leftSelTpl leftSelFi
  (ICScrut, ICPair) -> Just $ do
    spend "scrut-pair"
    la <- peer (Port m 1)
    rb <- peer (Port m 2)
    r <- peer (Port n 1)
    deleteNode n >> deleteNode m
    el <- newNode ICEra
    er <- newNode ICEra
    connect (Port el 0) la
    connect (Port er 0) rb
    deliverSelector rightSelTpl rightSelFi r
  (ICScrut, ICAborted) -> Just $ passThrough "scrut-aborted" n 1 m
  (ICScrut, ICStuckV _) -> Just $ passThrough "scrut-stuck" n 1 m
  (ICScrut, _) | valueKind mk -> Just $ do
    r <- peer (Port n 1)
    deleteNode n >> deleteNode m
    stuckAt "scrut-nondata"
      ("gate scrutinee is " <> show mk <> ", not data") r []
  -- abort message arrived: Zero means carry on as the identity
  (ICScrutAbort, ICZero) -> Just $
    selectZero "abort-zero" n m idSelTpl idSelFi
  (ICScrutAbort, ICPair) -> Just $ do
    spend "abort-pair"
    r <- peer (Port n 1)
    deleteNode n
    ab <- newNode ICAborted
    connect (Port ab 1) (Port m 0) -- the message pair survives underneath
    connect (Port ab 0) r
  (ICScrutAbort, ICAborted) -> Just $ passThrough "abort-aborted" n 1 m
  (ICScrutAbort, ICStuckV _) -> Just $ passThrough "abort-stuck" n 1 m
  (ICScrutAbort, _) | valueKind mk -> Just $ do
    r <- peer (Port n 1)
    deleteNode n >> deleteNode m
    stuckAt "abort-nondata"
      ("abort message is " <> show mk <> ", not data") r []
  -- projections
  (ICLeft, ICZero) -> Just $ passThrough "left-zero" n 1 m
  (ICLeft, ICPair) -> Just $ projectPair "left-pair" n m 1 2
  (ICLeft, ICAborted) -> Just $ passThrough "left-aborted" n 1 m
  (ICLeft, ICStuckV _) -> Just $ passThrough "left-stuck" n 1 m
  (ICLeft, _) | valueKind mk -> Just $ projectNonPair "left-nonpair" n m mk
  (ICRight, ICZero) -> Just $ passThrough "right-zero" n 1 m
  (ICRight, ICPair) -> Just $ projectPair "right-pair" n m 2 1
  (ICRight, ICAborted) -> Just $ passThrough "right-aborted" n 1 m
  (ICRight, ICStuckV _) -> Just $ passThrough "right-stuck" n 1 m
  (ICRight, _) | valueKind mk -> Just $ projectNonPair "right-nonpair" n m mk
  -- env splitting: both components of a pair delivered in one interaction,
  -- with nothing duplicated and nothing erased. Every other case behaves
  -- exactly as a Left and a Right projection of the same value would.
  (ICSplit, ICPair) -> Just $ do
    spend "split-pair"
    la <- peer (Port m 1)
    rb <- peer (Port m 2)
    cl <- peer (Port n 1)
    cr <- peer (Port n 2)
    deleteNode n >> deleteNode m
    connect la cl
    connect rb cr
  -- both projections of Zero are Zero
  (ICSplit, ICZero) -> Just $ do
    spend "split-zero"
    cl <- peer (Port n 1)
    cr <- peer (Port n 2)
    deleteNode n >> deleteNode m
    forM_ [cl, cr] $ \c -> do
      zv <- newNode ICZero
      connect (Port zv 0) c
  -- an aborted value passes through both projections, sharing its message
  (ICSplit, ICAborted) -> Just $ do
    spend "split-aborted"
    cl <- peer (Port n 1)
    cr <- peer (Port n 2)
    msg <- peer (Port m 1)
    deleteNode n >> deleteNode m
    dm <- newNode . ICDup =<< freshLabel
    connect (Port dm 0) msg
    forM_ [(cl, 1), (cr, 2)] $ \(c, s) -> do
      ab <- newNode ICAborted
      connect (Port ab 1) (Port dm s)
      connect (Port ab 0) c
  (ICSplit, ICStuckV msg) -> Just $ do
    spend "split-stuck"
    cl <- peer (Port n 1)
    cr <- peer (Port n 2)
    deleteNode n >> deleteNode m
    forM_ [cl, cr] $ \c -> do
      sv <- newNode (ICStuckV msg)
      connect (Port sv 0) c
  (ICSplit, _) | valueKind mk -> Just $ do
    spend "split-nonpair"
    cl <- peer (Port n 1)
    cr <- peer (Port n 2)
    deleteNode n >> deleteNode m
    forM_ [cl, cr] $ \c -> do
      sv <- newNode . ICStuckV $
        "projection target is " <> show mk <> ", not a pair"
      connect (Port sv 0) c
  -- erasure. A pair whose head is a code pointer with a published capture
  -- layout is a closure the plan knows the shape of: drop its materialized
  -- skeleton directly ('eraRegion') instead of unfolding the generic
  -- eraser cascade one interaction at a time — the symmetric twin of the
  -- guided duplication rule below, and the common fate of the closures a
  -- gate's unselected branch carries.
  (ICEra, ICPair) -> Just $ do
    la <- peer (Port m 1)
    dupPlanFor la >>= \case
      Just shape -> do
        spend "era-closure"
        rb <- peer (Port m 2)
        deleteNode n >> deleteNode m
        eraRegion CapCode la
        eraRegion shape rb
      Nothing -> do
        spend "era-pair"
        rb <- peer (Port m 2)
        deleteNode n >> deleteNode m
        el <- newNode ICEra
        er <- newNode ICEra
        connect (Port el 0) la
        connect (Port er 0) rb
  (ICEra, ICAborted) -> Just $ do
    spend "era-aborted"
    msg <- peer (Port m 1)
    deleteNode n >> deleteNode m
    era <- newNode ICEra
    connect (Port era 0) msg
  (ICEra, _) | valueKind mk -> Just $ do
    spend "era-leaf"
    deleteNode n >> deleteNode m
  -- duplication. A pair whose head is a code pointer with a published
  -- capture layout is a closure the plan knows the shape of: copy its
  -- materialized skeleton directly ('dupRegion') instead of unfolding
  -- the generic fan cascade one interaction at a time.
  (ICDup l, ICPair) -> Just $ do
    la <- peer (Port m 1)
    dupPlanFor la >>= \case
      Just shape -> do
        spend "dup-closure"
        c1 <- peer (Port n 1)
        c2 <- peer (Port n 2)
        rb <- peer (Port m 2)
        deleteNode n >> deleteNode m
        (f1, f2) <- dupRegion l CapCode la
        (e1, e2) <- dupRegion l shape rb
        p1 <- newNode ICPair
        p2 <- newNode ICPair
        connect (Port p1 1) f1
        connect (Port p1 2) e1
        connect (Port p2 1) f2
        connect (Port p2 2) e2
        connect (Port p1 0) c1
        connect (Port p2 0) c2
      Nothing -> do
        spend "dup-pair"
        c1 <- peer (Port n 1)
        c2 <- peer (Port n 2)
        rb <- peer (Port m 2)
        deleteNode n >> deleteNode m
        p1 <- newNode ICPair
        p2 <- newNode ICPair
        dl <- newNode (ICDup l)
        dr <- newNode (ICDup l)
        connect (Port dl 0) la
        connect (Port dr 0) rb
        connect (Port p1 1) (Port dl 1)
        connect (Port p1 2) (Port dr 1)
        connect (Port p2 1) (Port dl 2)
        connect (Port p2 2) (Port dr 2)
        connect (Port p1 0) c1
        connect (Port p2 0) c2
  (ICDup l, ICAborted) -> Just $ do
    spend "dup-aborted"
    c1 <- peer (Port n 1)
    c2 <- peer (Port n 2)
    msg <- peer (Port m 1)
    deleteNode n >> deleteNode m
    a1 <- newNode ICAborted
    a2 <- newNode ICAborted
    dm <- newNode (ICDup l)
    connect (Port dm 0) msg
    connect (Port a1 1) (Port dm 1)
    connect (Port a2 1) (Port dm 2)
    connect (Port a1 0) c1
    connect (Port a2 0) c2
  (ICDup l, ICDup l')
    -- the two halves of one dup meet again: the value passed through
    | l == l' -> Just $ do
        spend "dup-annihilate"
        a1 <- peer (Port n 1)
        a2 <- peer (Port n 2)
        b1 <- peer (Port m 1)
        b2 <- peer (Port m 2)
        deleteNode n >> deleteNode m
        connect a1 b1
        connect a2 b2
    -- unrelated dups commute (the standard square)
    | otherwise -> Just $ do
        spend "dup-commute"
        a1 <- peer (Port n 1)
        a2 <- peer (Port n 2)
        b1 <- peer (Port m 1)
        b2 <- peer (Port m 2)
        deleteNode n >> deleteNode m
        m1 <- newNode (ICDup l')
        m2 <- newNode (ICDup l')
        n1 <- newNode (ICDup l)
        n2 <- newNode (ICDup l)
        connect (Port m1 0) a1
        connect (Port m2 0) a2
        connect (Port n1 0) b1
        connect (Port n2 0) b2
        connect (Port m1 1) (Port n1 1)
        connect (Port m1 2) (Port n2 1)
        connect (Port m2 1) (Port n1 2)
        connect (Port m2 2) (Port n2 2)
  (ICDup _, _) | valueKind mk -> Just $ do
    -- leaf values (Zero, refs, gates, aborts) copy by node duplication;
    -- for a ref that is a pointer copy, the code-table payoff
    spend "dup-leaf"
    c1 <- peer (Port n 1)
    c2 <- peer (Port n 2)
    deleteNode n >> deleteNode m
    v1 <- newNode mk
    v2 <- newNode mk
    connect (Port v1 0) c1
    connect (Port v2 0) c2
  _noRule -> Nothing

-- | The kind at a delivery port, when it is a materialized value (its
-- principal faces us); Nothing while the wire still awaits a computation.
materialValue :: Port -> ICM (Maybe ICKind)
materialValue (Port node slot)
  | slot /= 0 = pure Nothing
  | otherwise = do
      k <- kindOf node
      pure $ if valueKind k then Just k else Nothing

-- | The capture layout of a closure, when the pair's head is a
-- materialized code pointer whose hash has published guidance — the plan
-- both the guided duplication and the guided erasure rules act on.
dupPlanFor :: Port -> ICM (Maybe CapShape)
dupPlanFor la = materialValue la >>= \case
  Just (ICRef tid _) -> State.gets (IntMap.lookup tid . icTemplates) >>= \case
    Just tpl -> State.gets (Map.lookup (tplHash tpl) . icGuidance)
    Nothing  -> pure Nothing
  _notCode -> pure Nothing

-- | Duplicate the value region at a delivery port by its capture shape:
-- structurally copy what is already a materialized constructor (pairs,
-- zeros) or code pointer, and place a fan — with the plan's label, as the
-- generic cascade would — at every frontier: unmaterialized values,
-- shared or foreign nodes, and positions the shape does not vouch for.
-- Correct for ANY shape: the shape only chooses where copying is
-- attempted, the materialization checks decide, so wrong guidance can
-- cost performance but never meaning.
dupRegion :: Label -> CapShape -> Port -> ICM (Port, Port)
dupRegion l shape p = materialValue p >>= \mk -> case (shape, mk) of
  (CapData, Just ICZero)       -> copyLeaf
  (CapData, Just ICPair)       -> copyPair CapData CapData
  (CapCode, Just (ICRef _ _))  -> copyLeaf
  (CapPair s1 s2, Just ICPair) -> copyPair s1 s2
  _frontier -> do
    d <- newNode (ICDup l)
    connect (Port d 0) p
    pure (Port d 1, Port d 2)
  where
    n = portNode p
    copyLeaf = do
      k <- kindOf n
      deleteNode n
      note "dup-plan-copy"
      v1 <- newNode k
      v2 <- newNode k
      pure (Port v1 0, Port v2 0)
    copyPair s1 s2 = do
      a <- peer (Port n 1)
      b <- peer (Port n 2)
      deleteNode n
      note "dup-plan-copy"
      (a1, a2) <- dupRegion l s1 a
      (b1, b2) <- dupRegion l s2 b
      p1 <- newNode ICPair
      p2 <- newNode ICPair
      connect (Port p1 1) a1
      connect (Port p1 2) b1
      connect (Port p2 1) a2
      connect (Port p2 2) b2
      pure (Port p1 0, Port p2 0)

-- | Erase the value region at a delivery port by its capture shape:
-- delete outright what is already a materialized constructor (pairs,
-- zeros) or code pointer, and place an eraser — as the generic cascade
-- would — at every frontier: unmaterialized values, shared or foreign
-- nodes, and positions the shape does not vouch for. The same safety
-- argument as 'dupRegion': the shape only chooses where deletion is
-- attempted, the materialization checks decide, so wrong guidance can
-- cost performance but never meaning.
eraRegion :: CapShape -> Port -> ICM ()
eraRegion shape p = materialValue p >>= \mk -> case (shape, mk) of
  (CapData, Just ICZero)       -> dropLeaf
  (CapData, Just ICPair)       -> dropPair CapData CapData
  (CapCode, Just (ICRef _ _))  -> dropLeaf
  (CapPair s1 s2, Just ICPair) -> dropPair s1 s2
  _frontier -> do
    e <- newNode ICEra
    connect (Port e 0) p
  where
    n = portNode p
    dropLeaf = do
      deleteNode n
      note "era-plan-drop"
    dropPair s1 s2 = do
      a <- peer (Port n 1)
      b <- peer (Port n 2)
      deleteNode n
      note "era-plan-drop"
      eraRegion s1 a
      eraRegion s2 b

-- | A bounded structural sketch of the value at a node, for error
-- messages: pairs descend, leaves print their kind, in-flight machinery
-- prints as itself.
describeValue :: Int -> Int -> ICM String
describeValue depth n
  | depth <= 0 = pure "..."
  | otherwise = kindOf n >>= \case
      ICZero -> pure "0"
      ICPair -> do
        a <- peer (Port n 1)
        b <- peer (Port n 2)
        sa <- describeValue (depth - 1) (portNode a)
        sb <- describeValue (depth - 1) (portNode b)
        pure $ "(" <> sa <> "," <> sb <> ")"
      ICRef t _ -> pure $ "ref" <> show t
      ICData _ -> pure "data"
      ICDup l  -> do
        src <- peer (Port n 0)
        s <- describeValue (depth - 1) (portNode src)
        pure $ "dup" <> show l <> "[" <> s <> "]"
      k        -> pure (show k)

-- | Forward the value @m@ to the consumer @n@'s result slot, deleting the
-- consumer: projections of Zero, and Aborted values passing through.
passThrough :: String -> Int -> Int -> Int -> ICM ()
passThrough name n slot m = do
  spend name
  r <- peer (Port n slot)
  deleteNode n
  connect (Port m 0) r

-- | A poisoned application head survives; its unused argument is erased.
passApplication :: String -> Int -> Int -> ICM ()
passApplication name n m = do
  spend name
  e <- peer (Port n 1)
  r <- peer (Port n 2)
  deleteNode n
  era <- newNode ICEra
  connect (Port era 0) e
  connect (Port m 0) r

-- | Hand a reserved selector defer to the waiting port.
deliverSelector :: TemplateId -> FunctionIndex -> Port -> ICM ()
deliverSelector tid fi r = do
  sel <- newNode (ICRef tid fi)
  connect (Port sel 0) r

-- | A gate or abort awaiting its operand's shape met Zero: both nodes go
-- and the matching selector defer takes their place.
selectZero :: String -> Int -> Int -> TemplateId -> FunctionIndex -> ICM ()
selectZero name n m tid fi = do
  spend name
  r <- peer (Port n 1)
  deleteNode n >> deleteNode m
  deliverSelector tid fi r

-- | A projection met a value that is not a pair.
projectNonPair :: String -> Int -> Int -> ICKind -> ICM ()
projectNonPair name n m mk = do
  r <- peer (Port n 1)
  deleteNode n >> deleteNode m
  stuckAt name ("projection target is " <> show mk <> ", not a pair") r []

-- | An applied gate or abort must inspect its operand's shape: replace the
-- apply with a shape-awaiting node facing the operand.
awaitShape :: String -> Int -> Int -> ICKind -> ICM ()
awaitShape name n m k = do
  spend name
  e <- peer (Port n 1)
  r <- peer (Port n 2)
  deleteNode n >> deleteNode m
  sc <- newNode k
  connect (Port sc 0) e
  connect (Port sc 1) r

-- | Project one component of a pair to the consumer's result and erase the
-- other.
projectPair :: String -> Int -> Int -> Int -> Int -> ICM ()
projectPair name n m keep drop' = do
  spend name
  kept <- peer (Port m keep)
  dropped <- peer (Port m drop')
  r <- peer (Port n 1)
  deleteNode n >> deleteNode m
  era <- newNode ICEra
  connect (Port era 0) dropped
  connect kept r

-- * Readback

-- | Read a normalized value net back into syntax. A ref reads back as the
-- defer of its template's body under its own site's index, so results
-- compare equal to the reference evaluator's (defer equality is by index)
-- even when sites share a template.
readback :: Port -> ICM CompiledExpr
readback (Port n _) = kindOf n >>= \case
  ICZero -> pure ZeroB
  ICPair -> PairB <$> (readback =<< peer (Port n 1))
                  <*> (readback =<< peer (Port n 2))
  ICRef tid fi -> State.gets (IntMap.lookup tid . icTemplates) >>= \case
    Just tpl -> pure . StuckEE $ DeferSF fi (tplBody tpl)
    Nothing  -> throwError . ICInternal $ "readback: no template " <> show tid
  ICGate -> pure GateB
  ICAbort -> pure AbortB
  ICAborted -> AbortEE . AbortedF <$> (readbackData =<< peer (Port n 1))
  ICData (DataKnown e) -> pure (cata dataTerm e)
  ICData (DataPart p) -> throwError . ICInternal $
    "readback: symbolic input part at path " <> show p
  -- a stuck value survived into demanded output: only now is it an error
  ICStuckV msg -> throwError $ ICStuck msg
  k -> throwError . ICStuck $ "result contains a non-value: " <> show k

-- | Abort messages are data; anything else truncates to Zero, mirroring
-- the reference evaluator's message truncation.
readbackData :: Port -> ICM BasicExpr
readbackData (Port n _) = kindOf n >>= \case
  ICPair -> PairB <$> (readbackData =<< peer (Port n 1))
                  <*> (readbackData =<< peer (Port n 2))
  ICZero    -> pure ZeroB
  ICData (DataKnown e) -> pure e
  _nonData  -> pure ZeroB

-- | A data value as a term.
dataTerm :: BasicExprF CompiledExpr -> CompiledExpr
dataTerm = \case
  ZeroSF     -> ZeroB
  PairSF a b -> PairB a b

-- * Entry points

-- | Reserved templates for the values the runtime itself mints: the gate
-- selectors and the abort continuation. Registered first, in this order.
-- (A user body equal to a selector's shares its template; the per-site
-- index on the ref keeps them apart observationally.)
leftSelTpl, rightSelTpl, idSelTpl :: TemplateId
leftSelTpl = 0
rightSelTpl = 1
idSelTpl = 2

leftSelFi, rightSelFi, idSelFi :: FunctionIndex
leftSelFi = toEnum leftGateInd
rightSelFi = toEnum rightGateInd
idSelFi = toEnum abortInd

setupSelectors :: ICM ()
setupSelectors = do
  (lt, _) <- compileDefer (keyDefers doLeft)
  (rt, _) <- compileDefer (keyDefers doRight)
  (it, _) <- compileDefer (keyDefers (deferB abortInd EnvB))
  unless ([lt, rt, it] == [leftSelTpl, rightSelTpl, idSelTpl])
    . throwError $ ICInternal "selector templates got unexpected ids"

defaultFuel :: Int
defaultFuel = 10 * 1000 * 1000

-- | Evaluate a closed term, also reporting how many interactions each rule
-- fired (the runtime's cost model).
icEvalDetailed :: Int -> CompiledExpr
               -> (Either ICError CompiledExpr, Map String Int)
icEvalDetailed = icEvalDetailedWith mempty

-- | 'icEvalDetailed' with per-hash capture layouts from the EAL pass
-- ('Telomare.EAL.ealCaptureLayouts') guiding closure duplication.
icEvalDetailedWith :: Map (Digest SHA256) CapShape -> Int -> CompiledExpr
                   -> (Either ICError CompiledExpr, Map String Int)
icEvalDetailedWith guidance fuel term =
  let (r, st) = icRunState guidance fuel term
  in (r, icStats st)

-- | Run a closed term to a finished net, returning the raw outcome and the
-- final state — the one entry point the others project from.
icRunState :: Map (Digest SHA256) CapShape -> Int -> CompiledExpr
           -> (Either ICError CompiledExpr, ICState)
icRunState guidance fuel term =
  State.runState (runExceptT go) (emptyState guidance fuel)
  where
    go = do
      unless (Map.null (envUsage term)) . throwError $
        ICStuck "unbound Env at top level"
      setupSelectors
      root <- newNode ICRoot
      p <- compileTerm (keyDefers term)
      connect (Port root 0) p
      reduce
      readback =<< peer (Port root 0)

-- | Evaluate with the default interaction budget.
icEvalIC :: CompiledExpr -> Either ICError CompiledExpr
icEvalIC = fst . icEvalDetailed defaultFuel

-- | Interpret a finished run under the reference evaluator's contract: an
-- Aborted value surviving anywhere in the result is an 'AbortRunTime'
-- (mirroring the reference checkError); runtime trouble maps onto
-- 'GenericRunTimeError'.
icOutcome :: Either ICError CompiledExpr -> Either RunTimeError CompiledExpr
icOutcome = \case
  Left e -> Left $ GenericRunTimeError ("IC runtime: " <> show e) ZeroB
  Right x -> case cata findError x of
    Just msg -> Left $ AbortRunTime msg
    Nothing  -> Right x
  where
    findError = \case
      AbortFW (AbortedF e) -> Just e
      x                    -> asum x

-- | Evaluate under the reference evaluator's contract ('icOutcome').
icEval :: CompiledExpr -> Either RunTimeError CompiledExpr
icEval = icOutcome . icEvalIC

-- | What one run cost, measured: the interactions spent against fuel, the
-- per-event counters (interaction rules and compile-time notes alike),
-- the net's peak storage (construction included) and the template table.
data ICCost = ICCost
  { costInteractions :: !Int
  , costEvents       :: Map String Int
  , costPeak         :: !Resources
  , costTemplates    :: !Resources
  } deriving (Eq, Show)

icCost :: ICState -> ICCost
icCost st = ICCost (icSpent st) (icStats st) (icPeak st) (templateStorage st)

-- | One guided run, reported for a driver: the outcome under the reference
-- contract and what the run cost. A run that fails still reports what it
-- cost up to the failure.
icRunReport :: Map (Digest SHA256) CapShape -> Int -> CompiledExpr
            -> (Either RunTimeError CompiledExpr, ICCost)
icRunReport guidance fuel term =
  let (r, st) = icRunState guidance fuel term
  in (icOutcome r, icCost st)

-- * Iterations: main applied to an input

-- | Build the net of one driver iteration, @main@ applied to a data input
-- ('Telomare.Machine.appB'), with the input as one node of the given kind;
-- returns the root. The term is compiled with a Zero standing in for the
-- input, and that node then takes the input's kind: a Zero, or the whole
-- input held as one 'ICData' node. Either way the input is one node, so
-- the net is built identically whatever the input is — which is what lets
-- 'Telomare.IC.Space' run the same construction for every input at once.
buildApplied :: CompiledExpr -> ICKind -> ICM Int
buildApplied mainTerm kind = do
  let term = appB mainTerm ZeroB
  unless (Map.null (envUsage term)) . throwError $
    ICStuck "unbound Env at top level"
  setupSelectors
  root <- newNode ICRoot
  p <- compileTerm (keyDefers term)
  connect (Port root 0) p
  -- appB main i = SetEnv (SetEnv (Pair twiddle (Pair i main)))
  outer <- expect ICSetEnv 1 =<< peer (Port root 0)
  inner <- expect ICSetEnv 1 =<< peer (Port outer 0)
  frame <- expect ICPair 0 =<< peer (Port inner 0)
  args <- expect ICPair 0 =<< peer (Port frame 2)
  slot <- expect ICZero 0 =<< peer (Port args 1)
  State.modify' $ \st -> st { icNodes = IntMap.adjust
    (\nd -> nd { nodeKind = kind }) slot (icNodes st) }
  pure root
  where
    expect k s (Port n s') = kindOf n >>= \k' ->
      if k' == k && s' == s then pure n else throwError . ICInternal $
        "buildApplied: expected " <> show k <> " at slot " <> show s
          <> ", found " <> show k' <> " at slot " <> show s'

-- | How a concrete input enters the net: Zero as itself, anything else
-- held whole until a consumer takes it apart.
inputKind :: BasicExpr -> ICKind
inputKind = \case
  ZeroB -> ICZero
  input -> ICData (DataKnown input)

-- | Run @main@ on one input, the way the driver's loop runs an iteration:
-- 'icRunState' of @appB main input@, except that the input is not built
-- into the net node by node but enters as one node and is taken apart only
-- as far as the program looks at it.
icRunApplied :: Map (Digest SHA256) CapShape -> Int -> CompiledExpr -> BasicExpr
             -> (Either ICError CompiledExpr, ICState)
icRunApplied guidance fuel mainTerm input =
  State.runState (runExceptT go) (emptyState guidance fuel)
  where
    go = do
      root <- buildApplied mainTerm (inputKind input)
      reduce
      readback =<< peer (Port root 0)

-- | 'icRunReport' for one iteration ('icRunApplied').
icRunAppliedReport :: Map (Digest SHA256) CapShape -> Int -> CompiledExpr
                   -> BasicExpr -> (Either RunTimeError CompiledExpr, ICCost)
icRunAppliedReport guidance fuel mainTerm input =
  let (r, st) = icRunApplied guidance fuel mainTerm input
  in (icOutcome r, icCost st)
