{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Whole-run logical storage bounds for a prepared IC program, over every
-- finite data input.
--
-- A /world/ is the runtime's own net in which some values are /regions/: an
-- @ICInput p@ node stands for an arbitrary finite Zero/Pair tree, the part
-- of the input at path @p@, of size @|p|@ ('Telomare.SpaceBound'); below the
-- root a region may also be the Zero that projecting a Zero yields, hence
-- @|p| + 1@. Everything else is fired by the runtime's own rules in the
-- runtime's own LIFO order. The analysis never reorders an interaction the
-- runtime would perform: the certified quantity, the peak of resident
-- agents, port entries and pending pairs, depends on that order.
--
-- A region meets a consumer in one of three ways.
--
--   * Erasure and copying are summarized. An erasure cascade over a data
--     tree is atomic under LIFO, so it costs one step. A copy cascade is
--     not: the runtime's consumers of the copies run before the cascade
--     finishes, so an eraser standing in for the cascade keeps the source
--     region resident, at the cascade's own position in the worklist, until
--     that position is reached. Every live region carries an allowance
--     covering its tree and any cascade's intermediates: 4|p| agents, 12|p|
--     port entries and 4|p| pending pairs.
--   * Projections and applications reveal the region in place as a pair of
--     two regions, without committing the world. Each of those rules' pair
--     case dominates its Zero case in storage, and a region already
--     includes Zero among its trees.
--   * A gate scrutinee or abort message selects different code by shape.
--     The world forks: one child commits the path to Zero, the other to
--     Pair, and every later test of that path in a child, on any copy of
--     the region, dispatches without forking. A path under a committed Zero
--     is Zero; a path above a committed Pair is a pair.
--
-- The bound is the maximum, over every world and every transition, of the
-- peak the runtime's counters recorded since the live regions last changed,
-- plus the allowance of the regions live during that stretch. Budgets are
-- explicit: exhaustion is 'Unknown', never a partial bound.
--
-- Worlds never rejoin, so a program whose control depends on many
-- independent input parts has a number of worlds exponential in that count
-- and exhausts the budget.
module Telomare.IC.Space where

import Control.Monad (forM_, when)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import qualified Control.Monad.State.Strict as State
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IM
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Numeric.Natural (Natural)
import Telomare.IC
import Telomare.IR.Base (BasicExpr, pattern PairB, pattern ZeroB)
import Telomare.SpaceBound

-- | A certificate bounds every resource for every finite input.
data AnalysisOutcome = Established (Resources SpaceBound) | Unknown String
  deriving (Eq, Show)

-- | Interactions over all worlds together, and world forks.
data AnalysisBudget = AnalysisBudget Int Int

defaultAnalysisBudget :: AnalysisBudget
defaultAnalysisBudget = AnalysisBudget 20000000 100000

-- | What the analysis did, for calibration and tests.
data AnalysisStats = AnalysisStats
  { statTransitions :: !Int
  , statForks       :: !Int
  , statWorlds      :: !Int
  } deriving (Eq, Show)

-- | The size of every part of a finite input, by path. A part under a Zero
-- is absent and has size 0.
inputSizes :: BasicExpr -> Map Integer Natural
inputSizes = go 0
  where
    go :: Integer -> BasicExpr -> Map Integer Natural
    go p ZeroB = Map.singleton p 1
    go p (PairB a b) =
      let l = go (2 * p + 1) a
          r = go (2 * p + 2) b
      in Map.insert p (1 + l Map.! (2 * p + 1) + r Map.! (2 * p + 2)) (l <> r)
    go _ _ = error "inputSizes: not a finite data input"

-- | Whether a measured peak is within the certificate at its input.
-- 'Unknown' never validates.
certificateCovers :: BasicExpr -> ICSpaceStats -> AnalysisOutcome -> Bool
certificateCovers input stats (Established bounds) =
  and (liftA2 (\actual bound -> sbEvaluate size bound >= actual) (spacePeak stats) bounds)
  where size p = Map.findWithDefault 0 p (inputSizes input)
certificateCovers _ _ (Unknown _) = False

-- * Worlds

data World = World
  { worldNet    :: !ICState
  , worldShapes :: !(Map Integer Bool)
    -- ^ committed shapes: True for a pair
  , worldLoad   :: !(Map Integer Int)
    -- ^ live regions per path
  , worldBounds :: !(Resources SpaceBound)
    -- ^ the maximum over this world's past, its ancestors' included
  }

type WM = ExceptT ICError (State.State World)

runNet :: ICM a -> ICState -> (Either ICError a, ICState)
runNet action = State.runState (runExceptT action)

runWorld :: WM a -> World -> (Either ICError a, World)
runWorld action = State.runState (runExceptT action)

net :: ICM a -> WM a
net action = do
  w <- State.get
  let (r, st) = runNet action (worldNet w)
  State.put w { worldNet = st }
  either throwError pure r

-- | Close the current stretch: charge its recorded peak with the allowance
-- of the regions that were live throughout, and start a new stretch. A
-- region holds the part at its path, or below the root a Zero where the
-- part is absent: @|p| + 1@.
fold :: WM ()
fold = State.modify' $ \w ->
  let st = worldNet w
      live = SpaceBound [Affine (fromIntegral <$> worldLoad w)
                                (fromIntegral (sum (Map.delete 0 (worldLoad w))))]
      peak = liftA2 (<>) (sbConst <$> icPeak st) ((`sbScale` live) <$> Resources 4 12 4)
  in w { worldBounds = liftA2 (\x y -> sbWiden 16 (sbMax x y)) (worldBounds w) peak
       , worldNet = st { icPeak = icResident st } }

load :: Int -> Integer -> WM ()
load delta p = State.modify' $ \w ->
  w { worldLoad = Map.alter (\k -> case maybe delta (+ delta) k of 0 -> Nothing; k' -> Just k') p (worldLoad w) }

newRegion :: Integer -> WM Int
newRegion p = fold >> load 1 p >> net (newNode (ICInput p))

dropRegion :: Int -> WM ()
dropRegion n = net (kindOf n) >>= \case
  ICInput p -> fold >> load (-1) p >> net (deleteNode n)
  k         -> throwError (ICInternal ("dropRegion: " <> show k))

-- | Replace a region by a constructor in place. Node identity and principal
-- wiring survive; a pair gets two fresh regions for its parts.
reveal :: Int -> Integer -> Bool -> WM ()
reveal n p isPair = do
  fold
  load (-1) p
  net . State.modify' $ \st -> st { icNodes = IM.adjust
    (\nd -> nd { nodeKind = if isPair then ICPair else ICZero }) n (icNodes st) }
  when isPair . forM_ [(1, 2 * p + 1), (2, 2 * p + 2)] $ \(slot, child) -> do
    c <- newRegion child
    net (connect (Port n slot) (Port c 0))

-- | What the world knows about a path: a committed shape, a Zero under a
-- committed Zero, a pair above a committed pair, or nothing.
shapeOf :: Map Integer Bool -> Integer -> Maybe Bool
shapeOf shapes p = case Map.lookup p shapes of
  Just s -> Just s
  Nothing
    | any (\a -> Map.lookup a shapes == Just False) (ancestors p) -> Just False
    | any (\(q, s) -> s && p `elem` ancestors q) (Map.toList shapes) -> Just True
    | otherwise -> Nothing

-- | The paths above a path, nearest first.
ancestors :: Integer -> [Integer]
ancestors 0 = []
ancestors p = let a = (p - 1) `div` 2 in a : ancestors a

-- * The walk

data Step = Done | Continue | Fork Int Integer
  -- ^ Fork: the region node whose shape the popped pair needs, and its path.

analyzeIC :: AnalysisBudget -> ICProgram -> AnalysisOutcome
analyzeIC budget = fst . analyzeICDetailed budget

-- | The runtime's fuel cap is not a termination argument: budget exhaustion
-- returns Unknown, never the peak of an unfinished run.
analyzeICDetailed :: AnalysisBudget -> ICProgram -> (AnalysisOutcome, AnalysisStats)
analyzeICDetailed (AnalysisBudget steps0 forks0) prog =
  case runNet initialize (programInitial prog) { icFuel = maxBound
                                               , icPeak = icResident (programInitial prog) } of
    (Left err, _) -> (Unknown (show err), stats0)
    (Right _, st) -> walk steps0 forks0 stats0 (pure (sbConst 0))
      [World st Map.empty (Map.singleton 0 1) (pure (sbConst 0))]
  where
    stats0 = AnalysisStats 0 0 0
    initialize = initializeIC prog ((`Port` 0) <$> newNode (ICInput 0))
    walk _ _ stats done [] = (Established (sbWiden 16 <$> done), stats)
    walk steps forks stats done (w : rest)
      | steps <= 0 = (Unknown "IC transition budget exhausted", stats)
      | otherwise = case runWorld step w of
          (Left err, _) -> (Unknown ("unsupported IC transition: " <> show err), stats)
          (Right Done, w') -> walk steps forks stats { statWorlds = statWorlds stats + 1 }
            (liftA2 sbMax done (worldBounds w')) rest
          (Right Continue, w') -> walk (steps - 1) forks
            stats { statTransitions = statTransitions stats + 1 } done (w' : rest)
          (Right (Fork n p), w')
            | forks <= 0 -> (Unknown ("IC fork budget exhausted at " <> renderPath p), stats)
            | otherwise -> case traverse (child w' n p) [False, True] of
                Left err -> (Unknown (show err), stats)
                Right kids -> walk (steps - 1) (forks - 1)
                  stats { statTransitions = statTransitions stats + 1
                        , statForks = statForks stats + 1 }
                  done (kids <> rest)
    -- The popped pair went back; the child fires it against the shape.
    child w n p isPair = w' <$ r
      where (r, w') = runWorld (commit >> reveal n p isPair) w
            commit = State.modify' $ \x -> x { worldShapes = Map.insert p isPair (worldShapes x) }

-- | One popped pair, exactly as the runtime's 'reduce' pops it.
step :: WM Step
step = net pop >>= \case
  Nothing -> fold >> pure Done
  Just (a, b) -> do
    (ka, kb) <- net ((,) <$> kindOf a <*> kindOf b)
    case regionRule a ka b kb of
      Just act -> act
      Nothing -> case regionRule b kb a ka of
        Just act -> act
        Nothing  -> net (fire a b) >> pure Continue

-- | Transitions the runtime has no rule for: a consumer meeting a region, and
-- the erasure of a closed data tree. The pair was popped; a rule that ends
-- in a runtime interaction fires it itself.
regionRule :: Int -> ICKind -> Int -> ICKind -> Maybe (WM Step)
regionRule n nk m mk = case (nk, mk) of
  (ICEra, ICInput _) -> Just $ net (deleteNode n) >> dropRegion m >> pure Continue
  (ICDup _, ICInput p) -> Just $ do
    (c1, c2) <- net $ (,) <$> peer (Port n 1) <*> peer (Port n 2)
    net (deleteNode n)
    -- The eraser sits where the runtime's cascade pairs would; the copies'
    -- consumers are pushed after it, as the runtime pushes theirs.
    ghost <- net (newNode ICEra)
    net (connect (Port ghost 0) (Port m 0))
    forM_ [c1, c2] $ \c -> do
      copy <- newRegion p
      net (connect (Port copy 0) c)
    pure Continue
  (ICScrut, ICInput p) -> Just (byShape p)
  (ICScrutAbort, ICInput p) -> Just (byShape p)
  (_, ICInput p) | consumer nk -> Just $ do
    shapes <- State.gets worldShapes
    reveal m p (shapeOf shapes p /= Just False)
    net (fire n m)
    pure Continue
  (ICEra, ICPair) -> Just $ do
    st <- State.gets worldNet
    case materialTree st m of
      Nothing -> net (fire n m) >> pure Continue
      Just ns -> do
        -- The cascade is atomic under LIFO: at most one eraser per
        -- constructor and two new erasers and enqueues at each pair. Reserve
        -- that peak here and jump to the end.
        let k = 2 * fromIntegral (length ns) + 2 :: Natural
        net . State.modify' $ \s -> s { icPeak = liftA2 max (icPeak s)
          (liftA2 (+) (icResident s) (Resources k (3 * k) k)) }
        net $ mapM_ deleteNode (n : ns)
        pure Continue
  _ -> Nothing
  where
    consumer = \case
      ICSetEnv -> True
      ICApply  -> True
      ICLeft   -> True
      ICRight  -> True
      ICSplit  -> True
      _        -> False
    byShape p = do
      shapes <- State.gets worldShapes
      case shapeOf shapes p of
        Nothing -> do
          -- Put the pair back for the children.
          net $ do
            State.modify' $ \st -> st { icActive = (n, m) : icActive st }
            account $ \r -> r { resourceWork = resourceWork r + 1 }
          pure (Fork m p)
        Just isPair -> do
          reveal m p isPair
          net (fire n m)
          pure Continue

-- | The nodes of a closed Zero/Pair tree hanging from a node: every part is
-- a constructor whose principal faces its parent. A principal port has one
-- wire, so such a tree is never shared.
materialTree :: ICState -> Int -> Maybe [Int]
materialTree st n = do
  nd <- IM.lookup n (icNodes st)
  slots <- case nodeKind nd of
    ICZero -> Just []
    ICPair -> Just [1, 2]
    _      -> Nothing
  (n :) . concat <$> traverse (child nd) slots
  where
    child nd slot = do
      Port m 0 <- IM.lookup slot (nodePorts nd)
      materialTree st m

renderICSpace :: AnalysisOutcome -> String
renderICSpace (Unknown reason) = "IC logical storage: Unknown — " <> reason <> "\n"
renderICSpace (Established bounds) =
  renderICSpaceCertificate Bounds walkMethod bounds

-- |Whether a certificate's figures are a bound the analysis established, or
-- only an estimate. The reader is told which before any figure.
data Claim = Bounds | Estimates
  deriving (Eq, Show)

-- |How the walk introduces itself on a certificate it established.
walkMethod :: [String]
walkMethod =
  [ "How it was computed: a net walk. The analysis replayed the runtime's own"
  , "rules over a symbolic input, splitting wherever control depends on the"
  , "input's shape, and kept the worst peak over every split, plus a fixed"
  , "allowance for each unknown part of the input. Where the walk finishes,"
  , "as it did here, the figures are usually close to the real peak."
  ]

-- |A certificate as a reader-facing document: what it claims (a bound or an
-- estimate), how it was computed (the caller's method lines), the figures,
-- and what each figure counts. Everything the reader needs to understand a
-- figure is on the page.
renderICSpaceCertificate :: Claim -> [String] -> Resources SpaceBound -> String
renderICSpaceCertificate claim methodLines bounds = unlines $
  claimLines claim
  <> fmap indent methodLines
  <> [""]
  <> peakHeading claim
  <> [""]
  <> [ "    " <> pad name <> " ≤ " <> affine (sbHeadline b) | (name, b) <- named ]
  <> [ ""
     , "  Agents are the nodes resident in the net, port entries the wire"
     , "  endpoints it stores (stale ones included), and pending pairs the"
     , "  interactions waiting on the worklist."
     ]
  <> byPart
  <> [ "" | rounds ]
  <> [ "  Figures over six digits are shown rounded up to three significant" | rounds ]
  <> [ "  figures; rounding up never shows less than the analysis computed." | rounds ]
  <> [ ""
     , "  Not counted: preparation workspace, readback of the result, Haskell"
     , "  runtime overhead, GC and process memory."
     ]
  where
    claimLines Bounds =
      [ "IC space certificate"
      , ""
      , "  What this bounds: run this program on the interaction-net runtime"
      , "  (--ic) on any finite Zero/Pair input, and the net's logical storage"
      , "  stays within the figures below. |input| is the number of constructor"
      , "  cells (Zero and Pair nodes) of that input."
      , ""
      ]
    claimLines Estimates =
      [ "IC space estimate"
      , ""
      , "  What this estimates: the net's logical storage when this program runs"
      , "  on the interaction-net runtime (--ic) on any finite Zero/Pair input."
      , "  The figures are an estimate, not a guarantee (see below). |input| is"
      , "  the number of constructor cells (Zero and Pair nodes) of that input."
      , ""
      ]
    peakHeading Bounds =
      [ "  Peak storage of one evaluation (a session of several evaluations"
      , "  peaks at the largest of them):"
      ]
    peakHeading Estimates =
      [ "  Estimated peak storage of one evaluation (a session of several"
      , "  evaluations peaks at the largest of them):"
      ]
    indent = ("  " <>)
    named = zip ["agents", "port entries", "pending pairs"] (toList bounds)
    pad name = take 14 (name <> repeat ' ')
    rounds = any roundsIn bounds
    roundsIn b = sbRounds b || sbRounds (SpaceBound [sbHeadline b])
    byPart
      | all sbIsHeadline bounds = []
      | otherwise =
          [ ""
          , "  The figures above fold every part of the input into the whole;"
          , "  by part, where |input.left| counts only the cells of the input's"
          , "  left subtree and input.left×63 folds 63 left steps, the analysis"
          , "  established the tighter:"
          , ""
          ]
          <> concatMap cases named
    cases (name, b) = case sbCases b of
      [one] -> ["    " <> name <> ": " <> one]
      many  -> ("    " <> name <> ", the largest of " <> show (length many) <> " cases:")
               : fmap ("      " <>) many
