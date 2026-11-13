{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternSynonyms #-}

-- | How much the interaction-net runtime ('Telomare.IC') can hold, worked
-- out before the program runs: the most storage one iteration's net reaches,
-- over every input.
--
-- The runtime keeps an iteration's input whole, as one 'ICData' node, and
-- takes it apart one layer at a time, only when a consumer needs its shape
-- ('Telomare.IC.revealData'). So what a run does depends on the input only
-- through the shapes the program actually looks at. This module runs the
-- runtime's own net with an input whose shape is unknown: the input is one
-- 'ICData' node holding a /path/ instead of a value ('DataPart'), every
-- pair fires by the runtime's own code, in the runtime's own order (it
-- schedules through 'Telomare.IC.nextPair'), and when a consumer needs the
-- shape of an input part nobody has looked at yet, the walk splits in two:
-- one copy goes on as if that part is Zero, the other as if it is a pair.
-- A copy of the walk is a /world/: a set of input shapes, all of which the
-- runtime runs identically, interaction for interaction, because it never
-- looks at anything that tells them apart.
--
-- That makes the result exact, not just a limit: every world's storage
-- counters are the runtime's counters for every input in it, so the
-- largest over all worlds is the most any input reaches, and the input
-- built from a world's shapes (Zero wherever nothing looked) reaches it.
--
-- Worlds never rejoin, so a program that looks at many input parts
-- independently has very many worlds. The walk has an explicit budget of
-- interactions and worlds; running out of either gives 'SpaceUnknown',
-- never a partial figure.
module Telomare.IC.Space
  ( SpaceBudget (..)
  , defaultSpaceBudget
  , Peak (..)
  , SpaceCertificate (..)
  , SpaceOutcome (..)
  , certifySpace
  , certificateCovers
  , renderSpace
  , renderData
  ) where

import Control.Monad.Except (catchError, runExceptT)
import qualified Control.Monad.State.Strict as State
import Crypto.Hash (Digest, SHA256)
import Data.Map (Map)
import qualified Data.Map as Map
import Telomare.EAL (CapShape)
import Telomare.IC
import Telomare.IR.Base (BasicExpr, pattern PairB, pattern ZeroB)
import Telomare.IR.Core (CompiledExpr)

-- | How much walking to do before giving up: interactions over all worlds
-- together, and worlds.
data SpaceBudget = SpaceBudget
  { budgetInteractions :: !Int
  , budgetWorlds       :: !Int
  } deriving (Eq, Show)

defaultSpaceBudget :: SpaceBudget
defaultSpaceBudget = SpaceBudget 20000000 100000

-- | The largest figure some input reaches, and one input that reaches it.
data Peak = Peak
  { peakValue :: !Int
  , peakInput :: BasicExpr
  } deriving (Eq, Show)

-- | What the walk established. Each storage component has its own worst
-- input; they need not be the same input.
data SpaceCertificate = SpaceCertificate
  { certAgents       :: Peak
  , certPorts        :: Peak
  , certWork         :: Peak
  , certTemplates    :: Resources
    -- ^ the template table: the same on every iteration and every input
  , certWorlds       :: !Int
    -- ^ input shapes the program tells apart
  , certErrorWorlds  :: !Int
    -- ^ of those, how many end in a runtime error before finishing
  , certInteractions :: !Int
    -- ^ interactions the walk performed over all worlds
  } deriving (Eq, Show)

data SpaceOutcome
  = SpaceBound SpaceCertificate
  | SpaceUnknown String Int Int
    -- ^ why, worlds finished, interactions performed
  deriving (Eq, Show)

-- | A copy of the walk, and the input shapes it has committed to, by path:
-- True for a pair.
data World = World
  { worldNet    :: ICState
  , worldShapes :: Map Integer Bool
  }

-- | Why a world stopped advancing.
data Stop = Finished | Failed | NeedShape Integer | OutOfInteractions

-- | Work out, before running, the most storage an iteration of @main@
-- reaches on the net, over every input, under the guidance a session runs
-- with ('Telomare.Eval.IC.icPlanLayouts').
certifySpace :: SpaceBudget -> Map (Digest SHA256) CapShape -> CompiledExpr
             -> SpaceOutcome
certifySpace (SpaceBudget interactions0 worlds0) guidance mainTerm =
  case traverse start [False, True] of
    Left err     -> SpaceUnknown ("the net could not be built: " <> show err) 0 0
    Right worlds -> walk interactions0 (worlds0 - 2) emptyAcc worlds
  where
    -- the input is Zero, or a pair whose parts nothing has looked at yet
    start isPair =
      let kind = if isPair then ICData (DataPart 0) else ICZero
          -- the runtime's own fuel: a world that would run out of it
          -- fails where the runtime fails
          (r, st) = runNet (buildApplied mainTerm kind)
                           (emptyState guidance defaultFuel)
      in World st (Map.singleton 0 isPair) <$ r

    walk _ _ acc [] = SpaceBound (finish acc)
    walk left spare acc (w : rest)
      | left <= 0 = outOf "interaction" acc
      | otherwise =
          let (r, st) = runNet (drive (worldShapes w) left) (worldNet w)
          in case r of
            Left err -> SpaceUnknown ("internal error in the walk: " <> show err)
              (accWorlds acc) (accInteractions acc)
            -- the runtime fails the same way on these inputs, and holds
            -- nothing after it does
            Right (Failed, used) -> walk (left - used - 1) spare
              (record True (worldShapes w) st used acc) rest
            Right (Finished, used) -> walk (left - used) spare
              (record False (worldShapes w) st used acc) rest
            Right (OutOfInteractions, used) ->
              outOf "interaction" acc { accInteractions = accInteractions acc + used }
            Right (NeedShape path, used)
              | spare <= 0 -> outOf "world"
                  acc { accInteractions = accInteractions acc + used }
              | otherwise ->
                  let child isPair = World st (Map.insert path isPair (worldShapes w))
                  in walk (left - used) (spare - 1)
                       acc { accInteractions = accInteractions acc + used }
                       (child False : child True : rest)

    outOf what acc = SpaceUnknown
      ("the check ran out of its " <> what <> " budget before it covered every "
         <> "input shape")
      (accWorlds acc) (accInteractions acc)

    finish acc = SpaceCertificate
      { certAgents = accAgents acc
      , certPorts = accPorts acc
      , certWork = accWork acc
      , certTemplates = accTemplates acc
      , certWorlds = accWorlds acc
      , certErrorWorlds = accErrors acc
      , certInteractions = accInteractions acc
      }

runNet :: ICM a -> ICState -> (Either ICError a, ICState)
runNet action = State.runState (runExceptT action)

-- | Fire pairs in the runtime's order until the net is done, the budget is
-- spent, or a consumer needs the shape of an input part this world has not
-- committed to. A pair is only taken off its queue once it can fire, so a
-- world that stops for a shape resumes, in each child, at the same pair.
-- Returns how many pairs fired.
drive :: Map Integer Bool -> Int -> ICM (Stop, Int)
drive shapes limit = go 0
  where
    -- one pair at a time, each under its own handler: a rule that fails
    -- ends the world where the runtime's run would end
    go k
      | k >= limit = pure (OutOfInteractions, k)
      | otherwise = ((Right <$> step) `catchError` (pure . Left)) >>= \case
          Left _err        -> pure (Failed, k)
          Right (Just why) -> pure (why, k)
          Right Nothing    -> go (k + 1)
    step = nextPair >>= \case
      Nothing -> pure (Just Finished)
      Just next -> demanded next >>= \case
        Just (n, path) -> case Map.lookup path shapes of
          Nothing -> pure (Just (NeedShape path))
          Just isPair -> do
            popNext next
            -- exactly what 'fire' does with a known value of this shape
            revealData n $ if isPair
              then Just (DataPart (2 * path + 1), DataPart (2 * path + 2))
              else Nothing
            fireNext next
            pure Nothing
        Nothing -> popNext next >> fireNext next >> pure Nothing
    -- parked pairs are applications meeting code: never data
    demanded = \case
      Eager a b -> demandedData a b >>= \case
        Just (n, DataPart path) -> pure (Just (n, path))
        _known -> pure Nothing
      Parked _ _ -> pure Nothing

-- * Accumulating worlds

data Acc = Acc
  { accAgents       :: !Peak
  , accPorts        :: !Peak
  , accWork         :: !Peak
  , accTemplates    :: !Resources
  , accWorlds       :: !Int
  , accErrors       :: !Int
  , accInteractions :: !Int
  }

emptyAcc :: Acc
emptyAcc = Acc none none none noResources 0 0 0
  where none = Peak (-1) ZeroB

record :: Bool -> Map Integer Bool -> ICState -> Int -> Acc -> Acc
record failed shapes st used acc = acc
  { accAgents = raise (resAgents peak) (accAgents acc)
  , accPorts = raise (resPorts peak) (accPorts acc)
  , accWork = raise (resWork peak) (accWork acc)
  , accTemplates = maxResources (templateStorage st) (accTemplates acc)
  , accWorlds = accWorlds acc + 1
  , accErrors = accErrors acc + (if failed then 1 else 0)
  , accInteractions = accInteractions acc + used
  }
  where
    peak = icPeak st
    raise v best
      | v > peakValue best = Peak v (witness shapes)
      | otherwise = best

-- | The input a world stands for, with Zero wherever nothing looked.
witness :: Map Integer Bool -> BasicExpr
witness shapes = go 0
  where
    go :: Integer -> BasicExpr
    go path
      | Map.lookup path shapes == Just True = PairB (go (2 * path + 1)) (go (2 * path + 2))
      | otherwise = ZeroB

-- | Whether a measured run stays within the certificate. Unknown never
-- does.
certificateCovers :: Resources -> SpaceOutcome -> Bool
certificateCovers measured = \case
  SpaceBound c -> resAgents measured <= peakValue (certAgents c)
    && resPorts measured <= peakValue (certPorts c)
    && resWork measured <= peakValue (certWork c)
  SpaceUnknown {} -> False

-- * Rendering

-- | A data value the way a reader writes it: @0@, @(0,(0,0))@; a large one
-- by its size.
renderData :: BasicExpr -> String
renderData e
  | length shown <= 60 = shown
  | otherwise = "an input of " <> show (cells e) <> " cells"
  where
    shown = go e
    go :: BasicExpr -> String
    go = \case
      PairB a b -> "(" <> go a <> "," <> go b <> ")"
      _zero     -> "0"
    cells :: BasicExpr -> Int
    cells = \case
      PairB a b -> 1 + cells a + cells b
      _zero     -> 1

renderSpace :: SpaceOutcome -> String
renderSpace = \case
  SpaceBound c -> unlines $
    [ "IC storage certificate", "" ]
    <> para ("Run this program on the interaction-net runtime (--ic), and on every "
             <> "iteration, whatever its input, the net holds at most:")
    <> [ ""
       , row "agents" (certAgents c)
       , row "port entries" (certPorts c)
       , row "pending pairs" (certWork c)
       , "" ]
    <> para ("These are exact worst cases, not estimates. The check ran the net once "
             <> "for every way the program can take its input apart ("
             <> plural (certWorlds c) "input shape" <> ", "
             <> commas (certInteractions c) <> " interactions in all), so some input "
             <> "reaches each figure; the input shown is one that does."
             <> if certErrorWorlds c > 0
                  then " " <> plural (certErrorWorlds c) "input shape"
                         <> " end the run in a runtime error; the figures cover "
                         <> "them up to the error."
                  else "")
    <> [""]
    <> para ("Agents are the nodes in the net, port entries the wire ends it stores, "
             <> "and pending pairs the interactions waiting to fire.")
    <> [""]
    <> para ("Not counted: the input itself, which the net holds whole until the "
             <> "program takes it apart; the template table (code, and constants counted "
             <> "cell by cell), the same on every "
             <> "iteration (" <> commas (resAgents (certTemplates c)) <> " agents, "
             <> commas (resPorts (certTemplates c)) <> " port entries); reading back "
             <> "the result; and the Haskell runtime's own memory (GC, the process).")
  SpaceUnknown why worlds interactions -> unlines $
    [ "IC storage certificate", "" ]
    <> para ("No limit could be worked out: " <> why <> ".")
    <> [""]
    <> para ("The check runs the net once for every way the program can take its "
             <> "input apart. It covered " <> plural worlds "input shape" <> " in "
             <> commas interactions <> " interactions and did not finish, so it "
             <> "claims nothing.")
  where
    row name pk = "    " <> pad 15 name <> pad 12 (commas (peakValue pk))
      <> "reached by input " <> renderData (peakInput pk)
    pad n str = str <> replicate (n - length str) ' '
    plural n what = commas n <> " " <> what <> (if n == 1 then "" else "s")

-- | A paragraph, indented two spaces and wrapped at 76 columns.
para :: String -> [String]
para = fmap ("  " <>) . go [] 0 . words
  where
    width = 74
    go line _ [] = [unwords (reverse line) | not (null line)]
    go [] _ (w : ws) = go [w] (length w) ws
    go line n (w : ws)
      | n + 1 + length w > width = unwords (reverse line) : go [w] (length w) ws
      | otherwise = go (w : line) (n + 1 + length w) ws

-- | 1234567 as 1,234,567.
commas :: Int -> String
commas n
  | n < 0 = '-' : commas (negate n)
  | otherwise = reverse . go . reverse $ show n
  where
    go (a : b : c : rest@(_ : _)) = a : b : c : ',' : go rest
    go xs                         = xs
