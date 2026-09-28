{-# LANGUAGE LambdaCase #-}

-- |Draw a prepared IC program as a standalone SVG figure: its entry net, then
-- the templates the entry can instantiate, breadth-first, one panel each,
-- within an agent budget. The entry net alone is the same scaffolding for
-- every program — the program's code lives in templates — so the templates
-- are what tell programs apart. Each panel has one circle per agent, a filled
-- dot on its principal port, open dots on the auxiliaries, and one line per
-- wire — with principal-to-principal wires in a hot color: the active pairs,
-- where rules fire, including boundary wires that become active once a run
-- attaches the input. The layout is layered: a breadth-first walk from the
-- root (in a prepared net or a template, which has none, from its boundary)
-- assigns depths, and one barycenter pass per layer keeps wires short.
-- Everything is pure; the figure shares its visual language with
-- interaction-nets.html.
module Telomare.IC.Draw where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import Data.List (sortOn)
import Data.Sequence (Seq ((:<|)), (|>))
import qualified Data.Sequence as Seq

import Telomare.IC
import Telomare.IC.Static (refTargets)

-- |Agents and wires, for reporting alongside the figure. Wires are stored
-- from both ends, so half the port entries.
netStats :: IntMap Node -> (Int, Int)
netStats nodes =
  (IntMap.size nodes, sum (fmap (IntMap.size . nodePorts) nodes) `div` 2)

-- |A short label a reader can take in inside a small circle.
shortKind :: ICKind -> String
shortKind = \case
  ICRoot       -> "root"
  ICExt        -> "ext"
  ICEra        -> "era"
  ICZero       -> "0"
  ICGate       -> "gate"
  ICAbort      -> "abort"
  ICRef t _    -> "ref " <> show t
  ICPair       -> "pair"
  ICAborted    -> "aborted"
  ICDup _      -> "dup"
  ICSplit      -> "split"
  ICSetEnv     -> "setenv"
  ICApply      -> "apply"
  ICScrut      -> "scrut"
  ICScrutAbort -> "scrab"
  ICLeft       -> "left"
  ICRight      -> "right"
  ICStuckV _   -> "stuck"
  ICInput p    -> "in " <> show p

-- |Depth per agent: breadth-first from a root node (the lowest id when no
-- 'ICRoot' remains unvisited); each disconnected component starts a fresh
-- band of layers below the previous one.
netDepths :: IntMap Node -> IntMap Int
netDepths nodes = go (IntMap.keysSet nodes) IntMap.empty 0
  where
    roots = [n | (n, nd) <- IntMap.toList nodes, ICRoot <- [nodeKind nd]]
    -- each component starts two rows below the deepest one so far, which is
    -- the previous component's deepest row: it began below all the others
    go unvisited acc base
      | IntSet.null unvisited = acc
      | otherwise = go (unvisited IntSet.\\ IntMap.keysSet comp)
                       (IntMap.union acc comp) (2 + maximum (IntMap.elems comp))
      where
        source = case filter (`IntSet.member` unvisited) roots of
          (r : _) -> r
          []      -> IntSet.findMin unvisited
        comp = walk (Seq.singleton (source, base)) IntMap.empty
        walk Seq.Empty seen = seen
        walk ((n, d) :<| rest) seen
          | IntMap.member n seen || not (IntSet.member n unvisited) =
              walk rest seen
          | otherwise = walk
              (foldl (\q m -> q |> (m, d + 1)) rest (neighbors nodes n))
              (IntMap.insert n d seen)

neighbors :: IntMap Node -> Int -> [Int]
neighbors nodes n =
  foldMap (fmap portNode . IntMap.elems . nodePorts) (IntMap.lookup n nodes)

-- |Rows of agent ids, top to bottom; within a row, agents sort by the mean
-- position of their neighbors in the rows already placed, so wires stay
-- short without any real graph-layout machinery.
netRows :: IntMap Node -> [[Int]]
netRows nodes = reverse . snd $ foldl place (IntMap.empty, []) rows
  where
    depth = netDepths nodes
    rows = IntMap.elems $ IntMap.fromListWith (flip (<>))
      [(d, [n]) | (n, d) <- IntMap.toList depth]
    place (posOf, done) row = (posOf', srt : done)
      where
        srt = sortOn (\n -> (barycenter n, n)) row
        posOf' = IntMap.union posOf
          (IntMap.fromList (zip srt [0 :: Int ..]))
        barycenter n = case
          [fromIntegral i | m <- neighbors nodes n
                          , Just i <- [IntMap.lookup m posOf]] of
          [] -> 1 / 0 :: Double
          xs -> sum xs / fromIntegral (length xs)

-- |A standalone SVG document around some elements, at its natural size in
-- pixels: a tall program drawing scrolls instead of shrinking to fit.
svgDocument :: Double -> Double -> [String] -> String
svgDocument width height elements = unlines $
  [ "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"" <> num width
      <> "\" height=\"" <> num height <> "\" viewBox=\"0 0 " <> num width <> " "
      <> num height <> "\" font-family=\"ui-monospace, Menlo, monospace\">"
  , "<style>"
  , ".wire{stroke:#1E6E58;stroke-width:1.6;fill:none}"
  , ".wire.hot{stroke:#C25A2E;stroke-width:2.6}"
  , ".body{fill:#EEF0EA;stroke:#20281F;stroke-width:1.3}"
  , ".pp{fill:#C25A2E;stroke:none}"
  , ".aux{fill:#F6F7F4;stroke:#20281F;stroke-width:1}"
  , "text{font-size:10px;fill:#20281F;text-anchor:middle}"
  , ".id{font-size:8px;fill:#6E7A70}"
  , ".head{font-size:12px;font-weight:600;text-anchor:start}"
  , ".title{font-size:11px;font-weight:600;text-anchor:start}"
  , ".rule{stroke:#CDD3C9;stroke-width:1}"
  , ".box{fill:#EEF0EA;stroke:#CDD3C9;stroke-width:1}"
  , "</style>"
  , "<rect width=\"100%\" height=\"100%\" fill=\"#F6F7F4\"/>"
  ]
  <> elements
  <> ["</svg>"]

-- |One net as a standalone figure.
drawNet :: IntMap Node -> String
drawNet nodes = svgDocument width height elements
  where (width, height, elements) = layoutPanel nodes

-- |What a program drawing covered, for reporting alongside the figure.
data DrawSummary = DrawSummary
  { drawnTemplates     :: !Int
  , reachableTemplates :: !Int
  , drawnAgents        :: !Int
  , totalAgents        :: !Int
  } deriving (Eq, Show)

-- |Templates the entry net can instantiate, directly or through other
-- templates, breadth-first, each with the template that first reached it
-- ('Nothing' for the entry). The reserved selectors are left out: every
-- program has the same three.
templateOrder :: ICProgram -> [(TemplateId, Maybe TemplateId)]
templateOrder prog = go IntSet.empty
  (Seq.fromList [(t, Nothing) | t <- refsOf (icNodes st)])
  where
    st = programInitial prog
    tpls = icTemplates st
    refsOf nodes = filter (`notElem` [leftSelTpl, rightSelTpl, idSelTpl])
      (IntMap.keys (refTargets nodes))
    go seen = \case
      Seq.Empty -> []
      (t, from) :<| rest
        | IntSet.member t seen -> go seen rest
        | otherwise -> (t, from) : go (IntSet.insert t seen)
            (foldl (|>) rest [ (r, Just t) | r <- foldMap (refsOf . tplNodes)
                                                   (IntMap.lookup t tpls) ])

-- |A program as a figure: a header, the entry net, then its reachable
-- templates in 'templateOrder'. A template that fits the remaining budget of
-- agents is drawn in full; one that does not is a collapsed box, and past a
-- dozen boxes the rest fold into one closing line.
drawProgram :: String -> Int -> ICProgram -> (String, DrawSummary)
drawProgram title limit prog =
  (svgDocument canvasW (sum (fmap fst placed) + 16) (concat stacked), summary)
  where
    st = programInitial prog
    tpls = icTemplates st
    entry = icNodes st
    order = templateOrder prog
    sizeOf t = maybe 0 (IntMap.size . tplNodes) (IntMap.lookup t tpls)
    decide _ [] = []
    decide left ((t, from) : rest)
      | sizeOf t <= left = (t, from, True) : decide (left - sizeOf t) rest
      | otherwise = (t, from, False) : decide left rest
    decided = decide limit order
    drawn = [ t | (t, _, True) <- decided ]
    collapsed = [ t | (t, _, False) <- decided ]
    boxed = take 12 collapsed
    folded = drop 12 collapsed
    summary = DrawSummary (length drawn) (length order)
      (sum (fmap sizeOf drawn)) (sum [ sizeOf t | (t, _) <- order ])
    header = title <> " — entry net (" <> commas (IntMap.size entry)
      <> " agents) and " <> show (drawnTemplates summary) <> " of "
      <> show (reachableTemplates summary) <> " reachable templates ("
      <> commas (drawnAgents summary) <> " of " <> commas (totalAgents summary)
      <> " agents); selector templates omitted"
    reach = maybe "reached from entry" (\f -> "reached from #" <> show f)
    panelOf label nodes = let (w, h, els) = layoutPanel nodes
      in (w, h + 30, \y -> [ "<g class=\"panel\" transform=\"translate(0," <> num y <> ")\">"
                          , "<line class=\"rule\" x1=\"0\" y1=\"0\" x2=\"" <> num canvasW <> "\" y2=\"0\"/>"
                          , "<text class=\"title\" x=\"16\" y=\"20\">" <> label <> "</text>"
                          , "<g transform=\"translate(0,30)\">" ]
                          <> els <> ["</g>", "</g>"])
    boxOf label = (textWidth label + 48, 40, \y ->
      [ "<g class=\"collapsed\" transform=\"translate(0," <> num y <> ")\">"
      , "<rect class=\"box\" x=\"16\" y=\"6\" width=\"" <> num (canvasW - 32)
          <> "\" height=\"28\" rx=\"4\"/>"
      , "<text class=\"title\" x=\"28\" y=\"24\">" <> label <> "</text>"
      , "</g>" ])
    lineOf cls label = (textWidth label + 32, 32, \y ->
      [ "<text class=\"" <> cls <> "\" x=\"16\" y=\"" <> num (y + 22) <> "\">"
          <> label <> "</text>" ])
    items =
      [ lineOf "head" header
      , panelOf ("entry net · " <> commas (IntMap.size entry)
                 <> " agents · what a run starts from") entry ]
      <> concat
        [ if isDrawn
            then [ panelOf ("template #" <> show t <> " · " <> commas (sizeOf t)
                            <> " agents · " <> reach from) (tplNodes tpl) ]
            else [ boxOf ("template #" <> show t <> " · " <> commas (sizeOf t)
                          <> " agents · " <> reach from
                          <> " — not expanded (over --draw-limit)")
                 | t `elem` boxed ]
        | (t, from, isDrawn) <- decided
        , Just tpl <- [IntMap.lookup t tpls] ]
      <> [ lineOf "title" ("+ " <> show (length folded) <> " more templates ("
             <> commas (sum (fmap sizeOf folded)) <> " agents) not drawn; raise --draw-limit")
         | not (null folded) ]
    canvasW = maximum (320 : [ w | (w, _, _) <- items ])
    placed = [ (h, f) | (_, h, f) <- items ]
    stacked = zipWith (\y (_, f) -> f y) (scanl (+) 0 (fmap fst placed)) placed
    textWidth label = 7.3 * fromIntegral (length label)

-- |Digits grouped by thousands, the way the certificate's readers expect.
commas :: Int -> String
commas n = reverse (go (reverse (show n)))
  where
    go (a : b : c : rest@(_ : _)) = a : b : c : ',' : go rest
    go ds                         = ds

-- |One net laid out on a fixed grid, in its own coordinates: its width,
-- height and elements. A small net is compact, a large one simply a larger
-- canvas to scroll.
layoutPanel :: IntMap Node -> (Double, Double, [String])
layoutPanel nodes = (width, height, fmap wire wires <> concatMap agent (IntMap.toList nodes))
  where
    rows = netRows nodes
    colW = 84 :: Double
    rowH = 110 :: Double
    radius = 21 :: Double
    width = 2 * colW + colW * fromIntegral (maximum (1 : fmap length rows) - 1)
    height = 2 * rowH + rowH * fromIntegral (max 1 (length rows) - 1)
    posOf = IntMap.fromList
      [ (n, (colW + colW * fromIntegral col, rowH + rowH * fromIntegral row))
      | (row, ns) <- zip [0 :: Int ..] rows, (col, n) <- zip [0 :: Int ..] ns ]
    at n = IntMap.findWithDefault (0, 0) n posOf
    -- every wire once: keep the end whose (node, slot) is smaller
    wires =
      [ (n, s, m, t)
      | (n, nd) <- IntMap.toList nodes
      , (s, Port m t) <- IntMap.toList (nodePorts nd)
      , (n, s) < (m, t) ]
    wire (n, s, m, t)
      | n == m = "<circle class=\"wire\" cx=\"" <> num x <> "\" cy=\""
          <> num (y - radius - 8) <> "\" r=\"8\" fill=\"none\"/>"
      | otherwise = "<line class=\"wire" <> hot <> "\" x1=\"" <> num ax
          <> "\" y1=\"" <> num ay <> "\" x2=\"" <> num bx
          <> "\" y2=\"" <> num by <> "\"/>"
      where
        hot = if s == 0 && t == 0 then " hot" else ""
        (x, y) = at n
        (ax, ay) = rim (at n) (at m)
        (bx, by) = rim (at m) (at n)
    agent (n, nd) =
      [ "<g class=\"agent\">"
      , "<circle class=\"body\" cx=\"" <> num x <> "\" cy=\"" <> num y
          <> "\" r=\"" <> num radius <> "\"/>"
      , "<text x=\"" <> num x <> "\" y=\"" <> num (y + 3.5) <> "\">"
          <> shortKind (nodeKind nd) <> "</text>"
      , "<text class=\"id\" x=\"" <> num x <> "\" y=\""
          <> num (y + radius + 11) <> "\">#" <> show n <> "</text>"
      ]
      <> [ port s (at (portNode p)) | (s, p) <- IntMap.toList (nodePorts nd) ]
      <> ["</g>"]
      where
        (x, y) = at n
        port s far = "<circle class=\"" <> cls <> "\" cx=\"" <> num px
            <> "\" cy=\"" <> num py <> "\" r=\"" <> r <> "\"/>"
          where
            cls = if s == 0 then "pp" else "aux"
            r = if s == 0 then "4.5" else "3.5"
            (px, py) = rim (x, y) far
    -- the point on a node's rim facing another node
    rim (x, y) (fx, fy)
      | len < 0.5 = (x, y - radius)
      | otherwise = (x + dx / len * radius, y + dy / len * radius)
      where
        dx = fx - x
        dy = fy - y
        len = sqrt (dx * dx + dy * dy)

-- |A coordinate to one decimal, without a trailing @.0@.
num :: Double -> String
num v = trim (show (fromIntegral (round (v * 10) :: Int) / 10 :: Double))
  where
    trim str = case break (== '.') str of
      (whole, ".0") -> whole
      _             -> str
