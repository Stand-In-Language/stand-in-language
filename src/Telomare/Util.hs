-- | Small helpers shared across the compiler. Nothing here may depend on
-- other Telomare modules.
module Telomare.Util where

import Debug.Trace (trace)

-- | Master debug switch. Flip in a dev checkout; never commit True.
debug :: Bool
debug = False

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

padRight :: Int -> String -> String
padRight w s = s <> replicate (max 0 (w - length s)) ' '

plural :: String -> Int -> String
plural word 1 = word
plural word _ = word <> "s"
