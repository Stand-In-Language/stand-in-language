-- | Small helpers shared across the compiler. Nothing here may depend on
-- other Telomare modules.
module Telomare.Util where

padRight :: Int -> String -> String
padRight w s = s <> replicate (max 0 (w - length s)) ' '

plural :: String -> Int -> String
plural word 1 = word
plural word _ = word <> "s"
