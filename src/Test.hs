{-# LANGUAGE FlexibleInstances #-}

module Test where

class Thing p where
  thing :: p -> String

class Thing1 p where
  thing1 :: Thing a => p a -> String

instance (Thing1 f, Thing x) => Thing (f x) where
  thing = thing1

data Token = Token

instance Thing x => Thing (Either x Token)

{-
testF :: (Thing x) => Either x Token -> String
testF = thing

testF' :: (Thing x) => x -> String -- no overlap here!
testF' = thing
-}
