{-# LANGUAGE LambdaCase      #-}

-- |A compiled program on disk, so that sizing happens once.
--
-- Sizing a Prelude-heavy program costs minutes and several gigabytes, and it
-- produces the same answer every time: it runs the program over a /symbolic/
-- input, so nothing about a particular run can change it. Paying that on every
-- invocation is pure waste. `--compile` writes the sized program, its
-- per-site iteration counts and its rendered certificate to a @.telc@ file;
-- running that file skips parsing, typechecking, resolving and sizing
-- entirely.
--
-- The encoding is a tag byte per node, written by hand rather than derived.
-- `CompiledExpr` is a fixpoint of three small functors, so this is a short
-- function; deriving it instead would mean either a `Read` instance (there is
-- none, and the `Show1` instances are not round-trippable) or orphan `Binary`
-- instances for a type this module does not own.
--
-- A hash of the sources is stored so a stale artifact can be recognized. It is
-- a warning and never a refusal: an artifact is expected to outlive the
-- checkout it came from, and the sources may not be there at all.
module Telomare.Artifact
  ( Artifact (..)
  , artifactMagic
  , artifactVersion
  , encodeArtifact
  , decodeArtifact
  , writeArtifact
  , readArtifact
  , sourcesHash
  , nodeCount
  , telcExtension
  , isArtifactPath
  ) where

import Crypto.Hash (Digest, SHA256, hash)
import Data.Binary.Get (Get, getInt64le, getLazyByteString, getWord8,
                        runGetOrFail)
import Data.Binary.Put (Put, putInt64le, putLazyByteString, putWord8, runPut)
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.UTF8 as UTF8
import Data.Functor.Foldable (cata, embed, project)
import Data.List (sortOn)
import Data.Map (Map)
import qualified Data.Map as Map
import System.FilePath (takeExtension)

import Telomare.Error
import Telomare.IR.Base
import Telomare.IR.Builder
import Telomare.IR.Core
import Telomare.IR.Loc
import Telomare.IR.Surface
import Telomare.IR.Types
import Telomare.Eval (SizingReport (..))
import Telomare.PossibleData (SizedRecursion (..))

-- |A program with its sizing already done.
data Artifact = Artifact
  { artifactEntry       :: String
  -- ^The module that holds `main`.
  , artifactSourceHash  :: String
  -- ^Hash of the sources this was compiled from.
  , artifactReport      :: SizingReport
  -- ^What sizing found, so `--certificate` needs no sources.
  , artifactCertificate :: String
  -- ^The static report as it was rendered at compile time.
  , artifactExpr        :: CompiledExpr
  -- ^The sized program.
  }

artifactMagic :: BL.ByteString
artifactMagic = BL.pack [0x54, 0x45, 0x4C, 0x43] -- "TELC"

-- |Bumped whenever the encoding changes, which invalidates older files rather
-- than misreading them.
artifactVersion :: Int
artifactVersion = 2

telcExtension :: String
telcExtension = ".telc"

isArtifactPath :: FilePath -> Bool
isArtifactPath = (== telcExtension) . takeExtension

-- |How many nodes the sized program has. Church towers make sized programs
-- much larger than their sources, which is worth reporting when one is
-- written.
nodeCount :: CompiledExpr -> Int
nodeCount = cata (\x -> 1 + sum x)

-- |A hash of every module that went into a program, order-independent.
sourcesHash :: [(String, String)] -> String
sourcesHash modules = show digest
  where
    digest :: Digest SHA256
    digest = hash . UTF8.fromString . concatMap chunk $ sortOn fst modules
    -- Lengths are included so that no regrouping of names and contents can
    -- collide with a different set of modules.
    chunk (name, content) =
      show (length name) <> ":" <> name <> show (length content) <> ":" <> content

encodeArtifact :: Artifact -> BL.ByteString
encodeArtifact a = runPut $ do
  putLazyByteString artifactMagic
  putInt' artifactVersion
  putString (artifactEntry a)
  putString (artifactSourceHash a)
  putString (artifactCertificate a)
  putReport (artifactReport a)
  putCompiled (artifactExpr a)

decodeArtifact :: BL.ByteString -> Either String Artifact
decodeArtifact bytes = case runGetOrFail getArtifact bytes of
  Left (_, _, err)     -> Left $ "not a readable telomare artifact: " <> err
  Right (_, _, result) -> result

getArtifact :: Get (Either String Artifact)
getArtifact = do
  magic <- getLazyByteString 4
  if magic /= artifactMagic
    then pure $ Left "not a telomare artifact (bad magic number)"
    else do
      version <- getInt'
      if version /= artifactVersion
        then pure . Left $ "this artifact is version " <> show version
          <> ", but this telomare reads version " <> show artifactVersion
          <> "; recompile it from source"
        else do
          entry <- getString
          sourceHash <- getString
          certificate <- getString
          report <- getReport
          expr <- getCompiled
          pure . Right $ Artifact entry sourceHash report certificate expr

writeArtifact :: FilePath -> Artifact -> IO ()
writeArtifact path = BL.writeFile path . encodeArtifact

readArtifact :: FilePath -> IO (Either String Artifact)
readArtifact path = decodeArtifact <$> BL.readFile path

-- Primitives.

putInt' :: Int -> Put
putInt' = putInt64le . fromIntegral

getInt' :: Get Int
getInt' = fromIntegral <$> getInt64le

putString :: String -> Put
putString s = do
  let bytes = BL.fromStrict (UTF8.fromString s)
  putInt' (fromIntegral (BL.length bytes))
  putLazyByteString bytes

getString :: Get String
getString = do
  n <- getInt'
  UTF8.toString . BL.toStrict <$> getLazyByteString (fromIntegral n)

putMaybe :: (a -> Put) -> Maybe a -> Put
putMaybe p = \case
  Nothing -> putWord8 0
  Just x  -> putWord8 1 >> p x

getMaybe :: Get a -> Get (Maybe a)
getMaybe g = getWord8 >>= \case
  0 -> pure Nothing
  _ -> Just <$> g

putList :: (a -> Put) -> [a] -> Put
putList p xs = putInt' (length xs) >> mapM_ p xs

getList :: Get a -> Get [a]
getList g = getInt' >>= \n -> mapM (const g) [1 .. n]

putMap :: (k -> Put) -> (v -> Put) -> Map k v -> Put
putMap pk pv = putList (\(k, v) -> pk k >> pv v) . Map.toAscList

getMap :: Ord k => Get k -> Get v -> Get (Map k v)
getMap gk gv = Map.fromList <$> getList ((,) <$> gk <*> gv)

-- Locations.

putPosition :: SourcePosition -> Put
putPosition p = do
  putInt' (sourcePositionLine p)
  putInt' (sourcePositionColumn p)
  putInt' (sourcePositionOffset p)

getPosition :: Get SourcePosition
getPosition = SourcePosition <$> getInt' <*> getInt' <*> getInt'

putSpan :: SourceSpan -> Put
putSpan s = do
  putMaybe putString (sourceSpanFile s)
  putPosition (sourceSpanStart s)
  putPosition (sourceSpanEnd s)

getSpan :: Get SourceSpan
getSpan = SourceSpan <$> getMaybe getString <*> getPosition <*> getPosition

putLocTag :: LocTag -> Put
putLocTag = \case
  SourceLoc s -> putWord8 0 >> putSpan s
  GeneratedLoc label parent -> putWord8 1 >> putString label >> putMaybe putLocTag parent
  BuiltinLoc label -> putWord8 2 >> putString label
  RuntimeLoc -> putWord8 3
  DecompiledLoc -> putWord8 4
  UnknownLoc -> putWord8 5

getLocTag :: Get LocTag
getLocTag = getWord8 >>= \case
  0 -> SourceLoc <$> getSpan
  1 -> GeneratedLoc <$> getString <*> getMaybe getLocTag
  2 -> BuiltinLoc <$> getString
  3 -> pure RuntimeLoc
  4 -> pure DecompiledLoc
  5 -> pure UnknownLoc
  n -> fail $ "unknown location tag " <> show n

putToken :: UnsizedRecursionToken -> Put
putToken = putInt' . unUnsizedRecursionToken

getToken :: Get UnsizedRecursionToken
getToken = UnsizedRecursionToken <$> getInt'

putReport :: SizingReport -> Put
putReport r = do
  putMap putToken (putMaybe putInt') (unSizedRecursion (sizingReportCounts r))
  putMap putToken putLocTag (sizingReportLocs r)
  putInt' (sizingReportBudget r)

getReport :: Get SizingReport
getReport = SizingReport . SizedRecursion
  <$> getMap getToken (getMaybe getInt')
  <*> getMap getToken getLocTag
  <*> getInt'

-- Terms.

putBasic :: BasicExpr -> Put
putBasic e = case project e of
  ZeroSF     -> putWord8 0
  PairSF a b -> putWord8 1 >> putBasic a >> putBasic b

getBasic :: Get BasicExpr
getBasic = getWord8 >>= \case
  0 -> pure (embed ZeroSF)
  1 -> (\a b -> embed (PairSF a b)) <$> getBasic <*> getBasic
  n -> fail $ "unknown basic node tag " <> show n

putCompiled :: CompiledExpr -> Put
putCompiled e = case project e of
  BasicFW ZeroSF -> putWord8 0
  BasicFW (PairSF a b) -> putWord8 1 >> putCompiled a >> putCompiled b
  StuckFW EnvSF -> putWord8 2
  StuckFW (SetEnvSF x) -> putWord8 3 >> putCompiled x
  StuckFW (DeferSF ind x) -> do
    putWord8 4
    putInt' (unFunctionIndex ind)
    putCompiled x
  StuckFW GateSF -> putWord8 5
  StuckFW (LeftSF x) -> putWord8 6 >> putCompiled x
  StuckFW (RightSF x) -> putWord8 7 >> putCompiled x
  AbortFW AbortF -> putWord8 8
  AbortFW (AbortedF b) -> putWord8 9 >> putBasic b
  _ -> error "Telomare.Artifact: unreachable compiled node"

getCompiled :: Get CompiledExpr
getCompiled = getWord8 >>= \case
  0 -> pure $ embed (BasicFW ZeroSF)
  1 -> (\a b -> embed (BasicFW (PairSF a b))) <$> getCompiled <*> getCompiled
  2 -> pure $ embed (StuckFW EnvSF)
  3 -> embed . StuckFW . SetEnvSF <$> getCompiled
  4 -> do
    ind <- FunctionIndex <$> getInt'
    embed . StuckFW . DeferSF ind <$> getCompiled
  5 -> pure $ embed (StuckFW GateSF)
  6 -> embed . StuckFW . LeftSF <$> getCompiled
  7 -> embed . StuckFW . RightSF <$> getCompiled
  8 -> pure $ embed (AbortFW AbortF)
  9 -> embed . AbortFW . AbortedF <$> getBasic
  n -> fail $ "unknown compiled node tag " <> show n
