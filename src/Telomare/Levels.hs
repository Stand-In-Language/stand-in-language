{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}

-- |Where each recursion site sits in the program's nesting of recursions, and
-- which bindings are used below the level they were bound at.
--
-- This is a purely structural reading of the parsed source: syntactic
-- containment, plus per-parameter offset summaries that let an offset compose
-- along a call chain. Nothing is evaluated and nothing is searched, so it
-- costs milliseconds on programs whose sizing costs a minute. That is the
-- whole point of it — it answers a different question than sizing does, and it
-- answers it cheaply.
--
-- A site at level @d@ has its test, recursion and last analyzed at @d + 1@. A
-- binding used @k@ levels below where it was bound is under duplication
-- pressure: every level between the two copies it. On `tictactoe.tel` that
-- names @whoWon.board@ at two levels down, which is the binding that made an
-- interaction-net backend for this language intractable.
--
-- What it is not: a termination proof, a runtime measurement, or a bound of
-- any kind. The counts that bound the program are the sizing pass's, reported
-- alongside these by "Telomare.Certificate".
--
-- Known approximation: a parameter applied as a function whose summary is
-- unknown contributes offset 0, so a recursion reached only through such a
-- parameter can be reported one level shallower than it truly is.
module Telomare.Levels
  ( -- * Running the analysis
    LevelsInfo (..)
  , levelsInfo
    -- * What it found
  , DefId (..)
  , SourceRef (..)
  , SiteKey (..)
  , Observation (..)
  , BindingKey (..)
    -- * Rendering pieces
  , renderDef
  , renderBinding
  , renderSource
  , renderLevels
  , bangs
  , pathChunks
  ) where

import Control.Comonad.Cofree (Cofree ((:<)))
import Data.Bifunctor (first)
import Data.Foldable (toList)
import Data.List (foldl', intercalate, sortOn)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Telomare.Error
import Telomare.IR.Base
import Telomare.IR.Builder
import Telomare.IR.Core
import Telomare.IR.Loc
import Telomare.IR.Surface
import Telomare.IR.Types
import Telomare.Parse (runParseModule)
import Telomare.Sugar (renderSugarError, sugarModule)

-- |A top-level definition, or a @let@ binding qualified by the definition it
-- appears in.
data DefId = DefId
  { defModule :: !String
  , defName   :: !String
  }
  deriving (Eq, Ord, Show)

-- |Where something is, as far as the parser recorded it.
data SourceRef = SourceRef
  { srcFile     :: !(Maybe FilePath)
  , srcLine     :: !(Maybe Int)
  , srcColumn   :: !(Maybe Int)
  , srcOffset   :: !(Maybe Int)
  , srcFallback :: !(Maybe String)
  -- ^What the location tag says when it is not a source span.
  }
  deriving (Eq, Ord, Show)

-- |A recursion site, identified by where it is written.
data SiteKey = SiteKey
  { siteOwner  :: !DefId
  , siteSource :: !SourceRef
  }
  deriving (Eq, Ord, Show)

-- |One site, seen at one level, reached along one static path. A site written
-- once can be observed at several levels: it is used from several places.
data Observation = Observation
  { obsSite  :: !SiteKey
  , obsLevel :: !Int
  , obsPath  :: ![DefId]
  }
  deriving (Eq, Show)

data BindingKey = BindingKey
  { bindingOwner :: !DefId
  , bindingName  :: !String
  }
  deriving (Eq, Ord, Show)

-- |What the structural pass found.
data LevelsInfo = LevelsInfo
  { levelsEntry        :: !DefId
  , levelsSites        :: ![(SiteKey, Set Int)]
  -- ^Every recursion site reachable from the entry, and the levels it is
  -- observed at.
  , levelsObservations :: ![Observation]
  -- ^One entry per (site, level, path) witness.
  , levelsBangs        :: ![(BindingKey, Int)]
  -- ^Bindings used below their binding level, and by how much.
  , levelsMaxDepth     :: !Int
  }
  deriving (Eq, Show)

-- |Analyze the modules, starting from the entry module's @main@.
levelsInfo :: [(String, String)] -- ^All modules as (Module_Name, Module_Content)
           -> String -- ^Name of the module holding `main`
           -> Either String LevelsInfo
levelsInfo moduleSrcs entry = do
  parsed <- parseModules moduleSrcs
  let entryId = DefId entry "main"
  mainDef <- maybe (Left $ "no entry definition " <> renderDef entryId) Right
    (lookupEntry entryId parsed)
  pure . summarize entryId $
    walk (globalEnv parsed) Map.empty Map.empty entryId [entryId] 0 mainDef emptySt

summarize :: DefId -> St -> LevelsInfo
summarize entryId st = LevelsInfo
  { levelsEntry = entryId
  , levelsSites = sortOn (\(site, _) -> (siteSource site, siteOwner site)) grouped
  , levelsObservations = observations
  , levelsBangs = sortOn (\(b, k) -> (negate k, bindingOwner b, bindingName b))
      [row | row@(_, k) <- Map.toList (stBangs st), k > 0]
  , levelsMaxDepth = maximumOr 0 (fmap ((+ 1) . obsLevel) observations)
  }
  where
    observations = sortOn obsSort (reverse (stObservations st))
    obsSort o = (siteSource (obsSite o), siteOwner (obsSite o), obsLevel o, obsPath o)
    grouped = Map.toList $ Map.fromListWith Set.union
      [(obsSite obs, Set.singleton (obsLevel obs)) | obs <- observations]

-- Each module is parsed under its bare name, the same way
-- `Telomare.Eval.compileModulesWith` parses it, so that a site's location here
-- and the same site's location in the sizing report are the same string.
-- Desugaring runs here too: this module walks the AST directly and only
-- understands the post-sugar vocabulary.
parseModules :: [(String, String)]
             -> Either String [(String, [Either AUPT (String, AUPT)])]
parseModules = traverse parseOne
  where
    parseOne (name, src) =
      either (Left . ((name <> ": ") <>)) (Right . (name,)) $
        runParseModule name src
          >>= first renderSugarError . fmap unSugared . sugarModule

lookupEntry :: DefId
            -> [(String, [Either AUPT (String, AUPT)])]
            -> Maybe AUPT
lookupEntry entryId parsed = lookup (defName entryId)
  [ (name, def)
  | (moduleName, entries) <- parsed
  , moduleName == defModule entryId
  , Right (name, def) <- entries
  ]

data DefInfo = DefInfo
  { diId   :: !DefId
  , diBody :: !AUPT
  }

type GlobalEnv = Map String DefInfo

data LocalInfo = LocalInfo
  { liId   :: !DefId
  , liBody :: !AUPT
  }

type LocalEnv = Map String LocalInfo

type AEnv = Map String AUPT

type Binds = Map String (BindingKey, Int)

data St = St
  { stVisited      :: !(Set (DefId, Int))
  , stObservations :: ![Observation]
  , stBangs        :: !(Map BindingKey Int)
  }

emptySt :: St
emptySt = St Set.empty [] Map.empty

globalEnv :: [(String, [Either AUPT (String, AUPT)])] -> GlobalEnv
globalEnv = foldl' addModule Map.empty
  where
    addModule env (moduleName, entries) = foldl' (addDef moduleName) env entries
    addDef moduleName env = \case
      Right (name, def) -> Map.insertWith keepExisting name
        (DefInfo (DefId moduleName name) def) env
      Left _ -> env
    keepExisting _ old = old

collectLams :: AUPT -> ([String], AUPT)
collectLams (_ :< UnprocessedParsedTermL (LamF (LocatedName (_, n)) b)) =
  let (ps, body) = collectLams b in (n : ps, body)
collectLams x = ([], x)

spine :: AUPT -> (AUPT, [AUPT])
spine (_ :< UnprocessedParsedTermL (AppF f x)) =
  let (h, args) = spine f in (h, args <> [x])
spine x = (x, [])

varName :: AUPT -> Maybe String
varName (_ :< UnprocessedParsedTermL (VarF v)) = Just v
varName _                                      = Nothing

maximumOr :: Int -> [Int] -> Int
maximumOr z [] = z
maximumOr _ xs = maximum xs

-- |How deep, in levels, each of a definition's leading parameters is used
-- inside its own body. This is what lets an offset compose along a call chain:
-- passing an argument to a parameter that is itself used one level down puts
-- that argument one level down.
paramOffsets :: AEnv -> Set String -> AUPT -> [Int]
paramOffsets env guard def =
  let (params, body) = collectLams def
  in fmap (\p -> occDepth env guard p 0 body) params

occDepth :: AEnv -> Set String -> String -> Int -> AUPT -> Int
occDepth env guard p d t@(_ :< node) = case node of
  UnprocessedParsedTermL (VarF v) -> if v == p then d else 0
  UnprocessedParsedTermL (LamF (LocatedName (_, n)) b)
    | n == p -> 0
    | otherwise -> occDepth env guard p d b
  UnprocessedParsedTermL (AppF _ _) ->
    let (h, args) = spine t
        offs = headOffsets env guard h
        argD (j, arg) = occDepth env guard p (d + offAt offs j) arg
    in maximumOr 0 (occDepth env guard p d h : fmap argD (zip [0 ..] args))
  UnprocessedParsedTermH (RecursionF a b c) ->
    maximumOr 0 (fmap (occDepth env guard p (d + 1)) [a, b, c])
  LetUPF bs body
    | p `elem` [n | (LocatedName (_, n), _) <- bs] -> 0
    | otherwise -> maximumOr 0
        (occDepth env guard p d body : fmap (occDepth env guard p d . snd) bs)
  other -> maximumOr 0 (fmap (occDepth env guard p d) (toList other))

headOffsets :: AEnv -> Set String -> AUPT -> [Int]
headOffsets env guard h = case varName h of
  Just v
    | v `Set.notMember` guard
    , Just def <- Map.lookup v env -> paramOffsets env (Set.insert v guard) def
  _ -> []

offAt :: [Int] -> Int -> Int
offAt offs j = if j < length offs then offs !! j else 0

-- |The walk. A definition is entered at most once per level, which is what
-- bounds the traversal.
walk :: GlobalEnv -> LocalEnv -> Binds -> DefId -> [DefId] -> Int -> AUPT -> St -> St
walk gs ls bn owner path d t@(ann :< node) st = case node of
  UnprocessedParsedTermH (RecursionF a b c) ->
    let obs = Observation (SiteKey owner (sourceRef ann)) d path
        st1 = st { stObservations = obs : stObservations st }
    in foldl' (flip (walk gs ls bn owner path (d + 1))) st1 [a, b, c]
  UnprocessedParsedTermL (AppF _ _) ->
    let (h, args) = spine t
        offs = headOffsets (auptEnv gs ls) Set.empty h
        st1 = walk gs ls bn owner path d h st
    in foldl' (\s (j, arg) -> walk gs ls bn owner path (d + offAt offs j) arg s)
              st1 (zip [0 ..] args)
  UnprocessedParsedTermL (VarF v) -> enterVar v (bang v st)
  UnprocessedParsedTermL (LamF (LocatedName (_, n)) b) ->
    let bn' = Map.insert n (BindingKey owner n, d) bn
    in walk gs (Map.delete n ls) bn' owner path d b st
  LetUPF bs body ->
    let localInfo (LocatedName (_, n), rhs) = (n, LocalInfo (localDef owner n) rhs)
        ls' = foldl' (\m b -> uncurry Map.insert (localInfo b) m) ls bs
        bn' = foldl' (\m (LocatedName (_, n), _) -> Map.insert n (BindingKey owner n, d) m)
                     bn bs
    in walk gs ls' bn' owner path d body st
  other -> foldl' (flip (walk gs ls bn owner path d)) st (toList other)
  where
    bang v s = case Map.lookup v bn of
      Nothing -> s
      Just (binding, bd) ->
        s { stBangs = Map.insertWith max binding (d - bd) (stBangs s) }
    enterVar v s
      | Set.member (nextOwner v, d) (stVisited s) = s
      | Just local <- Map.lookup v ls =
          let owner' = liId local
          in walk gs ls bn owner' (path <> [owner']) d (liBody local) (mark owner' s)
      | Just global <- Map.lookup v gs =
          let owner' = diId global
          in walk gs Map.empty Map.empty owner' (path <> [owner']) d (diBody global)
               (mark owner' s)
      | otherwise = s
    nextOwner v = maybe (maybe owner diId (Map.lookup v gs)) liId (Map.lookup v ls)
    mark owner' s = s { stVisited = Set.insert (owner', d) (stVisited s) }

auptEnv :: GlobalEnv -> LocalEnv -> AEnv
auptEnv gs ls = Map.map liBody ls `Map.union` Map.map diBody gs

localDef :: DefId -> String -> DefId
localDef owner name = owner { defName = defName owner <> "." <> name }

sourceRef :: LocTag -> SourceRef
sourceRef = \case
  SourceLoc spn -> fromSpan spn
  GeneratedLoc _ (Just parent) -> sourceRef parent
  GeneratedLoc reason Nothing -> fallback ("generated " <> reason)
  BuiltinLoc name -> fallback ("builtin " <> name)
  RuntimeLoc -> fallback "runtime"
  DecompiledLoc -> fallback "decompiled"
  UnknownLoc -> fallback "unknown"
  where
    fallback label = SourceRef Nothing Nothing Nothing Nothing (Just label)

fromSpan :: SourceSpan -> SourceRef
fromSpan spn = SourceRef
  { srcFile = sourceSpanFile spn
  , srcLine = Just line
  , srcColumn = Just column
  , srcOffset = Just offset
  , srcFallback = Nothing
  }
  where
    SourcePosition line column offset = sourceSpanStart spn

renderSource :: SourceRef -> String
renderSource ref = case (srcFile ref, srcLine ref, srcColumn ref, srcFallback ref) of
  (Just file, Just line, Just column, _) -> file <> ":" <> show line <> ":" <> show column
  (_, Just line, Just column, _)         -> "<source>:" <> show line <> ":" <> show column
  (_, _, _, Just label)                  -> label
  _                                      -> "unknown"

renderDef :: DefId -> String
renderDef d = defModule d <> "." <> defName d

renderBinding :: BindingKey -> String
renderBinding b = renderDef (bindingOwner b) <> "." <> bindingName b

renderLevels :: Set Int -> String
renderLevels = intercalate ", " . fmap show . Set.toAscList

bangs :: Int -> String
bangs k = replicate k '!'

-- |A long static path, broken into readable lines.
pathChunks :: [String] -> [String]
pathChunks xs = case fmap (intercalate " > ") (chunksOf 4 xs) of
  []     -> []
  y : ys -> y : fmap ("> " <>) ys
  where
    chunksOf _ [] = []
    chunksOf n ys = take n ys : chunksOf n (drop n ys)
