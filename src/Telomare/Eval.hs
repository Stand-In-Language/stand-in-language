{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-deferred-out-of-scope-variables #-}
{-# LANGUAGE TupleSections       #-}

module Telomare.Eval where

import Control.Comonad.Cofree (Cofree ((:<)), hoistCofree)
import Control.Lens.Plated (Plated (..), transform, transformM)
import Control.Monad (void)
import Control.Monad.State (State, StateT, evalState)
import qualified Control.Monad.State as State
import Control.Monad.Trans.Accum (AccumT)
import qualified Control.Monad.Trans.Accum as Accum
import Data.Bifunctor (first, second)
import Data.DList (DList)
import Data.Foldable (fold)
import Data.Functor.Foldable (cata, embed, project)
import Data.List (partition)
import Data.Semigroup (Min(..), Max(..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void
import Debug.Trace
import System.IO
import System.Process

import PrettyPrint
import Telomare (BreakState, BreakState', ExprA (..), FragExpr (..),
                 FragExprF (..), FragIndex (FragIndex), IExpr (..), LocTag (..),
                 PartialType (..), RecursionPieceFrag,
                 RecursionSimulationPieces (..), RunTimeError (..),
                 TelomareLike (..), Term3 (Term3), Term4 (Term4),
                 UnsizedRecursionToken (..), app, appF, eval, convertAbortMessage, deferF, forget, g2s,
                 innerChurchF, insertAndGetKey, pairF,
                 rootFrag, s2g, setEnvF, tag, unFragExprUR, cataFragExprUR)
import Telomare.Optimizer (optimize)
import Telomare.Parser (AnnotatedUPT, parsePrelude)
import Telomare.Possible (abortExprToTerm4, buildUnsizedLocMap, evalA, getSizesM, sizeTerm, sizeTermM, term3ToUnsizedExpr, abortPossibilities)
import Telomare.PossibleData (AbortExpr, VoidF, SizedRecursion(..))
-- import Telomare.Resolver (parseMain)
import Telomare.RunTime (hvmEval, optimizedEval, pureEval, simpleEval)
import Telomare.TypeChecker (TypeCheckError (..), typeCheck)
import qualified Control.Comonad.Trans.Cofree as CofreeT
import Data.Bifunctor (bimap, first)
import Data.Function (fix)
import Data.Functor.Foldable (Base, para, cata)
import Data.Map (Map)
import qualified Data.Map as Map
import Debug.Trace (trace)
import PrettyPrint (prettyPrint)
import System.IO (hGetContents)
import qualified System.IO.Strict as Strict
import System.Process (CreateProcess (std_out), StdStream (CreatePipe),
                       createProcess, shell)
import Telomare
import Telomare.Optimizer (optimize)
import Telomare.Parser (AnnotatedUPT, parseModule, parseOneExprOrTopLevelDefs)
import Telomare.Possible (abortExprToTerm4, evalA, sizeTerm,
                          term3ToUnsizedExpr, term4toAbortExpr)
import Telomare.PossibleData (StaticCheckExpr, convertBasic, convertStuck, convertAbort)
import Telomare.Resolver (main2Term3, process, resolveAllImports)
import Telomare.RunTime (pureEval, rEval)
import Telomare.TypeChecker (TypeCheckError (..), typeCheck)
import Text.Megaparsec (errorBundlePretty, runParser)

debug :: Bool
debug = False

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

data ExpP = ZeroP
    | PairP ExpP ExpP
    | VarP
    | SetEnvP ExpP Bool
    | DeferP ExpP
    | AbortP
    | GateP ExpP ExpP
    | LeftP ExpP
    | RightP ExpP
    | TraceP
    deriving (Eq, Show, Ord)

instance Plated ExpP where
  plate f = \case
    PairP a b   -> PairP <$> f a <*> f b
    SetEnvP x b -> SetEnvP <$> f x <*> pure b
    DeferP x    -> DeferP <$> f x
    GateP l r   -> GateP <$> f l <*> f r
    LeftP x     -> LeftP <$> f x
    RightP x    -> RightP <$> f x
    x           -> pure x

data EvalError = RTE RunTimeError
    | TCE TypeCheckError
    | StaticCheckError String
    | CompileConversionError
    | RecursionLimitError UnsizedRecursionToken
    deriving (Eq, Ord, Show)

type ExpFullEnv = ExprA Bool

newtype BetterMap k v = BetterMap { unBetterMap :: Map k v}

instance Functor (BetterMap k) where
  fmap f (BetterMap x) = BetterMap $ fmap f x

instance (Ord k, Semigroup m) => Semigroup (BetterMap k m) where
  (<>) (BetterMap a) (BetterMap b) = BetterMap $ Map.unionWith (<>) a b

annotateEnv :: IExpr -> (Bool, ExpP)
annotateEnv Zero = (True, ZeroP)
annotateEnv (Pair a b) =
  let (at, na) = annotateEnv a
      (bt, nb) = annotateEnv b
  in (at && bt, PairP na nb)
annotateEnv Env = (False, VarP)
annotateEnv (SetEnv x) = let (xt, nx) = annotateEnv x in (xt, SetEnvP nx xt)
annotateEnv (Defer x) = let (_, nx) = annotateEnv x in (True, DeferP nx)
annotateEnv (Gate a b) =
  let (at, na) = annotateEnv a
      (bt, nb) = annotateEnv b
  in (at && bt, GateP na nb)
annotateEnv (PLeft x) = LeftP <$> annotateEnv x
annotateEnv (PRight x) = RightP <$> annotateEnv x
annotateEnv Trace = (False, TraceP)

fromFullEnv :: (ExpP -> IExpr) -> ExpP -> IExpr
fromFullEnv _ ZeroP         = Zero
fromFullEnv f (PairP a b)   = Pair (f a) (f b)
fromFullEnv _ VarP          = Env
fromFullEnv f (SetEnvP x _) = SetEnv (f x)
fromFullEnv f (DeferP x)    = Defer (f x)
fromFullEnv f (GateP a b)   = Gate (f a) (f b)
fromFullEnv f (LeftP x)     = PLeft (f x)
fromFullEnv f (RightP x)    = PRight (f x)
fromFullEnv _ TraceP        = Trace

instance TelomareLike ExpP where
  fromTelomare = snd . annotateEnv
  toTelomare = pure . fix fromFullEnv

partiallyEvaluate :: ExpP -> IExpr
partiallyEvaluate se@(SetEnvP _ True) = Defer (pureEval . optimize $ fix fromFullEnv se)
partiallyEvaluate x = fromFullEnv partiallyEvaluate x

convertPT :: (UnsizedRecursionToken -> Int) -> Term3 -> Term4
convertPT ll (Term3 termMap) =
  let unURedMap = Map.map unFragExprUR termMap
      startKey = succ . fst $ Map.findMax termMap
      changeFrag :: Cofree (FragExprF RecursionPieceFrag) LocTag
                 -> State.State
                      ((), FragIndex,
                       Map
                         FragIndex
                         (Cofree (FragExprF RecursionPieceFrag) LocTag))
                      (Cofree (FragExprF RecursionPieceFrag) LocTag)
      changeFrag = \case
        anno :< AuxFragF (NestedSetEnvs n) -> innerChurchF anno $ ll n
        _ :< AuxFragF (SizingWrapper _ _ x) -> transformM changeFrag $ unFragExprUR x
        _ :< AuxFragF (CheckingWrapper anno tc c) ->
          let performTC = deferF ((\ia -> setEnvF (pairF (setEnvF (pairF (pure $ tag anno AbortFrag) ia))
                                                        (pure . tag anno $ RightFrag EnvFrag))) $ appF (pure . tag anno $ LeftFrag EnvFrag)
                                                                                                       (pure . tag anno $ RightFrag EnvFrag))
          in setEnvF (pairF performTC (pairF (transformM changeFrag $ unFragExprUR tc) (transformM changeFrag $ unFragExprUR c)))
        x -> pure x
      insertChanged :: FragIndex
                    -> Cofree (FragExprF RecursionPieceFrag) LocTag
                    -> BreakState RecursionPieceFrag () ()
      insertChanged nk nv = State.modify (\(_, k, m) -> ((), k, Map.insert nk nv m))
      builder = sequence $ Map.mapWithKey (\k v -> transformM changeFrag v >>= insertChanged k) unURedMap
      (_,_,newMap) = State.execState builder ((), startKey, unURedMap)
      changeType :: FragExprF a x -> FragExprF b x
      changeType = \case
        ZeroFragF      -> ZeroFragF
        PairFragF a b  -> PairFragF a b
        EnvFragF       -> EnvFragF
        SetEnvFragF x  -> SetEnvFragF x
        DeferFragF ind -> DeferFragF ind
        AbortFragF     -> AbortFragF
        GateFragF l r  -> GateFragF l r
        LeftFragF x    -> LeftFragF x
        RightFragF x   -> RightFragF x
        TraceFragF     -> TraceFragF
        AuxFragF z     -> error "convertPT should be no AuxFrags here TODO"
  in Term4 $ fmap (hoistCofree changeType) newMap

findChurchSizeD :: Bool -> Term3 -> Either EvalError Term4
findChurchSizeD useSizing t3 =
  if useSizing
    then calculateRecursionLimits t3  -- Use sizing algorithm
    else pure (convertPT (const 255) t3)  -- Use fixed size of 255

findChurchSize :: Term3 -> Either EvalError Term4
findChurchSize = findChurchSizeD False -- True

-- we should probably redo the types so that this is also a type conversion
removeChecks :: Term4 -> Term4
removeChecks (Term4 m) =
  let f = \case
        anno :< AbortFragF -> anno :< DeferFragF ind
        x                  -> x
      (ind, newM) = State.runState builder m
      builder = do
        envDefer <- insertAndGetKey $ DummyLoc :< EnvFragF
        insertAndGetKey $ DummyLoc :< DeferFragF envDefer
  in Term4 $ Map.map (transform f) newM

runStaticChecks :: Term4 -> Either EvalError Term4
runStaticChecks t@(Term4 termMap) =
  let result = evalA scTerm
      scTerm = term4toAbortExpr t
  in case debugTrace ("running static checks for:\n" <> prettyPrint t) result of
    Nothing -> pure t
    Just e  -> Left . StaticCheckError $ convertAbortMessage e

compileMain :: Term3 -> Either EvalError IExpr
compileMain term = case typeCheck (PairTypeP (ArrTypeP ZeroTypeP ZeroTypeP) AnyType) term of
  Just e -> Left $ TCE e
  _      -> compile pure term -- TODO add runStaticChecks back in

-- for testing
compileMain' :: Term3 -> Either EvalError IExpr
compileMain' = compile pure

compileUnitTest :: Term3 -> Either EvalError IExpr
compileUnitTest = compile runStaticChecks

compile :: (Term4 -> Either EvalError Term4) -> Term3 -> Either EvalError IExpr
compile staticCheck t = debugTrace ("compiling term3:\n" <> prettyPrint t)
  $ case toTelomare . removeChecks <$> (findChurchSize t >>= staticCheck) of
      Right (Just i) -> pure i
      Right Nothing  -> Left CompileConversionError
      Left e         -> Left e

-- converts between easily understood Haskell types and untyped IExprs around an iteration of a Telomare expression
funWrap :: (IExpr -> IExpr) -> IExpr -> Maybe (String, IExpr) -> (String, Maybe IExpr)
funWrap eval fun inp =
  let iexpInp = case inp of
        Nothing                  -> Zero
        Just (userInp, oldState) -> Pair (s2g userInp) oldState
  in case eval (app fun iexpInp) of
    Zero               -> ("aborted", Nothing)
    Pair disp newState -> (g2s disp, Just newState)
    z                  -> ("runtime error, dumped:\n" <> show z, Nothing)

runMainCore :: [(String, String)] -> String -> (IExpr -> IO a) -> IO a
runMainCore modulesStrings s e =
  let parsedModules :: [(String, Either String [Either AnnotatedUPT (String, AnnotatedUPT)])]
      parsedModules = (fmap . fmap) parseModule modulesStrings
      parsedModulesErrors :: [(String, Either String [Either AnnotatedUPT (String, AnnotatedUPT)])]
      parsedModulesErrors = filter (\(moduleStr, parsed) -> case parsed of
                                      Left _  -> True
                                      Right _ -> False)
                                   parsedModules
      flattenLeft = \case
        Left a -> a
        Right a -> error "flattenLeft error: got a Right when it should be Left"
      flattenRight = \case
        Right a -> a
        Left a -> error "flattenRight error: got a Left when it should be Right"
      modules :: [(String, [Either AnnotatedUPT (String, AnnotatedUPT)])]
      modules =
        case parsedModulesErrors of
          [] -> (fmap . fmap) flattenRight parsedModules
          errors -> let moduleWithError :: [(String, String)]
                        moduleWithError = (fmap . fmap) flattenLeft parsedModulesErrors
                        joinModuleError :: (String, String) -> String
                        joinModuleError (moduleName, errorStr) = "Error in module " <> moduleName <> ":\n" <> errorStr
                    in error . unlines $ joinModuleError <$> moduleWithError

  in
    case compileMain <$> main2Term3 modules s of
      Left e -> error $ concat ["failed to parse ", s, " ", e]
      Right (Right g) -> e g
      Right z -> error $ "compilation failed somehow, with result " <> show z

runMain_ :: [(String, String)] -> String -> IO String
runMain_ modulesStrings s = runMainCore modulesStrings s evalLoop_

runMain :: [(String, String)] -> String -> IO ()
runMain modulesStrings s = runMainCore modulesStrings s evalLoop

runMainWithInput :: [String] -> [(String, String)] -> String -> IO String
runMainWithInput inputList modulesStrings s = runMainCore modulesStrings s (evalLoopWithInput inputList)

schemeEval :: IExpr -> IO ()
schemeEval iexpr = do
  writeFile "scheme.txt" ('(' : (show (app iexpr Zero) <> ")"))
  (_, Just mhout, _, _) <- createProcess (shell "chez-script runtime.so") { std_out = CreatePipe }
  scheme <- hGetContents mhout
  putStrLn scheme

evalLoopCore :: IExpr
             -> (String -> String -> IO String)
             -> String
             -> [String]
             -> IO String
evalLoopCore iexpr accumFn initAcc manualInput =
  let wrappedEval :: Maybe (String, IExpr) -> (String, Maybe IExpr)
      wrappedEval = funWrap eval iexpr
      mainLoop :: String -> [String] -> Maybe (String, IExpr) -> IO String
      mainLoop acc strInput s = do
        let (out, nextState) = wrappedEval s
        newAcc <- accumFn acc out
        case nextState of
          Nothing -> pure acc
          Just Zero -> pure $ newAcc <> "\n" <> "done"
          Just ns -> do
            (inp, rest) <-
              if null strInput
              then (, []) <$> getLine
              else pure (head strInput, tail strInput)
            mainLoop newAcc rest $ pure (inp, ns)
  in mainLoop initAcc manualInput Nothing

evalLoop :: IExpr -> IO ()
evalLoop iexpr = void $ evalLoopCore iexpr printAcc "" []
  where
    printAcc _ out = do
      putStrLn out
      pure ""

evalLoopWithInput :: [String] -> IExpr -> IO String
evalLoopWithInput inputList iexpr = evalLoopCore iexpr printAcc "" inputList
  where
    printAcc acc out = if acc == ""
                       then pure out
                       else pure (acc <> "\n" <> out)

-- |Same as `evalLoop`, but keeping what was displayed.
evalLoop_ :: IExpr -> IO String
evalLoop_ iexpr = evalLoopCore iexpr printAcc "" []
  where
    printAcc acc out = if acc == ""
                       then pure out
                       else pure (acc <> "\n" <> out)

calculateRecursionLimits :: Term3 -> Either EvalError Term4
calculateRecursionLimits t3 =
  let abortExprToTerm4' :: AbortExpr -> Either IExpr Term4
      abortExprToTerm4' = abortExprToTerm4
      limitSize = 256
  in case fmap abortExprToTerm4' . sizeTermM limitSize $ term3ToUnsizedExpr limitSize t3 of
    Left urt -> Left $ RecursionLimitError urt
    Right t  -> case t of
      Left a  -> Left . StaticCheckError . convertAbortMessage $ a
      Right t -> pure t

-- takes a main function and sizes the unsized recursion and then displays the results as comments in the original source
showSizingInSource :: String -> String -> String
showSizingInSource prelude s
  = let asLines = zip [0..] $ lines s
        parsed = parsePrelude prelude >>= (\p -> parseMain p s)
        unsizedExpr = term3ToUnsizedExpr 256 <$> parsed
        sizedRecursion = unsizedExpr >>= (first (("Could not size token: " <>) . show) . getSizesM 256)
        sizeLocs = Map.toAscList . buildUnsizedLocMap <$> unsizedExpr
        -- (orphanLocs, lineLocs) = partition ((== DummyLoc) . snd) sizeLocs
        (orphanLocs, lineLocs) = case sizeLocs of
          Left e -> error ("Could not size: " <> show e)
          Right sl -> partition ((== DummyLoc) . snd) sl
        -- orphanList = map ((<> " ") . show . fst) orphanLocs
        orphans = "unsized with no location: " <> fold (map ((<> " ") . show . fst) orphanLocs)
        fromEnum' = \case
          Loc x _ -> x
          _ -> error "unexpected DummyLoc"
        lookupSize x = case sizedRecursion of
          Right (SizedRecursion sm) -> case Map.lookup x sm of
            Just (Just v) -> show v
            _ -> "?"
          _ -> "?"
        -- getSizeMatchingLine x = foldMap ((<> " ") . show) $ filter ((== x) . fromEnum' . snd) lineLocs
        getSizeMatchingLine x = case filter ((== x) . fromEnum' . snd) lineLocs of
          [] -> ""
          l -> ("   # " <>) $ foldMap ((\s -> show (fromEnum s) <> ":" <> lookupSize s <> " ") . fst) l
    in "showSizingInSource\n" <> orphans <> "\n" <> foldMap (\(l, s) -> s <> getSizeMatchingLine l <> "\n") asLines

showFunctionIndexesInSource :: String -> String -> String
showFunctionIndexesInSource prelude s
  = let asLines = zip [1..] $ lines s
        -- parsed = parsePrelude prelude >>= (\p -> parseMain p s)
        funMap = case parsePrelude prelude >>= (\p -> parseMain p s) of
          Right (Term3 f) -> f
          e -> error ("could not parse " <> show e)
        unAss (a :< _) = a
        -- sizeLocs = (\(fi, t) -> (fi))
        reduceL (a CofreeT.:< x) = let l = fromEnum' a in (Min l, Max l) <> fold x
        bodyLocs = second (cataFragExprUR reduceL) <$> Map.toAscList funMap
        sizeLocs = second (unAss . unFragExprUR) <$> Map.toAscList funMap
        (orphanLocs, lineLocs) = partition ((== DummyLoc) . snd) sizeLocs
        orphans = "functions with no location: " <> fold (map ((<> " ") . show . fst) orphanLocs)
        fromEnum' = \case
          Loc x _ -> x
          _ -> 0 -- error "unexpected DummyLoc"
        getFunMatchingLine x = case filter ((== x) . fromEnum' . snd) lineLocs of
          [] -> ""
          -- l -> ("   # " <>) $ foldMap ((\s -> show (fromEnum s) <> ":" <> lookupSize s <> " ") . fst) l
          l -> ("   # " <>) $ foldMap ((<> " ") . show . fromEnum . fst) l
    -- in "showFunInSource\n" <> orphans <> "\nBodyLocs\n" <> show bodyLocs <> "\n" <> foldMap (\(l, s) -> s <> getFunMatchingLine l <> "\n") asLines
    in "showFunInSource\n" <> orphans <> "\n" <> foldMap (\(l, s) -> s <> getFunMatchingLine l <> "\n") asLines

parseMain :: [(String, AnnotatedUPT)] -- ^Prelude: [(VariableName, BindedUPT)]
          -> String                            -- ^Raw string to be parserd.
          -> Either String Term3               -- ^Error on Left.
parseMain prelude' str =
  let prelude :: [(String, [Either AnnotatedUPT (String, AnnotatedUPT)])]
      prelude = [("Prelude", Right <$> prelude')]
      parseAuxModule :: String -> (String, [Either AnnotatedUPT (String, AnnotatedUPT)])
      parseAuxModule str =
        case sequence ("AuxModule", parseModule ("import Prelude\n" <> str)) of
          Left e    -> error $ show e
          Right pam -> pam
  in main2Term3 (parseAuxModule str:prelude) "AuxModule"

getAbortPossibilities :: String -> String -> Set IExpr
getAbortPossibilities prelude s
  = let parsed = parsePrelude prelude >>= (\p ->parseMain p s)
        unsizedExpr = term3ToUnsizedExpr 256 <$> parsed
    in case unsizedExpr of
         Left e -> error $ "getAbortPossibilities: " <> show e
         Right ue -> abortPossibilities 256 ue

getAbortPossibilities' :: String -> String -> Set String
getAbortPossibilities' prelude s
  = let parsed = parsePrelude prelude >>= (\p ->parseMain p s)
        unsizedExpr = term3ToUnsizedExpr 256 <$> parsed
    in case unsizedExpr of
         Left e -> error $ "getAbortPossibilities: " <> show e
         Right ue -> Set.map convertAbortMessage $ abortPossibilities 256 ue

eval2IExpr :: [(String, [Either AnnotatedUPT (String, AnnotatedUPT)])] -> String -> Either String IExpr
eval2IExpr extraModuleBindings str =
  first errorBundlePretty (runParser (parseOneExprOrTopLevelDefs resolved) "" str)
  >>= process
  >>= first show . compileUnitTest
    where
      aux = (\str -> Left (DummyLoc :< ImportQualifiedUPF str str)) . fst <$> extraModuleBindings
      resolved = resolveAllImports extraModuleBindings aux

tagIExprWithEval :: IExpr -> Cofree IExprF (Int, IExpr)
tagIExprWithEval iexpr = evalState (para alg iexpr) 0 where
  statePlus1 :: State Int Int
  statePlus1 = do
      i <- State.get
      State.modify (+ 1)
      pure i
  alg :: Base IExpr
              ( IExpr
              , State Int (Cofree IExprF (Int, IExpr))
              )
      -> State Int (Cofree IExprF (Int, IExpr))
  alg = \case
    ZeroF -> do
      i <- statePlus1
      pure ((i, rEval Zero Zero) :< ZeroF)
    EnvF -> do
      i <- statePlus1
      pure ((i, rEval Zero Env) :< EnvF)
    TraceF -> do
      i <- statePlus1
      pure ((i, rEval Zero Trace) :< TraceF)
    SetEnvF (iexpr0, x) -> do
      i <- statePlus1
      x' <- x
      pure $ (i, rEval Zero $ SetEnv iexpr0) :< SetEnvF x'
    DeferF (iexpr0, x) -> do
      i <- statePlus1
      x' <- x
      pure $ (i, rEval Zero $ Defer iexpr0) :< DeferF x'
    PLeftF (iexpr0, x) -> do
      i <- statePlus1
      x' <- x
      pure $ (i, rEval Zero $ PLeft iexpr0) :< PLeftF x'
    PRightF (iexpr0, x) -> do
      i <- statePlus1
      x' <- x
      pure $ (i, rEval Zero $ PRight iexpr0) :< PRightF x'
    PairF (iexpr0, x) (iexpr1, y) -> do
      i <- statePlus1
      x' <- x
      y' <- y
      pure $ (i, rEval Zero $ Pair iexpr0 iexpr1) :< PairF x' y'
    GateF (iexpr0, x) (iexpr1, y) -> do
      i <- statePlus1
      x' <- x
      y' <- y
      pure $ (i, rEval Zero $ Gate iexpr0 iexpr1) :< GateF x' y'

tagUPTwithIExpr :: [(String, AnnotatedUPT)]
                -> UnprocessedParsedTerm
                -> Cofree UnprocessedParsedTermF (Int, Either String IExpr)
tagUPTwithIExpr prelude upt = evalState (para alg upt) 0 where
  upt2iexpr :: UnprocessedParsedTerm -> Either String IExpr
  upt2iexpr u = process (tag DummyLoc u) >>= first show . compileUnitTest
  alg :: Base UnprocessedParsedTerm
              ( UnprocessedParsedTerm
              , State Int (Cofree UnprocessedParsedTermF (Int, Either String IExpr))
              )
      -> State Int (Cofree UnprocessedParsedTermF (Int, Either String IExpr))
  alg = \case
    ITEUPF (utp1, x) (utp2, y) (utp3, z) -> do
      i <- State.get
      State.modify (+ 1)
      x' <- x
      y' <- y
      z' <- z
      pure $ (i, upt2iexpr $ ITEUP utp1 utp2 utp3) :< ITEUPF x' y' z'
    ListUPF l -> do
      i <- State.get
      State.modify (+ 1)
      let scupt :: State Int [Cofree UnprocessedParsedTermF (Int, Either String IExpr)]
          scupt = mapM snd l
      cupt <- scupt
      pure $ (i, upt2iexpr . ListUP $ fst <$> l) :< ListUPF cupt
    LetUPF l (upt0, x) -> do
      i <- State.get
      State.modify (+ 1)
      let lupt :: [(String, UnprocessedParsedTerm)]
          lupt = (fmap . fmap) fst l
          slcupt :: State Int
                     [Cofree UnprocessedParsedTermF (Int, Either String IExpr)]
          slcupt = mapM snd (snd <$> l)
          vnames :: [String]
          vnames = fst <$> l
      lcupt <- slcupt
      x' <- x
      pure $ (i, upt2iexpr $ LetUP lupt upt0) :< LetUPF (vnames `zip` lcupt) x'
    CaseUPF (upt0, x) l -> do
      i <- State.get
      State.modify (+ 1)
      x' <- x
      let aux :: [ ( Pattern
                   , UnprocessedParsedTerm
                   )
                 ]
          aux = (fmap . fmap) fst l
          aux0 = (fmap . fmap) snd l
          aux1 :: State Int
                    [ ( Pattern
                      , Cofree UnprocessedParsedTermF (Int, Either String IExpr)
                      )
                    ]
          aux1 = mapM sequence aux0
      aux1' <- aux1
      pure $ (i, upt2iexpr $ CaseUP upt0 aux) :< CaseUPF x' aux1'
    LamUPF s (upt0, x) -> do
      i <- State.get
      State.modify (+ 1)
      x' <- x
      pure $ (i, upt2iexpr $ LamUP s upt0) :< LamUPF s x'
    AppUPF (upt1, x) (upt2, y) -> do
      i <- State.get
      State.modify (+ 1)
      x' <- x
      y' <- y
      pure $ (i, upt2iexpr $ AppUP upt1 upt2) :< AppUPF x' y'
    UnsizedRecursionUPF (upt1, x) (upt2, y) (upt3, z) -> do
      i <- State.get
      State.modify (+ 1)
      x' <- x
      y' <- y
      z' <- z
      pure $ (i, upt2iexpr $
                   UnsizedRecursionUP upt1 upt2 upt3) :<
                     UnsizedRecursionUPF x' y' z'
    CheckUPF (upt1, x) (upt2, y) -> do
      i <- State.get
      State.modify (+ 1)
      x' <- x
      y' <- y
      pure $ (i, upt2iexpr $ CheckUP upt1 upt2) :< CheckUPF x' y'
    LeftUPF (upt0, x) -> do
      i <- State.get
      State.modify (+ 1)
      x' <- x
      pure $ (i, upt2iexpr $ LeftUP upt0) :< LeftUPF x'
    RightUPF (upt0, x) -> do
      i <- State.get
      State.modify (+ 1)
      x' <- x
      pure $ (i, upt2iexpr $ RightUP upt0) :< RightUPF x'
    TraceUPF (upt0, x) -> do
      i <- State.get
      State.modify (+ 1)
      x' <- x
      pure $ (i, upt2iexpr $ TraceUP upt0) :< TraceUPF x'
    HashUPF (upt0, x) -> do
      i <- State.get
      State.modify (+ 1)
      x' <- x
      pure $ (i, upt2iexpr $ LeftUP upt0) :< LeftUPF x'
    IntUPF i -> do
      x <- State.get
      State.modify (+ 1)
      pure ((x, upt2iexpr $ IntUP i) :< IntUPF i)
    VarUPF s -> do
      x <- State.get
      State.modify (+ 1)
      pure ((x, upt2iexpr $ VarUP s) :< VarUPF s)
    PairUPF (upt1, x) (upt2, y) -> do
      i <- State.get
      State.modify (+ 1)
      x' <- x
      y' <- y
      pure $ (i, upt2iexpr $ PairUP upt1 upt2) :< PairUPF x' y'

