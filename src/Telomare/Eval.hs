{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-deferred-out-of-scope-variables #-}
{-# LANGUAGE TupleSections       #-}

module Telomare.Eval where

import Control.Comonad.Cofree (Cofree ((:<)), hoistCofree)
import Control.Lens.Plated (Plated (..), transformM)
import Control.Monad (void)
import Control.Monad.State (State, evalState)
import qualified Control.Monad.State as State
import Data.Bifunctor (first, second)
import Data.Foldable (fold)
import Data.List (partition)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Semigroup (Max (..), Min (..))
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace
import System.IO
import System.Process

import qualified Control.Comonad.Trans.Cofree as CofreeT
import Data.Functor.Foldable (Base, cata, embed, para)
import PrettyPrint
import Telomare (AbstractRunTime, BreakState, BreakState', ExprA (..),
                 FragExpr (..), FragExprF (..), FragIndex (FragIndex),
                 IExpr (..), IExprF (..), LocTag (..), PartialType (..),
                 Pattern, RecursionPieceFrag, RecursionSimulationPieces (..),
                 RunTimeError (..), TelomareLike (..), Term3 (Term3),
                 Term4 (Term4), UnprocessedParsedTerm (..),
                 UnprocessedParsedTermF (..), UnsizedRecursionToken (..), app,
                 appF, cataFragExprUR, convertAbortMessage, deferF, eval,
                 forget, g2s, innerChurchF, insertAndGetKey, pairF, rootFrag,
                 s2g, setEnvF, tag, unFragExprUR)
import Telomare.Parser (AnnotatedUPT, parseModule, parseOneExprOrTopLevelDefs,
                        parsePrelude)
import Telomare.Possible (abortExprToTerm4, abortPossibilities, appB,
                          buildUnsizedLocMap, deferB, evalA, getSizesM,
                          sizeTermM, term3ToUnsizedExpr, term4toAbortExpr)
import Telomare.PossibleData (AbortExpr, CompiledExpr (..), SizedRecursion (..),
                              VoidF, envB, leftB, pairB, pattern AbortFW,
                              rightB, setEnvB)
import Telomare.Resolver (main2Term3, process, resolveAllImports)
import Telomare.RunTime (rEval)
import Telomare.TypeChecker (TypeCheckError (..), typeCheck)
import Text.Megaparsec (errorBundlePretty, runParser)

debug :: Bool
debug = False

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

data EvalError = RTE RunTimeError
    | TCE TypeCheckError
    | StaticCheckError String
    | CompileConversionError
    | RecursionLimitError UnsizedRecursionToken
    deriving (Eq, Ord, Show)

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

-- rather than remove checks, we should extract them so that they can be run separately, if that gives a performance benefit
{-
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
-}
removeChecks :: Term4 -> Term4
removeChecks = id

runStaticChecks :: Term4 -> Either EvalError Term4
runStaticChecks t@(Term4 termMap) =
  let result = evalA scTerm
      scTerm = term4toAbortExpr t
  in case debugTrace ("running static checks for:\n" <> prettyPrint t) result of
    Nothing -> pure t
    Just e  -> Left . StaticCheckError $ convertAbortMessage e

compileMain :: Term3 -> Either EvalError CompiledExpr
compileMain term = case typeCheck (PairTypeP (ArrTypeP ZeroTypeP ZeroTypeP) AnyType) term of
  Just e -> Left $ TCE e
  _      -> compile pure term -- TODO add runStaticChecks back in

-- for testing
compileMain' :: Term3 -> Either EvalError CompiledExpr
compileMain' = compile pure

compileUnitTest :: Term3 -> Either EvalError CompiledExpr
compileUnitTest = compile runStaticChecks

-- TODO kind of a hack, really CompiledExpr should be the basis for TelomareLike
compileUnitTestNoAbort :: Term3 -> Either EvalError CompiledExpr
compileUnitTestNoAbort = fmap (cata f) . compileUnitTest where
  f = \case
    AbortFW _ -> deferB (toEnum (-9)) envB
    x -> embed x

compile :: (Term4 -> Either EvalError Term4) -> Term3 -> Either EvalError CompiledExpr
compile staticCheck t = debugTrace ("compiling term3:\n" <> prettyPrint t)
  $ term4toAbortExpr . removeChecks <$> (findChurchSize t >>= staticCheck)

-- converts between easily understood Haskell types and untyped IExprs around an iteration of a Telomare expression
funWrap :: forall a. (Show a, AbstractRunTime a) => a -> (a -> a -> a) -> Maybe (String, IExpr) -> (String, Either RunTimeError a)
funWrap fun app inp =
  let iexpInp = case inp of
        Nothing                  -> Zero
        Just (userInp, oldState) -> Pair (s2g userInp) oldState
  in case eval (app fun $ fromTelomare iexpInp) of
    Right x -> case toTelomare x of
      Nothing -> ("error converting iteration value:\n" <> show x, Left $ AbortRunTime Zero)
      Just Zero -> ("aborted", Left $ AbortRunTime Zero)
      Just (Pair disp newState) -> (g2s disp, pure $ fromTelomare newState)
      Just z -> ("unexpected runtime value, dumped:\n" <> show z, Left $ GenericRunTimeError "unexpected runtime value" z)
    Left e -> ("runtime error:\n" <> show e, Left e)

runMainCore :: [(String, String)] -- ^All modules as (Module_Name, Module_Content)
            -> String -- ^Module's name with `main` function
            -> (CompiledExpr -> IO a)
            -> IO a
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
      Right (Left z) -> error $ "compilation failed somehow, with result:\n" <> show z

runMain_ :: [(String, String)] -- ^All modules as (Module_Name, Module_Content)
         -> String -- ^Module's name with `main` function
         -> IO String
runMain_ modulesStrings s = runMainCore modulesStrings s evalLoop_

runMain :: [(String, String)] -- ^All modules as (Module_Name, Module_Content)
        -> String -- ^Module's name with `main` function
        -> IO ()
runMain modulesStrings s = runMainCore modulesStrings s evalLoop

runMainWithInput :: [String] -- ^Inputs
                 -> [(String, String)] -- ^All modules as (Module_Name, Module_Content)
                 -> String -- ^Module's name with `main` function
                 -> IO String
runMainWithInput inputList modulesStrings s = runMainCore modulesStrings s (evalLoopWithInput inputList)

schemeEval :: IExpr -> IO ()
schemeEval iexpr = do
  writeFile "scheme.txt" ('(' : (show (app iexpr Zero) <> ")"))
  (_, Just mhout, _, _) <- createProcess (shell "chez-script runtime.so") { std_out = CreatePipe }
  scheme <- hGetContents mhout
  putStrLn scheme

evalLoopCore :: CompiledExpr
             -> (String -> String -> IO String)
             -> String
             -> [String]
             -> IO String
evalLoopCore expr accumFn initAcc manualInput =
  let wrappedEval :: Maybe (String, IExpr) -> (String, Either RunTimeError CompiledExpr)
      wrappedEval = funWrap expr appB
      mainLoop acc strInput s = do
        let (out, nextState) = wrappedEval s
        newAcc <- accumFn acc out
        case toTelomare <$> nextState of
          Left _ -> pure acc
          Right Nothing -> pure $ newAcc <> "\ndone"
          Right (Just Zero) -> pure $ newAcc <> "\n" <> "done"
          Right (Just ns) -> do
            (inp, rest) <-
              if null strInput
              then (, []) <$> getLine
              else pure (head strInput, tail strInput)
            mainLoop newAcc rest $ pure (inp, fromTelomare ns)
  in mainLoop initAcc manualInput Nothing

evalLoop :: CompiledExpr -> IO ()
evalLoop iexpr = void $ evalLoopCore iexpr printAcc "" []
  where
    printAcc _ out = do
      putStrLn out
      pure ""

evalLoopWithInput :: [String] -> CompiledExpr -> IO String
evalLoopWithInput inputList iexpr = evalLoopCore iexpr printAcc "" inputList
  where
    printAcc acc out = if acc == ""
                       then pure out
                       else pure (acc <> "\n" <> out)

-- |Same as `evalLoop`, but keeping what was displayed.
evalLoop_ :: CompiledExpr -> IO String
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
        parsed = parsePrelude prelude >>= (`parseMain` s)
        unsizedExpr = term3ToUnsizedExpr 256 <$> parsed
        sizedRecursion = unsizedExpr >>= (first (("Could not size token: " <>) . show) . getSizesM 256)
        sizeLocs = Map.toAscList . buildUnsizedLocMap <$> unsizedExpr
        -- (orphanLocs, lineLocs) = partition ((== DummyLoc) . snd) sizeLocs
        (orphanLocs, lineLocs) = case sizeLocs of
          Left e   -> error ("Could not size: " <> show e)
          Right sl -> partition ((== DummyLoc) . snd) sl
        -- orphanList = map ((<> " ") . show . fst) orphanLocs
        orphans = "unsized with no location: " <> foldMap ((<> " ") . show . fst) orphanLocs
        fromEnum' = \case
          Loc x _ -> x
          _ -> error "unexpected DummyLoc"
        lookupSize x = case sizedRecursion of
          Right (SizedRecursion sm) -> case Map.lookup x sm of
            Just (Just v) -> show v
            _             -> "?"
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
        funMap = case parsePrelude prelude >>= (`parseMain` s) of
          Right (Term3 f) -> f
          e               -> error ("could not parse " <> show e)
        unAss (a :< _) = a
        -- sizeLocs = (\(fi, t) -> (fi))
        reduceL (a CofreeT.:< x) = let l = fromEnum' a in (Min l, Max l) <> fold x
        bodyLocs = second (cataFragExprUR reduceL) <$> Map.toAscList funMap
        sizeLocs = second (unAss . unFragExprUR) <$> Map.toAscList funMap
        (orphanLocs, lineLocs) = partition ((== DummyLoc) . snd) sizeLocs
        orphans = "functions with no location: " <> foldMap ((<> " ") . show . fst) orphanLocs
        fromEnum' = \case
          Loc x _ -> x
          _ -> 0 -- error "unexpected DummyLoc"
        getFunMatchingLine x = case filter ((== x) . fromEnum' . snd) lineLocs of
          [] -> ""
          -- l -> ("   # " <>) $ foldMap ((\s -> show (fromEnum s) <> ":" <> lookupSize s <> " ") . fst) l
          l  -> ("   # " <>) $ foldMap ((<> " ") . show . fromEnum . fst) l
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
  = let parsed = parsePrelude prelude >>= (`parseMain` s)
        unsizedExpr = term3ToUnsizedExpr 256 <$> parsed
    in case unsizedExpr of
         Left e   -> error $ "getAbortPossibilities: " <> show e
         Right ue -> abortPossibilities 256 ue

getAbortPossibilities' :: String -> String -> Set String
getAbortPossibilities' prelude s
  = let parsed = parsePrelude prelude >>= (`parseMain` s)
        unsizedExpr = term3ToUnsizedExpr 256 <$> parsed
    in case unsizedExpr of
         Left e   -> error $ "getAbortPossibilities: " <> show e
         Right ue -> Set.map convertAbortMessage $ abortPossibilities 256 ue

eval2IExpr :: [(String, [Either AnnotatedUPT (String, AnnotatedUPT)])] -> String -> Either String IExpr
eval2IExpr extraModuleBindings str =
  first errorBundlePretty (runParser (parseOneExprOrTopLevelDefs resolved) "" str)
  >>= process
  >>= tt . first show . compileUnitTest
    where
      tt = \case
        Left e -> Left e
        Right x -> case toTelomare x of
          Just ie -> pure ie
          _ -> Left $ "eval2IExpr conversion error back to iexpr:\n" <> prettyPrint x
      aux = (\str -> Left (DummyLoc :< ImportUPF str)) . fst <$> extraModuleBindings
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
  upt2iexpr u = process (tag DummyLoc u) >>= tt . first show . compileUnitTest
  tt = \case
    Left e -> Left e
    Right x -> case toTelomare x of
      Just ie -> pure ie
      _ -> Left $ "tagUPTwithExpr conversion error back to iexpr:\n" <> prettyPrint x
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

