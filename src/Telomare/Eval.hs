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
import Telomare (AbstractRunTime, EvalError (..),
                 LocTag (..),
                 PartialType (..), Pattern,
                 ResolverError (..),
                 RunTimeError (..), TelomareLike (..), Term2,
                 UnprocessedParsedTerm (..),
                 UnprocessedParsedTermF (..), UnsizedRecursionToken (..),
                 deferS, abortEE,
                 convertAbortMessage, eval, forget, embedB, basicEE, stuckEE, pairB, zeroB, rightB, leftB, embedS, setEnvB, envB, b2s, s2b,
                 insertAndGetKey, appS, pattern ZeroB, pattern PairB,
                 tag, Term3, CompiledExpr, StuckF (..), pattern StuckFW, Term3F (..), pattern AbortFW, StuckExpr, BasicExpr, CompiledExprF,
                 PartExprF (..), pattern BasicEE, pattern StuckEE, convertBasic, convertStuck, convertAbort,
                 pattern BasicFW, pattern StuckFW, Term3Builder, AbortableF (AbortF))
import Telomare.Parser (AnnotatedUPT, parseModule, parseOneExprOrTopLevelDefs,
                        parsePrelude)
import Telomare.Possible (SizingSettings (SizingSettings),
                          appB, deferB, evalStaticCheck, basicEval,
                          getSizesM, sizeTermM, term3ToUnsizedExpr,
                          )
import Telomare.PossibleData (SizedRecursion (..),
                              VoidF,
                              )
import Telomare.Resolver (main2Term3, main2Term3let, process, resolveAllImports)
import Telomare.TypeChecker (typeCheck)
import Text.Megaparsec (errorBundlePretty, runParser)
import Control.Lens (Identity(runIdentity))

debug :: Bool
debug = False

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

-- note that function indexes may be changed in this process
convertPT :: (UnsizedRecursionToken -> Int) -> Term3 -> CompiledExpr
{-
convertPT ll term =
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
-}
convertPT ll = forget . flip State.evalState (toEnum 0, toEnum 0) . cata (f (convertBasic (convertAbort failConvert))) where
  failConvert = error "convertPT failed"
  appTC :: Term3Builder (Cofree CompiledExprF LocTag)
  appTC = appS (pure $ leftB envB) (pure $ rightB envB)
  f convertOther (_ CofreeT.:< g)= case g of
    StuckFW (DeferSF _ x) -> x >>= deferS
    Term3Unsized urt -> pure $ iterate setEnvB envB !! ll urt
    Term3CheckingWrapper _ tc c ->
      let performTC = (>>= deferS) ((\ia -> setEnvB (pairB (setEnvB (pairB (abortEE AbortF) ia))
                                                     (rightB envB))) <$> appTC)
      in (\tc' c' ptc -> setEnvB (pairB ptc (pairB  tc' c'))) <$> tc <*> c <*> performTC
    x -> convertOther x

data SizingOption
  = NoSizing -- deprecated
  | UnitTestSizing
  | MainSizing
  | DebugSizing SizingSettings

findChurchSizeD :: SizingOption -> Term3 -> Either EvalError CompiledExpr
findChurchSizeD so t3 = let reallyBigNum = 65536 in case so of
  NoSizing       -> pure (convertPT (const reallyBigNum) t3)
  UnitTestSizing       -> pure (convertPT (const reallyBigNum) t3) -- TODO remove, just here to validate convertPT
  -- UnitTestSizing -> calculateRecursionLimits (SizingSettings reallyBigNum False) t3
  MainSizing     -> calculateRecursionLimits (SizingSettings reallyBigNum True) t3
  DebugSizing ss -> calculateRecursionLimits ss t3

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
removeChecks :: CompiledExpr -> CompiledExpr
removeChecks = id

runStaticChecks :: CompiledExpr -> Either EvalError CompiledExpr
runStaticChecks t =
  let result = evalStaticCheck False scTerm
      scTerm = runIdentity $ cata (convertBasic (convertStuck (convertAbort (\_ -> error "error converting for runStaticChecks")))) t
  in case debugTrace ("running static checks for:\n" <> prettyPrint t) result of
    Nothing -> pure t
    Just e  -> Left . StaticCheckError $ convertAbortMessage e

compileMain :: [(String, [Either AnnotatedUPT (String, AnnotatedUPT)])] -> String -> Either EvalError CompiledExpr
compileMain modules term = do
  tcTerm <- first RE $ main2Term3 modules term
  case typeCheck (PairTypeP (ArrTypeP ZeroTypeP ZeroTypeP) AnyType) tcTerm of
    Just e -> Left $ TCE e
    _      -> first RE (main2Term3let modules term) >>= compile MainSizing pure

-- for testing
compileMain' :: SizingSettings -> Term3 -> Either EvalError CompiledExpr
compileMain' ss = compile (DebugSizing ss) pure

compileUnitTest :: Term3 -> Either EvalError CompiledExpr
compileUnitTest = compile UnitTestSizing runStaticChecks

-- TODO kind of a hack, really CompiledExpr should be the basis for TelomareLike
compileUnitTestNoAbort :: Term3 -> Either EvalError CompiledExpr
compileUnitTestNoAbort = fmap (cata f) . compileUnitTest where
  f = \case
    AbortFW _ -> deferB (toEnum (-9)) envB
    x -> embed x

compile :: SizingOption -> (CompiledExpr -> Either EvalError CompiledExpr) -> Term3 -> Either EvalError CompiledExpr
compile so staticCheck t = debugTrace ("compiling term3:\n" <> prettyPrint t)
  $ removeChecks <$> (findChurchSizeD so t >>= staticCheck)

-- converts between easily understood Haskell types and untyped IExprs around an iteration of a Telomare expression
funWrap :: forall a. (Show a, AbstractRunTime a) => a -> (a -> a -> a) -> Maybe (String, BasicExpr) -> (String, Either RunTimeError BasicExpr)
funWrap fun app inp =
  let iexpInp = conv $ case inp of
        Nothing                  -> zeroB
        Just (userInp, oldState) -> pairB (s2b userInp) oldState
      conv = runIdentity . cata (convertBasic (\_ -> error "funWrap conversion error"))
      conv2 = runIdentity . cata (convertBasic (convertStuck ((\_ -> error "funWrap conversion error2"))))
      conv3 = runIdentity . cata (convertBasic (\_ -> error "funWrap conversion error3"))
  in case eval (app fun $ fromTelomare iexpInp) of
    Right x -> case toTelomare x of
      Nothing -> ("error converting iteration value:\n" <> show x, Left $ AbortRunTime zeroB)
      Just ZeroB -> ("aborted", Left $ AbortRunTime zeroB)
      -- Just (PairB disp newState) -> (b2s disp, pure $ fromTelomare newState)
      Just (PairB disp newState) -> case b2s disp of
        Just d -> (d, pure $ conv3 newState)
        _ -> ("error converting display value:\n" <> prettyPrint disp, Left . GenericRunTimeError "" $ conv2 disp)
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
    case compileMain modules s of
      Left e  -> error $ "runMainCore failed: " <> show e
      Right g -> e g

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

{- TODO fix
schemeEval :: CompiledExpr -> IO ()
schemeEval iexpr = do
  writeFile "scheme.txt" ('(' : (show (app iexpr Zero) <> ")"))
  (_, Just mhout, _, _) <- createProcess (shell "chez-script runtime.so") { std_out = CreatePipe }
  scheme <- hGetContents mhout
  putStrLn scheme
-}

evalLoopCore :: CompiledExpr
             -> (String -> String -> IO String)
             -> String
             -> [String]
             -> IO String
evalLoopCore expr accumFn initAcc manualInput =
  {-
  let wrappedEval :: Maybe (String, BasicExpr) -> (String, Either RunTimeError CompiledExpr)
      wrappedEval = funWrap expr appB
-}
  let wrappedEval = funWrap expr appB
      mainLoop acc strInput s = do
        let (out, nextState) = wrappedEval s
        newAcc <- accumFn acc out
        -- case toTelomare <$> nextState of
        case nextState of
          Left e -> pure $ newAcc <> "\n" <> show e
  {-
          Right Nothing -> pure $ newAcc <> "\ndone"
          Right (Just ZeroB) -> pure $ newAcc <> "\n" <> "done"
          Right (Just ns) -> do
-}
          Right ZeroB -> pure $ newAcc <> "\n" <> "done"
          Right ns -> do

            (inp, rest) <-
              if null strInput
              then (, []) <$> getLine
              else pure (head strInput, tail strInput)
            mainLoop newAcc rest $ pure (inp, ns)
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

calculateRecursionLimits :: SizingSettings -> Term3 -> Either EvalError CompiledExpr
calculateRecursionLimits sizingSettings t3 = case sizeTermM sizingSettings $ term3ToUnsizedExpr t3 of
    Left urt -> Left $ RecursionLimitError urt
    Right t  -> pure t
  {-
    Right t  -> case t of
      Left a  -> Left . StaticCheckError . convertAbortMessage $ a
      Right t -> pure t
-}

-- takes a main function and sizes the unsized recursion and then displays the results as comments in the original source
showSizingInSource :: String -> String -> String
showSizingInSource prelude s
  = let asLines = zip [0..] $ lines s
        parsed = first ParseError (parsePrelude prelude) >>= (`parseMain` s)
        unsizedExpr = term3ToUnsizedExpr <$> first RE parsed
        sizedRecursion = unsizedExpr >>= (first RecursionLimitError . getSizesM 256)
        sizeLocs = error "TODO showSizingInSource implement sizeLocs" --Map.toAscList . buildUnsizedLocMap <$> unsizedExpr
        -- (orphanLocs, lineLocs) = partition ((== DummyLoc) . snd) sizeLocs
        (orphanLocs, lineLocs) = case sizeLocs of
          Left e   -> error "uh" -- ("Could not size: " <> show e)
          Right sl -> partition ((== DummyLoc) . snd) sl
        -- orphanList = map ((<> " ") . show . fst) orphanLocs
        -- orphans = "unsized with no location: " <> foldMap ((<> " ") . show . fst) orphanLocs
        orphans = error "TODO showSizingInSource thing"
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

{-
showFunctionIndexesInSource :: String -> String -> String
showFunctionIndexesInSource prelude s
  = let asLines = zip [1..] $ lines s
        -- parsed = parsePrelude prelude >>= (\p -> parseMain p s)
        funMap = case first ParseError (parsePrelude prelude) >>= (`parseMain` s) of
          Right (Term3 f) -> f
          e               -> error ("could not parse " <> show e)
        unAss (a :< _) = a
        -- sizeLocs = (\(fi, t) -> (fi))
        reduceL (a CofreeT.:< x) = let l = fromEnum' a in (Min l, Max l) <> fold x
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
-}

parseMain :: [(String, AnnotatedUPT)] -- ^Prelude: [(VariableName, BindedUPT)]
          -> String                            -- ^Raw string to be parserd.
          -> Either ResolverError Term3               -- ^Error on Left.
parseMain prelude' str =
  let prelude :: [(String, [Either AnnotatedUPT (String, AnnotatedUPT)])]
      prelude = [("Prelude", Right <$> prelude')]
      parseAuxModule :: String -> (String, [Either AnnotatedUPT (String, AnnotatedUPT)])
      parseAuxModule str =
        case sequence ("AuxModule", parseModule ("import Prelude\n" <> str)) of
          Left e    -> error $ show e
          Right pam -> pam
  in main2Term3 (parseAuxModule str:prelude) "AuxModule"

{-
getAbortPossibilities :: String -> String -> Set BasicExpr
getAbortPossibilities prelude s
  = let parsed = first ParseError (parsePrelude prelude) >>= (`parseMain` s)
        unsizedExpr = term3ToUnsizedExpr <$> parsed
    in case unsizedExpr of
         Left e   -> error $ "getAbortPossibilities: " <> show e
         Right ue -> abortPossibilities 256 ue

getAbortPossibilities' :: String -> String -> Set String
getAbortPossibilities' prelude s
  = let parsed = first ParseError (parsePrelude prelude) >>= (`parseMain` s)
        unsizedExpr = term3ToUnsizedExpr <$> parsed
    in case unsizedExpr of
         Left e   -> error $ "getAbortPossibilities: " <> show e
         Right ue -> Set.map convertAbortMessage $ abortPossibilities 256 ue
-}

eval2IExpr :: [(String, [Either AnnotatedUPT (String, AnnotatedUPT)])] -> String -> Either String CompiledExpr
eval2IExpr extraModuleBindings str =
  first errorBundlePretty (runParser (parseOneExprOrTopLevelDefs resolved) "" str)
  >>= first show . process
  >>= tt . first show . compileUnitTest
    where
      tt = \case
        Left e -> Left $ show e
        Right x -> pure x
  {-
        Right x -> case toTelomare x of
          Just ie -> pure ie
          _ -> Left $ "eval2IExpr conversion error back to iexpr:\n" <> prettyPrint x
-}
      aux = (\str -> Left (DummyLoc :< ImportQualifiedUPF str str)) . fst <$> extraModuleBindings
      resolved = resolveAllImports extraModuleBindings aux

tagIExprWithEval :: CompiledExpr -> Cofree CompiledExprF (Int, CompiledExpr)
tagIExprWithEval iexpr = evalState (para alg iexpr) 0 where
  statePlus1 :: State Int Int
  statePlus1 = do
      i <- State.get
      State.modify (+ 1)
      pure i
  alg :: Base CompiledExpr
              ( CompiledExpr
              , State Int (Cofree CompiledExprF (Int, CompiledExpr))
              )
      -> State Int (Cofree CompiledExprF (Int, CompiledExpr))
  alg = \case
    BasicFW ZeroSF -> do
      i <- statePlus1
      -- pure ((i, rEval Zero Zero) :< ZeroF)
      pure ((i, basicEval zeroB) :< embedB ZeroSF)
    BasicFW EnvSF -> do
      i <- statePlus1
      -- pure ((i, rEval Zero Env) :< EnvF)
      pure ((i, basicEval zeroB) :< embedB EnvSF)
    BasicFW (SetEnvSF (iexpr0, x)) -> do
      i <- statePlus1
      x' <- x
      -- pure $ (i, rEval Zero $ SetEnv iexpr0) :< SetEnvF x'
      pure $ (i, basicEval $ setEnvB iexpr0) :< embedB (SetEnvSF x')
    StuckFW (DeferSF ind (iexpr0, x)) -> do
      i <- statePlus1
      x' <- x
      -- pure $ (i, rEval Zero $ Defer iexpr0) :< DeferF x'
      pure $ (i, basicEval . stuckEE $ DeferSF (toEnum (-1)) iexpr0) :< embedS (DeferSF (toEnum (-1)) x')
    BasicFW (LeftSF (iexpr0, x)) -> do
      i <- statePlus1
      x' <- x
      -- pure $ (i, rEval Zero $ PLeft iexpr0) :< PLeftF x'
      pure $ (i, basicEval $ leftB iexpr0) :< embedB (LeftSF x')
    BasicFW (RightSF (iexpr0, x)) -> do
      i <- statePlus1
      x' <- x
      -- pure $ (i, rEval Zero $ PRight iexpr0) :< PRightF x'
      pure $ (i, basicEval $ rightB iexpr0) :< embedB (RightSF x')
    BasicFW (PairSF (iexpr0, x) (iexpr1, y)) -> do
      i <- statePlus1
      x' <- x
      y' <- y
      -- pure $ (i, rEval Zero $ Pair iexpr0 iexpr1) :< PairF x' y'
      pure $ (i, basicEval $ pairB iexpr0 iexpr1) :< embedB (PairSF x' y')
    BasicFW (GateSF (iexpr0, x) (iexpr1, y)) -> do
      i <- statePlus1
      x' <- x
      y' <- y
      -- pure $ (i, rEval Zero $ Gate iexpr0 iexpr1) :< GateF x' y'
      pure $ (i, basicEval . basicEE $ GateSF iexpr0 iexpr1) :< embedB (GateSF x' y')

tagUPTwithIExpr :: [(String, AnnotatedUPT)]
                -> UnprocessedParsedTerm
                -> Cofree UnprocessedParsedTermF (Int, Either String CompiledExpr)
tagUPTwithIExpr prelude upt = evalState (para alg upt) 0 where
  upt2iexpr :: UnprocessedParsedTerm -> Either String CompiledExpr
  upt2iexpr u = first show (process (tag DummyLoc u)) >>= tt . first show . compileUnitTest
  tt = \case
    Left e -> Left e
    Right x -> pure x
  {-
    Right x -> case toTelomare x of
      Just ie -> pure ie
      _ -> Left $ "tagUPTwithExpr conversion error back to iexpr:\n" <> prettyPrint x
-}
  alg :: Base UnprocessedParsedTerm
              ( UnprocessedParsedTerm
              , State Int (Cofree UnprocessedParsedTermF (Int, Either String CompiledExpr))
              )
      -> State Int (Cofree UnprocessedParsedTermF (Int, Either String CompiledExpr))
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
      let scupt :: State Int [Cofree UnprocessedParsedTermF (Int, Either String CompiledExpr)]
          scupt = mapM snd l
      cupt <- scupt
      pure $ (i, upt2iexpr . ListUP $ fst <$> l) :< ListUPF cupt
    LetUPF l (upt0, x) -> do
      i <- State.get
      State.modify (+ 1)
      let lupt :: [(String, UnprocessedParsedTerm)]
          lupt = (fmap . fmap) fst l
          slcupt :: State Int
                     [Cofree UnprocessedParsedTermF (Int, Either String CompiledExpr)]
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
                      , Cofree UnprocessedParsedTermF (Int, Either String CompiledExpr)
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

