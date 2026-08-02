{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-deferred-out-of-scope-variables #-}
{-# LANGUAGE TupleSections       #-}

module Telomare.Eval where

import Control.Comonad.Cofree (Cofree ((:<)), hoistCofree)
import Control.Lens.Plated (Plated (..), transformM)
import Control.Monad (void)
import Control.Monad.State (State, evalState)
import qualified Control.Monad.State as State
import Data.Bifunctor (bimap, first, second)
import Data.Foldable (fold)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Semigroup (Max (..), Min (..))
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace

import qualified Control.Comonad.Trans.Cofree as CofreeT
import Control.Lens (Identity (runIdentity))
import Data.Functor.Foldable (Base, cata, embed, para)
import Telomare.PrettyPrint
import Telomare.Error
import Telomare.IR.Base
import Telomare.IR.Builder
import Telomare.IR.Core
import Telomare.IR.Loc
import Telomare.IR.Surface
import Telomare.IR.Types
import Telomare.Meter (Meter, evalMeter)
import Telomare.Parse (parseModule, parseModuleNamed,
                        parseOneExprOrTopLevelDefs, parsePrelude)
import Telomare.Possible (SizingSettings (..), appB, basicEval, deferB,
                          evalStaticCheck, sizeTermM, term3ToUnsizedExpr)
import Telomare.PossibleData (SizedRecursion (..), VoidF)
import Telomare.Resolver (main2Term3, main2Term3let, process, resolveAllImports)
import Telomare.TypeChecker (typeCheck)
import Text.Megaparsec (errorBundlePretty, runParser)

debug :: Bool
debug = False

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

-- note that function indexes may be changed in this process
convertPT :: (UnsizedRecursionToken -> Int) -> Term3 -> CompiledExpr
convertPT ll = forget . flip State.evalState (toEnum 0, toEnum 0) . cata (f (convertBasic (convertAbort failConvert))) where
  failConvert = error "convertPT failed"
  appTC :: Term3Builder (Cofree CompiledExprF LocTag)
  appTC = appS (pure $ LeftB EnvB) (pure $ RightB EnvB)
  f convertOther (_ CofreeT.:< g)= case g of
    StuckFW (DeferSF _ x) -> x >>= deferS
    Term3Unsized urt -> pure $ iterate SetEnvB EnvB !! ll urt
    Term3CheckingWrapper _ tc c ->
      let performTC = (>>= deferS) ((\ia -> SetEnvB (PairB (SetEnvB (PairB (AbortEE AbortF) ia))
                                                     (RightB EnvB))) <$> appTC)
      in (\tc' c' ptc -> SetEnvB (PairB ptc (PairB  tc' c'))) <$> tc <*> c <*> performTC
    x -> convertOther x

data SizingOption
  = NoSizing -- deprecated
  | UnitTestSizing
  | MainSizing
  | DebugSizing SizingSettings

-- |What the sizing pass learned, kept rather than discarded. These iteration
-- counts are the numbers the compiler already relies on to claim a program is
-- total; reporting them asserts nothing new.
data SizingReport = SizingReport
  { sizingReportCounts :: SizedRecursion
  -- ^Per recursion site, the iteration count inferred over every input.
  , sizingReportLocs   :: Map UnsizedRecursionToken LocTag
  -- ^Where each site is in the source.
  , sizingReportBudget :: Int
  -- ^The unrolling budget the search was allowed.
  }

-- |Every recursion site's source location, recovered from the `Term3`
-- annotations that `term3ToUnsizedExpr` drops on its way to `UnsizedExpr`.
buildUnsizedLocMap :: Term3 -> Map UnsizedRecursionToken LocTag
buildUnsizedLocMap = cata f where
  f (anno CofreeT.:< g) = case g of
    Term3Unsized tok -> Map.singleton tok anno
    x                -> fold x

-- |`sizeTermM` names the recursion that failed but cannot say where it is.
locateSizingFailure :: Map UnsizedRecursionToken LocTag -> SizingFailure -> SizingFailure
locateSizingFailure locs failure =
  failure { sizingFailureLoc = Map.lookup (sizingFailureToken failure) locs }

sizingBudget :: SizingOption -> Int
sizingBudget = \case
  NoSizing       -> reallyBigNum
  UnitTestSizing -> reallyBigNum
  MainSizing     -> reallyBigNum
  DebugSizing ss -> maxSizingSize ss

reallyBigNum :: Int
reallyBigNum = 65536

findChurchSizeD :: SizingOption -> Term3 -> Either EvalError CompiledExpr
findChurchSizeD so = fmap snd . findChurchSizeReporting so

findChurchSizeReporting :: SizingOption -> Term3 -> Either EvalError (SizingReport, CompiledExpr)
findChurchSizeReporting so t3 = case so of
  NoSizing       -> pure (report mempty, convertPT (const reallyBigNum) t3)
  UnitTestSizing -> sized (SizingSettings reallyBigNum False)
  MainSizing     -> sized (SizingSettings reallyBigNum True)
  DebugSizing ss -> sized ss
  where
    locs = buildUnsizedLocMap t3
    report counts = SizingReport counts locs (sizingBudget so)
    sized settings = case sizeTermM settings $ term3ToUnsizedExpr t3 of
      Left failure      -> Left . RecursionLimitError $ locateSizingFailure locs failure
      Right (counts, t) -> pure (report counts, t)

-- rather than remove checks, we should extract them so that they can be run separately, if that gives a performance benefit
{-
removeChecks :: Term4 -> Term4
removeChecks (Term4 m) =
  let f = \case
        anno :< AbortFragF -> anno :< DeferFragF ind
        x                  -> x
      (ind, newM) = State.runState builder m
      builder = do
        envDefer <- insertAndGetKey $ GeneratedLoc "removeChecks" Nothing :< EnvFragF
        insertAndGetKey $ GeneratedLoc "removeChecks" Nothing :< DeferFragF envDefer
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
compileMain modules term = snd <$> compileMainReporting MainSizing modules term

-- |`compileMain`, keeping the sizing results. Sizing costs minutes on
-- Prelude-heavy programs, so anything that wants to report the inferred
-- iteration counts must come by them through here rather than size again.
compileMainReporting :: SizingOption
                     -> [(String, [Either AnnotatedUPT (String, AnnotatedUPT)])]
                     -> String
                     -> Either EvalError (SizingReport, CompiledExpr)
compileMainReporting so modules term = do
  let modules' = second (fmap (bimap unAnnotatedUPT (second unAnnotatedUPT))) <$> modules
      mainType = embed $ PairTypeP (embed $ ArrTypeP (embed ZeroTypeP) (embed ZeroTypeP)) (embed AnyType)
  tcTerm <- first RE $ main2Term3 modules' term
  case typeCheck mainType tcTerm of
    Just e -> Left $ TCE e
    _      -> first RE (main2Term3let modules' term) >>= compileReporting so pure

-- for testing
compileMain' :: SizingSettings -> Term3 -> Either EvalError CompiledExpr
compileMain' ss = compile (DebugSizing ss) pure

compileUnitTest :: Term3 -> Either EvalError CompiledExpr
compileUnitTest = compile UnitTestSizing runStaticChecks

-- TODO kind of a hack, really CompiledExpr should be the basis for TelomareLike
compileUnitTestNoAbort :: Term3 -> Either EvalError CompiledExpr
compileUnitTestNoAbort = fmap (cata f) . compileUnitTest where
  f = \case
    AbortFW _ -> deferB (toEnum (-9)) EnvB
    x -> embed x

compile :: SizingOption -> (CompiledExpr -> Either EvalError CompiledExpr) -> Term3 -> Either EvalError CompiledExpr
compile so staticCheck t = snd <$> compileReporting so staticCheck t

compileReporting :: SizingOption
                 -> (CompiledExpr -> Either EvalError CompiledExpr)
                 -> Term3
                 -> Either EvalError (SizingReport, CompiledExpr)
compileReporting so staticCheck t = debugTrace ("compiling term3:\n" <> prettyPrint t) $ do
  (report, sized) <- findChurchSizeReporting so t
  checked <- staticCheck sized
  pure (report, removeChecks checked)

-- converts between easily understood Haskell types and untyped IExprs around an iteration of a Telomare expression
funWrap :: forall a. (Show a, AbstractRunTime a) => a -> (a -> a -> a) -> Maybe (String, BasicExpr) -> (String, Either RunTimeError BasicExpr)
funWrap fun app inp = snd $ funWrapWith (\x -> ((), eval x)) fun app inp

-- |`funWrap` over an evaluator that also reports something about the run, so
-- the metered and plain loops share one conversion path.
funWrapWith :: forall a m. (Show a, TelomareLike a, Monoid m)
            => (a -> (m, Either RunTimeError a))
            -> a -> (a -> a -> a) -> Maybe (String, BasicExpr)
            -> (m, (String, Either RunTimeError BasicExpr))
funWrapWith evaluator fun app inp =
  let iexpInp = conv $ case inp of
        Nothing                  -> ZeroB
        Just (userInp, oldState) -> PairB (s2b userInp) oldState
      conv = runIdentity . cata (convertBasic (\_ -> error "funWrap conversion error"))
      conv2 = runIdentity . cata (convertBasic (convertStuck (\_ -> error "funWrap conversion error2")))
      conv3 = runIdentity . cata (convertBasic (\_ -> error "funWrap conversion error3"))
      (measured, outcome) = evaluator (app fun $ fromTelomare iexpInp)
  in (,) measured $ case outcome of
    Right x -> case toTelomare x of
      Nothing -> ("error converting iteration value:\n" <> show x, Left $ AbortRunTime ZeroB)
      Just ZeroB -> ("aborted", Left $ AbortRunTime ZeroB)
      -- Just (PairB disp newState) -> (b2s disp, pure $ fromTelomare newState)
      Just (PairB disp newState) -> case b2s disp of
        Just d -> (d, pure $ conv3 newState)
        _ -> ("error converting display value:\n" <> prettyPrint disp, Left . GenericRunTimeError "" $ conv2 disp)
    Left e -> ("runtime error:\n" <> show e, Left e)

-- |Parse and compile a module set, keeping the sizing results. Every problem
-- comes back as text a user can act on rather than as an exception, so callers
-- decide how to report it.
--
-- Each module is parsed under its own name, so the locations in diagnostics
-- can say which file a term came from.
compileModules :: [(String, String)] -- ^All modules as (Module_Name, Module_Content)
               -> String -- ^Module's name with `main` function
               -> Either String (SizingReport, CompiledExpr)
compileModules = compileModulesWith MainSizing

-- |`compileModules` at a chosen sizing budget. Tests use a deliberately tiny
-- budget to reach the budget-exhaustion path without waiting for 65536
-- abstract unrollings.
compileModulesWith :: SizingOption
                   -> [(String, String)]
                   -> String
                   -> Either String (SizingReport, CompiledExpr)
compileModulesWith so modulesStrings s =
  case [ "Error in module " <> moduleName <> ":\n" <> err
       | (moduleName, Left err) <- parsed ] of
    [] -> first renderEvalError $ compileMainReporting so [ (n, m) | (n, Right m) <- parsed ] s
    errs -> Left $ unlines errs
  where
    parsed :: [(String, Either String [Either AnnotatedUPT (String, AnnotatedUPT)])]
    parsed = fmap (\(moduleName, content) -> (moduleName, parseModuleNamed moduleName content)) modulesStrings

runMainCore :: [(String, String)] -- ^All modules as (Module_Name, Module_Content)
            -> String -- ^Module's name with `main` function
            -> (CompiledExpr -> IO a)
            -> IO a
runMainCore modulesStrings s e = case compileModules modulesStrings s of
  -- Still an exception, since callers depend on that; the CLI takes the
  -- `compileModules` route instead so a user never sees this framing.
  Left err         -> error $ "runMainCore failed: " <> err
  Right (_, sized) -> e sized

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

evalLoopCore :: CompiledExpr
             -> (String -> String -> IO String)
             -> String
             -> [String]
             -> IO String
evalLoopCore expr accumFn initAcc manualInput =
  let wrappedEval = funWrap expr appB
      mainLoop acc strInput s = do
        let (out, nextState) = wrappedEval s
        newAcc <- accumFn acc out
        case nextState of
          Left e -> pure $ newAcc <> "\n" <> show e
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

-- |`evalLoop`, measuring what the session costs. Prints exactly what
-- `evalLoop` prints; the caller decides what to do with the measurement.
evalLoopMetered :: [String] -> CompiledExpr -> IO Meter
evalLoopMetered manualInput expr = go mempty manualInput Nothing where
  wrappedEval = funWrapWith evalMeter expr appB
  go measured strInput s = do
    let (m, (out, nextState)) = wrappedEval s
        measured' = measured <> m
    putStrLn out
    case nextState of
      Left _      -> pure measured'
      Right ZeroB -> pure measured'
      Right ns    -> do
        (inp, rest) <-
          if null strInput
          then (, []) <$> getLine
          else pure (head strInput, tail strInput)
        go measured' rest $ pure (inp, ns)

-- |Same as `evalLoop`, but keeping what was displayed.
evalLoop_ :: CompiledExpr -> IO String
evalLoop_ iexpr = evalLoopCore iexpr printAcc "" []
  where
    printAcc acc out = if acc == ""
                       then pure out
                       else pure (acc <> "\n" <> out)

calculateRecursionLimits :: SizingSettings -> Term3 -> Either EvalError CompiledExpr
calculateRecursionLimits sizingSettings = findChurchSizeD (DebugSizing sizingSettings)

-- |Every recursion site in the program, where it is, and how many times it can
-- iterate. The counts hold for every input: the sizing pass finds them by
-- running the program over a symbolic input, and takes the worst case across
-- the paths it explores.
--
-- Nothing here is a new claim. These are the very numbers the compiler bakes
-- into the program to make it total; a program that does not size does not
-- compile at all.
renderSizingCertificate :: SizingReport -> String
renderSizingCertificate report = unlines $
  "recursion sites (iterations, over every input):"
    : (if null sites then ["  none - this program has no unsized recursion"] else sites)
    <> ["", "sizing budget in force: " <> show (sizingReportBudget report) <> " unrollings"]
  where
    counts = Map.toAscList . unSizedRecursion $ sizingReportCounts report
    sites = fmap site counts
    site (tok, size) = "  " <> pad (place tok) <> "  <= " <> maybe "?" show size
    place tok =
      let named = "#" <> show (unUnsizedRecursionToken tok)
      in case Map.lookup tok (sizingReportLocs report) >>= renderLocTagCompact of
           Just spot -> spot <> " (" <> named <> ")"
           Nothing   -> named
    width = maximum (0 : fmap (length . place . fst) counts)
    pad s = s <> replicate (width - length s) ' '

parseMain :: [(String, AnnotatedUPT)] -- ^Prelude: [(VariableName, BindedUPT)]
          -> String                            -- ^Raw string to be parserd.
          -> Either ResolverError Term3               -- ^Error on Left.
parseMain prelude' str =
  let
      prelude = [("Prelude", Right . second unAnnotatedUPT <$> prelude')]
      parseAuxModule :: String -> (String, [Either AUPT (String, AUPT)])
      parseAuxModule str =
        case sequence ("AuxModule", parseModule ("import Prelude\n" <> str)) of
          Left e    -> error $ show e
          Right pam -> second (fmap (bimap unAnnotatedUPT (second unAnnotatedUPT))) pam
  in main2Term3 (parseAuxModule str:prelude) "AuxModule"

eval2IExpr :: [(String, [Either AUPT (String, AUPT)])] -> String -> Either String CompiledExpr
eval2IExpr extraModuleBindings str =
  first errorBundlePretty (runParser (parseOneExprOrTopLevelDefs resolved) "" str)
  >>= first show . process . AnnotatedUPT
  >>= tt . first show . compileUnitTest
    where
      tt = \case
        Left e -> Left $ show e
        Right x -> pure x
      aux = (\str -> Left (GeneratedLoc "eval2IExpr.import" Nothing :< ImportQualifiedUPF str str)) . fst <$> extraModuleBindings
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
      pure ((i, basicEval ZeroB) :< embedB ZeroSF)
    StuckFW EnvSF -> do
      i <- statePlus1
      pure ((i, basicEval ZeroB) :< embedS EnvSF)
    StuckFW (SetEnvSF (iexpr0, x)) -> do
      i <- statePlus1
      x' <- x
      pure $ (i, basicEval $ SetEnvB iexpr0) :< embedS (SetEnvSF x')
    StuckFW (DeferSF ind (iexpr0, x)) -> do
      i <- statePlus1
      x' <- x
      pure $ (i, basicEval . StuckEE $ DeferSF (toEnum (-1)) iexpr0) :< embedS (DeferSF (toEnum (-1)) x')
    StuckFW (LeftSF (iexpr0, x)) -> do
      i <- statePlus1
      x' <- x
      pure $ (i, basicEval $ LeftB iexpr0) :< embedS (LeftSF x')
    StuckFW (RightSF (iexpr0, x)) -> do
      i <- statePlus1
      x' <- x
      pure $ (i, basicEval $ RightB iexpr0) :< embedS (RightSF x')
    BasicFW (PairSF (iexpr0, x) (iexpr1, y)) -> do
      i <- statePlus1
      x' <- x
      y' <- y
      pure $ (i, basicEval $ PairB iexpr0 iexpr1) :< embedB (PairSF x' y')
    StuckFW GateSF -> do
      i <- statePlus1
      pure $ (i, basicEval $ StuckEE GateSF) :< embedS GateSF

