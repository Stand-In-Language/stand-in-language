{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Telomare.Eval where

import Control.Comonad.Cofree (Cofree ((:<)), hoistCofree)
import Control.Lens.Plated hiding (para)
import Control.Monad.Except
import Control.Monad.Reader (Reader, runReader)
import Control.Monad.State (State, StateT, evalState)
import qualified Control.Monad.State as State
import Control.Monad.Trans.Accum (AccumT)
import qualified Control.Monad.Trans.Accum as Accum
import Data.Bifunctor (bimap, first)
import Data.DList (DList)
import Data.Functor.Foldable (Base, cata, embed, para, project)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void
import Debug.Trace
import System.IO
import qualified System.IO.Strict as Strict
import System.Process

import PrettyPrint
import Telomare (BreakState, BreakState', ExprA (..), FragExpr (..),
                 FragExprF (..), FragIndex (FragIndex), IExpr (..), IExprF (..),
                 LocTag (..), PartialType (..), RecursionPieceFrag,
                 RecursionSimulationPieces (..), RunTimeError (..),
                 TelomareLike (..), Term3 (Term3), Term4 (Term4),
                 UnsizedRecursionToken (..), app, forget, g2s, innerChurchF,
                 insertAndGetKey, pattern AbortAny, pattern AbortRecursion,
                 pattern AbortUser, rootFrag, s2g, tag, unFragExprUR)
import Telomare.Optimizer (optimize)
import Telomare.Parser (AnnotatedUPT, Pattern, PrettyUPT (PrettyUPT),
                        UnprocessedParsedTerm (..), UnprocessedParsedTermF (..),
                        parseOneExprOrTopLevelDefs, parsePrelude)
import Telomare.Possible (AbortExpr, VoidF, abortExprToTerm4, evalA, sizeTerm,
                          term3ToUnsizedExpr)
import Telomare.Resolver (parseMain, process)
import Telomare.RunTime (hvmEval, optimizedEval, pureEval, rEval, simpleEval)
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

fromFullEnv :: Applicative a => (ExpP -> a IExpr) -> ExpP -> a IExpr
fromFullEnv _ ZeroP         = pure Zero
fromFullEnv f (PairP a b)   = Pair <$> f a <*> f b
fromFullEnv _ VarP          = pure Env
fromFullEnv f (SetEnvP x _) = SetEnv <$> f x
fromFullEnv f (DeferP x)    = Defer <$> f x
fromFullEnv f (GateP a b)   = Gate <$> f a <*> f b
fromFullEnv f (LeftP x)     = PLeft <$> f x
fromFullEnv f (RightP x)    = PRight <$> f x
fromFullEnv _ TraceP        = pure Trace

instance TelomareLike ExpP where
  fromTelomare = snd . annotateEnv
  toTelomare = fix fromFullEnv

partiallyEvaluate :: ExpP -> Either RunTimeError IExpr
partiallyEvaluate se@(SetEnvP _ True) = Defer <$> (fix fromFullEnv se >>= pureEval . optimize)
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
        _ :< AuxFragF (SizingWrapper _ x) -> transformM changeFrag $ unFragExprUR x
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

findChurchSize :: Term3 -> Either EvalError Term4
findChurchSize = pure . convertPT (const 255)
-- findChurchSize = calculateRecursionLimits -- works fine for unit tests, but uses too much memory for tictactoe

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

convertAbortMessage :: IExpr -> String
convertAbortMessage = \case
  AbortRecursion -> "recursion overflow (should be caught by other means)"
  AbortUser s -> "user abort: " <> g2s s
  AbortAny -> "user abort of all possible abort reasons (non-deterministic input)"
  x -> "unexpected abort: " <> show x

runStaticChecks :: Term4 -> Either EvalError Term4
runStaticChecks t@(Term4 termMap) =
  let result = evalA combine (Just Zero) t
      combine a b = case (a,b) of
        (Nothing, _) -> Nothing
        (_, Nothing) -> Nothing
        (a, _)       -> a
  in case result of
    Nothing -> pure t
    Just e  -> Left . StaticCheckError $ convertAbortMessage e

compileMain :: Term3 -> Either EvalError IExpr
compileMain term = case typeCheck (PairTypeP (ArrTypeP ZeroTypeP ZeroTypeP) AnyType) term of
  Just e -> Left $ TCE e
  _      -> compile pure term -- TODO add runStaticChecks back in

compileUnitTest :: Term3 -> Either EvalError IExpr
compileUnitTest = compile runStaticChecks

compile :: (Term4 -> Either EvalError Term4) -> Term3 -> Either EvalError IExpr
compile staticCheck t = debugTrace ("compiling term3:\n" <> prettyPrint t)
  $ case toTelomare . removeChecks <$> (findChurchSize t >>= staticCheck) of
      Right (Just i) -> pure i
      Right Nothing  -> Left CompileConversionError
      Left e         -> Left e

runMain :: String -> String -> IO ()
runMain preludeString s =
  let prelude :: [(String, AnnotatedUPT)]
      prelude =
        case parsePrelude preludeString of
          Right p -> p
          Left pe -> error pe
  in
    case compileMain <$> parseMain prelude s of
      Left e -> putStrLn $ concat ["failed to parse ", s, " ", e]
      Right (Right g) -> evalLoop g
      Right z -> putStrLn $ "compilation failed somehow, with result " <> show z

schemeEval :: IExpr -> IO ()
schemeEval iexpr = do
  writeFile "scheme.txt" ('(' : (show (app iexpr Zero) <> ")"))
  (_, Just mhout, _, _) <- createProcess (shell "chez-script runtime.so") { std_out = CreatePipe }
  scheme <- hGetContents mhout
  putStrLn scheme


evalLoop :: IExpr -> IO ()
evalLoop iexpr =
  let mainLoop s = do
        result <- simpleEval $ app iexpr s
        case result of
          Zero -> putStrLn "aborted"
          (Pair disp newState) -> do
            putStrLn . g2s $ disp
            case newState of
              Zero -> putStrLn "done"
              _ -> do
                inp <- s2g <$> getLine
                mainLoop $ Pair inp newState
          r -> putStrLn ("runtime error, dumped " <> show r)
  in mainLoop Zero

-- |Same as `evalLoop`, but keeping what was displayed.
-- TODO: make evalLoop and evalLoop always share eval method (i.e. simpleEval, hvmEval)
evalLoop_ :: IExpr -> IO String
evalLoop_ iexpr =
  let mainLoop prev s = do
        -- result <- optimizedEval (app peExp s)
        result <- simpleEval (app iexpr s)
        --result <- simpleEval $ traceShowId $ app peExp s
        case result of
          Zero -> pure $ prev <> "\n" <> "aborted"
          (Pair disp newState) -> do
            let d = g2s disp
            case newState of
              Zero -> pure $ prev <> "\n" <> d <> "\ndone"
              _ -> do
                inp <- s2g <$> getLine
                mainLoop (prev <> "\n" <> d) $ Pair inp newState
          r -> pure ("runtime error, dumped " <> show r)
  in mainLoop "" Zero

calculateRecursionLimits :: Term3 -> Either EvalError Term4
calculateRecursionLimits t3 =
  let abortExprToTerm4' :: AbortExpr -> Either IExpr Term4
      abortExprToTerm4' = abortExprToTerm4
      limitSize = 256
  in case fmap abortExprToTerm4' . sizeTerm limitSize $ term3ToUnsizedExpr limitSize t3 of
    Left urt -> Left $ RecursionLimitError urt
    Right t  -> case t of
      Left a  -> Left . StaticCheckError . convertAbortMessage $ a
      Right t -> pure t

prelude :: IO [(String, AnnotatedUPT)]
prelude = do
  preludeString <- Strict.readFile "Prelude.tel"
  case parsePrelude preludeString of
    Right p -> pure p
    Left pe -> error pe

eval2IExpr :: [(String, AnnotatedUPT)] -> String -> Either String IExpr
eval2IExpr prelude str = bimap errorBundlePretty (\x -> DummyLoc :< LetUPF prelude x) (runParser (parseOneExprOrTopLevelDefs prelude) "" str)
                           >>= process prelude
                           >>= first show . compileUnitTest

tagIExprWithEval :: IExpr -> Cofree IExprF (Int, Either RunTimeError IExpr)
tagIExprWithEval iexpr = evalState (para alg iexpr) 0 where
  statePlus1 :: State Int Int
  statePlus1 = do
      i <- State.get
      State.modify (+ 1)
      pure i
  alg :: Base IExpr
              ( IExpr
              , State Int (Cofree IExprF (Int, Either RunTimeError IExpr))
              )
      -> State Int (Cofree IExprF (Int, Either RunTimeError IExpr))
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
  upt2iexpr u = process prelude (tag DummyLoc u) >>= first show . compileUnitTest
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
