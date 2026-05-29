{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
module Common where

import Control.Applicative
import Control.Comonad.Cofree (Cofree ((:<)))
import Data.Bifunctor
import Data.Functor.Foldable (embed, project)
import qualified Data.Map as Map
import System.IO
import System.Posix.IO
import System.Posix.Process
import System.Posix.Types (ProcessID)
import Telomare
import Telomare.Parser
import Telomare.Resolver
import Telomare.TypeChecker
import Test.QuickCheck
import Test.QuickCheck.Gen

class TestableIExpr a where
  getIExpr :: a -> StuckExpr -- maybe this should be StuckExpr

newtype TestIExpr = TestIExpr StuckExpr

newtype ValidTestIExpr = ValidTestIExpr TestIExpr

newtype ArrowTypedTestIExpr = ArrowTypedTestIExpr TestIExpr

newtype URTestExpr = URTestExpr {unURTest :: Term3} deriving Show

newtype IExprWrapper a = IExprWrapper a
  deriving (Eq, Show, Functor)

instance Applicative IExprWrapper where
  pure = IExprWrapper
  (<*>) (IExprWrapper f) (IExprWrapper x) = IExprWrapper $ f x

type DataTypedIExpr = IExprWrapper StuckExpr

instance TestableIExpr DataTypedIExpr where
  getIExpr (IExprWrapper x) = x

instance TestableIExpr TestIExpr where
  getIExpr (TestIExpr x) = x

instance Show TestIExpr where
  show (TestIExpr t) = show t

instance TestableIExpr ValidTestIExpr where
  getIExpr (ValidTestIExpr x) = getIExpr x

instance Show ValidTestIExpr where
  show (ValidTestIExpr v) = show v

instance TestableIExpr ArrowTypedTestIExpr where
  getIExpr (ArrowTypedTestIExpr x) = getIExpr x

instance Show ArrowTypedTestIExpr where
  show (ArrowTypedTestIExpr x) = show x

lift1Texpr :: (StuckExpr -> StuckExpr) -> TestIExpr -> TestIExpr
lift1Texpr f (TestIExpr x) = TestIExpr $ f x

lift2Texpr :: (StuckExpr -> StuckExpr -> StuckExpr) -> TestIExpr -> TestIExpr -> TestIExpr
lift2Texpr f (TestIExpr a) (TestIExpr b) = TestIExpr $ f a b

instance Arbitrary TestIExpr where
  arbitrary = sized tree where
    tree i = let half = div i 2
                 pure2 = pure . TestIExpr
             in case i of
                  0 -> oneof $ fmap pure2 [zeroB, envB]
                  x -> oneof
                    [ pure2 zeroB
                    , pure2 envB
                    , lift2Texpr pairB <$> tree half <*> tree half
                    , lift1Texpr setEnvB <$> tree (i - 1)
                    , lift1Texpr (stuckEE . DeferSF (toEnum (-1))) <$> tree (i - 1)
                    , lift2Texpr gateB <$> tree half <*> tree half
                    , lift1Texpr leftB <$> tree (i - 1)
                    , lift1Texpr rightB <$> tree (i - 1)
                    ]
  shrink (TestIExpr x) = case x of
    ZeroB -> []
    StuckEE EnvSF -> []
    StuckEE (GateSF a b) -> TestIExpr a : TestIExpr b :
      [lift2Texpr gateB a' b' | (a', b') <- shrink (TestIExpr a, TestIExpr b)]
    StuckEE (LeftSF x) -> TestIExpr x : (fmap (lift1Texpr leftB) . shrink $ TestIExpr x)
    StuckEE (RightSF x) -> TestIExpr x : (fmap (lift1Texpr rightB) . shrink $ TestIExpr x)
    StuckEE (SetEnvSF x) -> TestIExpr x : (fmap (lift1Texpr setEnvB) . shrink $ TestIExpr x)
    StuckEE (DeferSF fi x) -> TestIExpr x : (fmap (lift1Texpr (stuckEE . DeferSF fi)) . shrink $ TestIExpr x)
    PairB a b -> TestIExpr a : TestIExpr  b :
      [lift2Texpr pairB a' b' | (a', b') <- shrink (TestIExpr a, TestIExpr b)]

instance Arbitrary DataType where
  arbitrary = sized gen where
    gen i = let half = div i 2 in oneof $ pure ZeroType :
      if i < 1
      then []
      else [ ArrType <$> gen half <*> gen half
           , PairType <$> gen half <*> gen half
           ]

zeroTyped = null . typeCheck ZeroTypeP . fromTelomare . getIExpr

genTypedTree :: Maybe DataType -> DataType -> Int -> Gen StuckExpr
genTypedTree ti t i =
  let half = div i 2
      optionEnv = if ti == Just t
                  then (pure envB :)
                  else id
      optionGate ti' to = if ti' == ZeroType
                          then ((gateB <$> genTypedTree ti to half <*> genTypedTree ti to half) :)
                          else id
      setEnvOption to = arbitrary >>= makeSetEnv where
        makeSetEnv ti' = setEnvB <$> genTypedTree ti (PairType (ArrType ti' to) ti') (i - 1)
      leftOption to = arbitrary >>= (\ti' -> leftB <$> genTypedTree ti (PairType to ti') (i - 1))
      rightOption to = arbitrary >>= (\ti' -> rightB <$> genTypedTree ti (PairType ti' to) (i - 1))
  in oneof . optionEnv $ case t of
                    ZeroType ->
                      pure zeroB : if i < 1
                      then []
                      else [ genTypedTree ti (PairType ZeroType ZeroType) i
                          , setEnvOption ZeroType
                          , leftOption ZeroType
                          , rightOption ZeroType
                          ]
                    PairType ta tb ->
                      (pairB <$> genTypedTree ti ta half <*> genTypedTree ti tb half) :
                      if i < 1
                      then []
                      else [ setEnvOption (PairType ta tb)
                          , leftOption (PairType ta tb)
                          , rightOption (PairType ta tb)
                          ]
                    ArrType ti' to ->
                      (stuckEE . DeferSF (toEnum (-1)) <$> genTypedTree (Just ti') to (i - 1)) :
                      if i < 1
                      then []
                      else optionGate ti' to
                      [ leftOption (ArrType ti' to)
                      , rightOption (ArrType ti' to)
                      ]

instance Arbitrary DataTypedIExpr where
  arbitrary = IExprWrapper <$> sized (genTypedTree Nothing ZeroType)
  shrink (IExprWrapper x) = fmap (IExprWrapper . getIExpr) . filter zeroTyped . shrink $ TestIExpr x

typeable x = case inferType (fromTelomare $ getIExpr x) of
  Left _ -> False
  _      -> True

instance Arbitrary ValidTestIExpr where
  arbitrary = ValidTestIExpr <$> suchThat arbitrary typeable
  shrink (ValidTestIExpr te) = fmap ValidTestIExpr . filter typeable $ shrink te

simpleArrowTyped x = inferType (fromTelomare $ getIExpr x) == Right (ArrTypeP ZeroTypeP ZeroTypeP)

instance Arbitrary ArrowTypedTestIExpr where
  arbitrary = ArrowTypedTestIExpr <$> suchThat arbitrary simpleArrowTyped
  shrink (ArrowTypedTestIExpr atte) = fmap ArrowTypedTestIExpr . filter simpleArrowTyped $ shrink atte

instance Arbitrary UnprocessedParsedTerm where
  arbitrary = sized (genTree []) where
    leaves :: [String] -> Gen UnprocessedParsedTerm
    leaves varList =
      oneof $
          (if not (null varList) then ((embed . VarUPF <$> elements varList) :) else id)
          [ StringUP <$> elements (fmap (("s" <>) . show) [1..9]) -- chooseAny
          , IntUP <$> elements [0..9]
          , ChurchUP <$> elements [0..9]
          ]
    lambdaTerms = ["w", "x", "y", "z"]
    letTerms = fmap (("l" <>) . show) [1..255]
    identifierList :: Gen [String]
    identifierList = frequency
      [ (1, pure . cycle $ letTerms)
      , (3, pure . cycle $ lambdaTerms <> letTerms)
      , (1, cycle <$> shuffle (lambdaTerms <> letTerms))
      ]
    genImportName :: Gen String
    genImportName = do
      firstChar <- elements $ ['a'..'z'] <> ['A'..'Z']
      len <- choose (3, 15)
      rest <- vectorOf (len - 1)
                       (frequency [ (10, elements (['a'..'z'] <> ['A'..'Z'] <> ['0'..'9']))
                                  , (1, pure '_')
                                  , (1, pure '.')
                                  ])
      return (firstChar : rest)
    genTree :: [String] -> Int -> Gen UnprocessedParsedTerm
    genTree varList i = let half = div i 2
                            third = div i 3
                            recur = genTree varList
                            childList = do
                              listSize <- choose (0, i)
                              let childShare = div i listSize
                              vectorOf listSize $ genTree varList childShare
                        in case i of
                                 0 -> leaves varList
                                 x -> oneof
                                   [ leaves varList
                                   , ImportUP <$> genImportName
                                   , ImportQualifiedUP <$> genImportName <*> genImportName
                                   , HashUP <$> recur (i - 1)
                                   , LeftUP <$> recur (i - 1)
                                   , RightUP <$> recur (i - 1)
                                   , TraceUP <$> recur (i - 1)
                                    , elements lambdaTerms >>= \var -> LamUP (locatedName UnknownLoc var) <$> genTree (var : varList) (i - 1)
                                   , ITEUP <$> recur third <*> recur third <*> recur third
                                   , UnsizedRecursionUP <$> recur third <*> recur third <*> recur third
                                   , ListUP <$> childList
                                    , do { listSize <- choose (2, max i 2)
                                         ; let childShare = div i listSize
                                               makeList [] = pure []
                                               makeList (v:vl) = do
                                                  newTree <- genTree (v:varList) childShare
                                                  ((locatedName UnknownLoc v, newTree) :) <$> makeList vl
                                         ; vars <- take listSize <$> identifierList
                                         ; childList <- makeList vars
                                         ; pure $ LetUP (init childList) (letBindingValue . last $ childList)
                                         }
                                   , PairUP <$> recur half <*> recur half
                                   , AppUP <$> recur half <*> recur half
                                   ]
  shrink = fmap embed . shrink' . project where
    shrink' = \case
      StringUPF s -> case s of
        [] -> []
        _  -> pure . StringUPF $ tail s
      IntUPF i -> case i of
        0 -> []
        x -> pure . IntUPF $ x - 1
      ChurchUPF i -> case i of
        0 -> []
        x -> pure . ChurchUPF $ x - 1
      UnsizedRecursionUPF t r b -> project t : project r : project b : [UnsizedRecursionUPF nt nr nb | (nt, nr, nb) <- shrink (t,r,b)]
      VarUPF _ -> []
      HashUPF x -> project x : fmap HashUPF (shrink x)
      LeftUPF x -> project x : fmap LeftUPF (shrink x)
      RightUPF x -> project x : fmap RightUPF (shrink x)
      TraceUPF x -> project x : fmap TraceUPF (shrink x)
      LamUPF v x -> project x : fmap (LamUPF v) (shrink x)
      ITEUPF i t e -> project i : project t : project e : [ITEUPF ni nt ne | (ni, nt, ne) <- shrink (i,t,e)]
      ListUPF l -> case l of
        [e] -> if null $ shrink e then [project e] else project e : fmap (ListUPF . pure) (shrink e)
        _   -> project (head l) : ListUPF (tail l) : fmap (ListUPF . shrink) l
    {-
      LetUP l i -> i : case l of -- TODO make this do proper, full enumeration
        [(v,e)] -> if null $ shrink e then [e] else e : map (flip LetUP i . pure . (v,)) (shrink e) <> (map (LetUP l) (shrink i))
        _ -> let shrinkBinding (n, v) = map (n,) $ shrink v
            in snd (head l) : LetUP (tail l) i : map (flip LetUP i . second shrink) l
  -}
      LetUPF l i -> let shrinkBinding (n, v) = (n,) <$> shrink v
                        removeAt n x = let (f,s) = splitAt n x in (f <> tail s)
                        makeOptions f n [] = error "debugging split here"
                        makeOptions f n x = let (pa,c:pz) = splitAt n x in ((pa ++) . (:pz) <$> f c)
                        lessBindings = if length l > 1
                          then [LetUPF (removeAt n l) i | n <- [0..length l - 1]]
                          else []
                    in project i : (lessBindings <> concat [(`LetUPF` i) <$> makeOptions shrinkBinding n l | n <- [0..length l - 1]])
      PairUPF a b -> project a : project b : [PairUPF na nb | (na, nb) <- shrink (a,b)]
      AppUPF f i -> project f : project i : [AppUPF nf ni | (nf, ni) <- shrink (f,i)]

instance Arbitrary Term1 where
  arbitrary = sized (genTree []) where
    leaves :: [String] -> Gen Term1
    leaves varList =
      oneof $
          (if not (null varList) then (((UnknownLoc :<) . TVarF <$> elements varList) :) else id)
          [ pure $ UnknownLoc :< ParserTermB ZeroSF
          ]
    lambdaTerms = ["w", "x", "y", "z"]
    letTerms = fmap (("l" <>) . show) [1..255]
    identifierList = frequency
      [ (1, pure . cycle $ letTerms)
      , (3, pure . cycle $ lambdaTerms <> letTerms)
      , (1, cycle <$> shuffle (lambdaTerms <> letTerms))
      ]
    genTree :: [String] -> Int -> Gen Term1
    genTree varList i = let half = div i 2
                            third = div i 3
                            recur = genTree varList
                            childList = do
                              -- listSize <- chooseInt (0, i)
                              listSize <- choose (0, i)
                              let childShare = div i listSize
                              vectorOf listSize $ genTree varList childShare
                        in case i of
                                 0 -> leaves varList
                                 x -> oneof
                                   [ leaves varList
                                   , (UnknownLoc :<) . THashF <$> recur (i - 1)
                                   , (UnknownLoc :<) . TLeftF <$> recur (i - 1)
                                   , (UnknownLoc :<) . TRightF <$> recur (i - 1)
                                   , (UnknownLoc :<) . TTraceF <$> recur (i - 1)
                                   , elements lambdaTerms >>= \var -> (UnknownLoc :<) . TLamF (Open var) <$> genTree (var : varList) (i - 1)
                                   , (\a b c -> UnknownLoc :< TITEF a b c) <$> recur third <*> recur third <*> recur third
                                   , (\a b c -> UnknownLoc :< TLimitedRecursionF a b c) <$> recur third <*> recur third <*> recur third
                                   , (\a b -> UnknownLoc :< ParserTermB (PairSF a b)) <$> recur half <*> recur half
                                   , (\a b -> UnknownLoc :< TAppF a b) <$> recur half <*> recur half
                                   ]
  shrink = \case
    _ :< ParserTermB ZeroSF -> []
    anno :< TLimitedRecursionF t r b -> t : r : b : [anno :< TLimitedRecursionF nt nr nb | (nt, nr, nb) <- shrink (t,r,b)]
    _ :< TVarF _ -> []
    anno :< THashF x -> x : fmap ((anno :<) . THashF) (shrink x)
    anno :< TLeftF x -> x : fmap ((anno :<) . TLeftF) (shrink x)
    anno :< TRightF x -> x : fmap ((anno :<) . TRightF) (shrink x)
    anno :< TTraceF x -> x : fmap ((anno :<) . TTraceF) (shrink x)
    anno :< TLamF v x -> x : fmap ((anno :<) . TLamF v) (shrink x)
    anno :< TITEF i t e -> i : t : e : [anno :< TITEF ni nt ne | (ni, nt, ne) <- shrink (i,t,e)]
    anno :< ParserTermB (PairSF a b) -> a : b : [anno :< ParserTermB (PairSF na nb) | (na, nb) <- shrink (a,b)]
    anno :< TAppF f i -> f : i : [anno :< TAppF nf ni | (nf, ni) <- shrink (f,i)]

instance Arbitrary Term2 where
  arbitrary = do
    term1 <- arbitrary :: Gen Term1
    let term2 = case debruijinize [] term1 of
                  Left str -> error $ "Non valid `Term1` generated from `arbitrarry :: Gen Term1`: "
                                        <> show term1
                                        <> " With error message: "
                                        <> shre str
                  Right t2 -> t2
        shre :: ResolverError -> String
        shre = show
    pure term2
  shrink = \case
    _ :< ParserTermB ZeroSF -> []
    anno :< TLimitedRecursionF t r b -> t : r : b : [anno :< TLimitedRecursionF nt nr nb | (nt, nr, nb) <- shrink (t,r,b)]
    _ :< TVarF _ -> []
    anno :< THashF x -> x : fmap ((anno :<) . THashF) (shrink x)
    anno :< TLeftF x -> x : fmap ((anno :<) . TLeftF) (shrink x)
    anno :< TRightF x -> x : fmap ((anno :<) . TRightF) (shrink x)
    anno :< TTraceF x -> x : fmap ((anno :<) . TTraceF) (shrink x)
    anno :< TLamF v x -> x : fmap ((anno :<) . TLamF v) (shrink x)
    anno :< TITEF i t e -> i : t : e : [anno :< TITEF ni nt ne | (ni, nt, ne) <- shrink (i,t,e)]
    anno :< ParserTermB (PairSF a b) -> a : b : [anno :< ParserTermB (PairSF na nb) | (na, nb) <- shrink (a,b)]
    anno :< TAppF f i -> f : i : [anno :< TAppF nf ni | (nf, ni) <- shrink (f,i)]
