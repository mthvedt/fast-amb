{-# LANGUAGE
  FlexibleContexts,
  FlexibleInstances,
  GeneralizedNewtypeDeriving,
  KindSignatures,
  ScopedTypeVariables,
  TypeFamilies,
  ViewPatterns
#-}
-- To prevent the rewriting of properties we wanted to test, we have:
{-# OPTIONS_GHC
  -fno-enable-rewrite-rules
#-}

module Control.Logic.Test.Amb (ambTests) where

import GHC.Prim

import Control.Monad
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans
import Data.Foldable (toList)

import Control.DeepSeq

import Control.Logic.Amb

import Test.QuickCheck
import Test.QuickCheck.Function
import Test.QuickCheck.Gen
import Test.QuickCheck.Random

import Distribution.TestSuite.QuickCheck

timeout :: Testable prop => prop -> Property
timeout = within $ 1000 * 2

root :: Double -> Int -> Int
root _ i = i
-- root d i = min i . round $ fromIntegral i ** d

newtype ArbTwoThirds p = ArbTwoThirds { unArbTwoThirds :: p }
  deriving Show

instance Arbitrary p => Arbitrary (ArbTwoThirds p) where
  arbitrary = scale (root (2 / 3)) arbitrary
  shrink (ArbTwoThirds p) = ArbTwoThirds <$> shrink p

newtype ArbOneThird p = ArbOneThird { unArbOneThird :: p }
  deriving Show

instance Arbitrary p => Arbitrary (ArbOneThird p) where
  arbitrary = scale (root (1 / 3)) arbitrary
  shrink (ArbOneThird p) = ArbOneThird <$> shrink p

-- Cases are injective, so you probably want to use a new type for each one.
-- We express this with type families. Fundeps are less verbose, but are more likely to cause
-- situations that GHC considers undecidable, since you often want to define cases in a fairly
-- generic way.
-- TODO doc for reals
class (Arbitrary (Case c), Show (Case c), NFData (Case c)) => Harness c where
  type Case c :: *
  type Target c :: *
  gen :: c -> Case c -> Target c

class TestEq t where
  runEq :: t -> t -> Bool

-- Per Haskell's free theorems, any parameterized type which works on any given type parameter
-- works on all type parameters (if that parameter is unconstrained).
{-# ANN axiomFunctorId "HLint: ignore Functor law" #-}
axiomFunctorId :: (Functor f, Harness c, Target c ~ f Int, TestEq (f Int)) => c -> Case c -> Bool
axiomFunctorId c g = (id <$> fx) `runEq` fx where
  fx = gen c g

{-# ANN axiomFunctorComp "HLint: ignore Functor law" #-}
axiomFunctorComp :: (Functor f, Harness c, Target c ~ f Int, TestEq (f Int)) =>
  c -> Case c -> Fun Int Int -> Fun Int Int -> Bool
axiomFunctorComp c g (apply -> fn1) (apply -> fn2) = (fn2 . fn1 <$> fx) `runEq` (fmap fn2 . fmap fn1 $ fx) where
  fx = gen c g

-- TODO: applicative axioms
testFunctor :: (Functor f, Harness c, Target c ~ f Int, TestEq (f Int)) => String -> c -> Test
testFunctor typeclass_desc c = testGroup ("Functor axioms for " ++ typeclass_desc)
  [ testProperty "Functor identity law" . timeout $ axiomFunctorId c
  , testProperty "Functor composition law" . timeout $ axiomFunctorComp c
  ]

{-# ANN axiomMonadLeftId "HLint: ignore Monad law, left identity" #-}
axiomMonadLeftId :: (Monad m, Harness c, Target c ~ m Int, TestEq (m Int)) => c -> Int -> Fun Int (Case c) -> Bool
axiomMonadLeftId c i (apply -> fcase) = (return i >>= f) `runEq` f i where
  f = gen c . fcase

{-# ANN axiomMonadRightId "HLint: ignore Monad law, right identity" #-}
axiomMonadRightId :: (Monad m, Harness c, Target c ~ m Int, TestEq (m Int)) => c -> Case c -> Bool
axiomMonadRightId c g = (mx >>= return) `runEq` mx where
  mx = gen c g

{-# ANN axiomMonadAssoc "HLint: ignore Functor law" #-}
axiomMonadAssoc :: (Monad m, Harness c, Target c ~ m Int, TestEq (m Int)) =>
  c -> Case c -> Fun Int (Case c) -> Fun Int (Case c) -> Bool
axiomMonadAssoc c g (apply -> fcase) (apply -> gcase) = ((mx >>= mf) >>= mg) `runEq` (mx >>= (mf >=> mg)) where
  mx = gen c g
  mf = gen c . fcase
  mg = gen c . gcase

testMonad :: (Monad m, Harness c, Target c ~ m Int, TestEq (m Int)) => String -> c -> Test
testMonad typeclass_desc c = testGroup ("Monad axioms for " ++ typeclass_desc)
  [ testFunctor typeclass_desc c
  , testProperty "Monad left identity law" . timeout $ axiomMonadLeftId c
  , testProperty "Monad right identity law" . timeout $ axiomMonadRightId c
  , testProperty "Monad associativity law" . timeout $ axiomMonadAssoc c
  ]

axiomMTId :: (MonadTrans t, Monad m, Monad (t m), Harness c, Target c ~ t m Int, TestEq (t m Int)) =>
  c -> Int -> Bool
axiomMTId (_witness :: c) i = (return i :: Target c) `runEq` lift (return i)

-- TODO is this wrong?
axiomMTDistributive :: (MonadTrans t, Monad m, Monad (t m),
    Harness c, Target c ~ t m Int, Harness c0, Target c0 ~ m Int, TestEq (t m Int)) =>
  c0 -> c -> Case c0 -> Fun Int (Case c0) -> Bool
axiomMTDistributive c0 (_witness :: c) g (apply -> fcase) =
  lift (ma >>= mf) `runEq` ((lift ma :: Target c) >>= (lift . mf)) where
    ma = gen c0 g
    mf = gen c0 . fcase

testMonadTrans :: (MonadTrans t, Monad m, Monad (t m),
    Harness c, Target c ~ t m Int, Harness c0, Target c0 ~ m Int, TestEq (t m Int)) =>
  String -> c0 -> c -> Test
testMonadTrans typeclass_desc c0 c =  testGroup ("MonadTrans axioms for " ++ typeclass_desc)
  [ testProperty "MonadTrans identity law" . timeout $ axiomMTId c
  , testProperty "MonadTrans distributive law" . timeout $ axiomMTDistributive c0 c
  ]

-- Tests that ambs are depth-first.
axiomDepthFirst :: (Amb a, Harness c, Target c ~ a Int, TestEq (a Int)) => c -> ArbOneThird [[Case c]] -> Bool
axiomDepthFirst c cases = ambcat (ambcat <$> as) `runEq` join (ambcat <$> amb as) where
  as = fmap (gen c) <$> force (unArbOneThird cases)
--
testAmb :: (Amb a, Harness c, Target c ~ a Int, TestEq (a Int)) => String -> c -> Test
testAmb typeclass_desc c = testGroup ("Amb tests for " ++ typeclass_desc)
  [ testMonad typeclass_desc c
  , testProperty "Ambs are depth-first" . timeout $ axiomDepthFirst c
  ]

newtype TestState a = TestState (State Int a)
  deriving (Functor, Applicative, Monad)

testState :: (Int -> (a, Int)) -> TestState a
testState = TestState . state

runTestState :: TestState a -> Int -> (a, Int)
runTestState (TestState s) = runState s

instance Show (TestState a) where
  show (TestState s) = show $ Blind s

data IdentityCase = IdentityCase

instance Harness IdentityCase where
  type Case IdentityCase = Int
  type Target IdentityCase = Identity Int
  gen _ = return

data StateCase = StateCase

instance Harness StateCase where
  type Case StateCase = (Int, Int)
  type Target StateCase = TestState Int
  gen _ (x, y) = testState $ \i -> (x, x * 524287 + y * 8191 + i)

-- TODO: nomenclautre. Is 'Case' correct?
-- TODO: rename AmbTrans t -> AmbTrans a
-- TODO: consider renaming AmbTrans -> AmbT
newtype AmbTHarness (a :: (* -> *) -> * -> *) (m :: * -> *) c = AmbTHarness c

ambTCase :: c -> AmbTHarness a m c
ambTCase = AmbTHarness

instance (AmbTrans a m, Harness c, Target c ~ m Int) => Harness (AmbTHarness a m c) where
  type Case (AmbTHarness a m c) = [Maybe (Case c)]
  type Target (AmbTHarness a m c) = a m Int
  gen (AmbTHarness c0) gs = let toAmb (Just v) = lift v
                                toAmb Nothing = afail
                                -- We don't *need* this force, but it helps debug when there's a performance
                                -- problem in a test. Some of these tests are quite large.
                                gs' = fmap (gen c0) <$> force gs
                                amblist = toAmb <$> gs'
                            in ambcat amblist

testAmbT :: (AmbTrans a Identity, AmbTrans a TestState, TestEq (a Identity Int), TestEq (a TestState Int)) =>
  String -> a Identity Int -> Test
testAmbT typeclass_desc (_witness :: a Identity Int) = testGroup ("AmbT suite tests for " ++ typeclass_desc)
  [ testAmb typeclass_desc caseId
  -- , testMonadTrans typeclass_desc StateCase caseState
  -- , testAmb (typeclass_desc ++ " (as State transformer)") caseState
  ] where
    caseId :: AmbTHarness a Identity IdentityCase
    caseId = ambTCase IdentityCase
    caseState :: AmbTHarness a TestState StateCase
    caseState = ambTCase StateCase

instance (AmbTrans a Identity, Eq t) => TestEq (a Identity t) where
  runEq = ambEq

instance (AmbTrans a TestState, Eq t) => TestEq (a TestState t) where
  a `runEq` b = runTestState (toMaybeListM a) 1 == runTestState (toMaybeListM b) 1

ambTests :: Test
ambTests = testGroup "Control.Logic.Amb"
  [ testAmbT "ChurchAmb" (return 1 :: ChurchAmb Int)
  -- , testCase "ScottAmb" (return 1 :: ScottAmb Int)
  -- , testCase "ParigotAmb" (return 1 :: ParigotAmb Int)
  -- , testCase "FastAmb" (return 1 :: FastAmb Int)
  ]
