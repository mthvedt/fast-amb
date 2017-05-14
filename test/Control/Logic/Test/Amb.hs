{-# LANGUAGE
  FlexibleContexts,
  FlexibleInstances,
  TypeFamilies,
  ViewPatterns
#-}

module Control.Logic.Test.Amb (ambTests) where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans
import Data.Foldable (toList)

import qualified Control.Monad.Free as Free
import qualified Control.Monad.Free.Church as Church

import Test.QuickCheck
import Test.QuickCheck.Function
import Test.QuickCheck.Gen

import Distribution.TestSuite.QuickCheck

import Control.Logic.Amb

-- Per Haskell's free theorems, any parameterized type which works on any given type parameter
-- works on all type parameters (if that parameter is unconstrained).
{-# ANN axiomFunctorId "HLint: ignore Functor law" #-}
axiomFunctorId :: (Functor f, Eq (f Int)) => f Int -> f Int -> Bool
axiomFunctorId _w fx = (id <$> fx) == fx

{-# ANN axiomFunctorComp "HLint: ignore Functor law" #-}
axiomFunctorComp :: (Functor f, Eq (f Int)) => f Int -> f Int -> Fun Int Int -> Fun Int Int -> Bool
axiomFunctorComp _w fx (apply -> fn1) (apply -> fn2) = (fn2 . fn1 <$> fx) == (fmap fn2 . fmap fn1 $ fx)

-- TODO: applicative axioms
testFunctor _w typeclass_desc = testGroup ("Functor axioms for " ++ typeclass_desc)
  [ testProperty "Functor identity law" $ axiomFunctorId _w
  , testProperty "Functor composition law" $ axiomFunctorComp _w
  ]

{-# ANN axiomMonadLeftId "HLint: ignore Monad law, left identity" #-}
axiomMonadLeftId :: (Monad m, Eq (m Int)) => m Int -> Int -> Fun Int (m Int) -> Bool
axiomMonadLeftId _w x (apply -> f) = (return x >>= f) == f x

{-# ANN axiomMonadRightId "HLint: ignore Monad law, right identity" #-}
axiomMonadRightId :: (Monad m, Eq (m Int)) => m Int -> m Int -> Bool
axiomMonadRightId _w mx = (mx >>= return) == mx

{-# ANN axiomMonadAssoc "HLint: ignore Functor law" #-}
axiomMonadAssoc :: (Monad m, Eq (m Int)) => m Int -> m Int -> Fun Int (m Int) -> Fun Int (m Int) -> Bool
axiomMonadAssoc _w mx (apply -> mf) (apply -> mg) = ((mx >>= mf) >>= mg) == (mx >>= (mf >=> mg))

testMonad :: (Monad m, Arbitrary (m Int), Show (m Int), Eq (m Int)) => m Int -> String -> Test
testMonad _w typeclass_desc = testGroup ("Monad axioms for " ++ typeclass_desc)
  [ testFunctor _w typeclass_desc
  , testProperty "Monad left identity law" $ axiomMonadLeftId _w
  , testProperty "Monad right identity law" $ axiomMonadRightId _w
  , testProperty "Monad associativity law" $ axiomMonadAssoc _w
  ]

axiomMTId :: (MonadTrans t, Monad m, Monad (t m)) =>
  t m Int -> (t m Int -> t m Int -> Bool) -> Int -> Bool
axiomMTId _w eqf i = (return i `asTypeOf` _w) `eqf` lift (return i)

-- TODO this is wrong
axiomMTDistributive :: (MonadTrans t, Monad m, Monad (t m)) =>
  t m Int -> (t m Int -> t m Int -> Bool) -> m Int -> Fun Int (m Int) -> Bool
axiomMTDistributive _w eqf ma (apply -> mf) = lift (ma >>= mf) `eqf` (lift ma `asTypeOf` _w >>= (lift . mf))

testMonadTrans :: (MonadTrans t, Monad m, Monad (t m),
                   Arbitrary (m Int), Show (m Int)) =>
                   t m Int -> (t m Int -> t m Int -> Bool) -> String -> Test
testMonadTrans _w eqf typeclass_desc =  testGroup ("MonadTrans axioms for " ++ typeclass_desc)
  [ testProperty "MonadTrans identity law" $ axiomMTId _w eqf
  , testProperty "MonadTrans distributive law" $ axiomMTDistributive _w eqf
  ]

instance Arbitrary (State Int Int) where
  arbitrary = do
    f <- arbitrary
    return $ do
      r <- get
      modify f
      return r

-- Tests that joining an Amb of Ambs is the same as running amb on joined lists.
propAmbcat :: (Amb a, Arbitrary (a Int), Eq (a Int), Show (a Int)) => a Int -> [[Int]] -> Bool
propAmbcat _mw iss = (join . amb $ amb <$> iss) == amb (concat iss) `asTypeOf` _mw

testAmb :: (Amb a, Arbitrary (a Int), Eq (a Int), Show (a Int)) => a Int -> String -> Test
testAmb _mw typeclass_desc = testGroup ("Amb tests for " ++ typeclass_desc)
  [ testMonad _mw typeclass_desc
  , testProperty "Join flattens amb" $ propAmbcat . (`asTypeOf` _mw)
  ]

-- TODO: Trans tests for AmbT
newtype TestState a = TestState (Blind (State Int a))

runTestState :: TestState a -> Int -> (a, Int)
runTestState (TestState (Blind s)) = runState s

instance Show (TestState a) where
  show (TestState blind) = show blind

instance Functor TestState where
  fmap = liftM

instance Applicative TestState where
  pure = return
  (<*>) = ap

instance Monad TestState where
  return x = TestState . Blind $ return x
  (TestState (Blind m1)) >>= f = TestState . Blind . state $ \s0 -> let (x, s1) = runState m1 s0
                                                                        (TestState (Blind m2)) = f x
                                                                    in runState m2 s1

instance Arbitrary t => Arbitrary (TestState t) where
  arbitrary = TestState . Blind . state <$> arbitrary

genAmbState :: (MonadTrans t, Amb (t TestState)) => [Maybe (TestState Int)] -> t TestState Int
genAmbState vs = let toAmb (Just v) = lift v
                     toAmb Nothing = afail
                 in join . amb $ toAmb <$> vs

ambStateEq :: AmbFold TestState a => a Int -> a Int -> Bool
ambStateEq a b = runTestState (toMaybeListM a) 1 == runTestState (toMaybeListM b) 1

testAmbT :: (MonadTrans t, AmbFold Identity (t Identity), AmbFold TestState (t TestState),
             Arbitrary (t Identity Int), Eq (t Identity Int), Show (t Identity Int)) =>
                t Identity Int -> t TestState Int -> String -> Test
testAmbT _mw _tmw typeclass_desc = testGroup ("AmbTrans tests for " ++ typeclass_desc)
  [ testMonadTrans _tmw ambStateEq typeclass_desc
  , testMonad _mw typeclass_desc
  ]

ambArbitrary :: (Amb a, Arbitrary v) => Gen (a v)
ambArbitrary = amb <$> arbitrary

ambShrink :: (Amb a, AmbFold Identity a, Arbitrary t) => a t -> [a t]
ambShrink = (amb <$>) . shrink . toList . asFoldable

-- (Amb a, Arbitrary t) => Arbitrary (a t) is undecidable and yields overlapping instances.
instance Arbitrary t => Arbitrary (ChurchAmb t) where
  arbitrary = ambArbitrary
  shrink = ambShrink

instance Arbitrary t => Arbitrary (ScottAmb t) where
  arbitrary = ambArbitrary
  shrink = ambShrink

instance Arbitrary t => Arbitrary (ParigotAmb t) where
  arbitrary = ambArbitrary
  shrink = ambShrink

instance Arbitrary t => Arbitrary (FastAmb t) where
  arbitrary = ambArbitrary
  shrink = ambShrink

ambTests :: Test
ambTests = testGroup "Control.Logic.Amb"
  [ testAmbT (return 1 :: ChurchAmb Int) (return 1) "ChurchAmb"
  , testAmbT (return 1 :: ScottAmb Int) (return 1) "ScottAmb"
  , testAmbT (return 1 :: ParigotAmb Int) (return 1) "ParigotAmb"
  , testAmbT (return 1 :: FastAmb Int) (return 1) "FastAmb"
  ]
