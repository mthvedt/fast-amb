{-# LANGUAGE
  FlexibleInstances,
  GeneralizedNewtypeDeriving,
  ViewPatterns
#-}

module Tests (tests) where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans

import qualified Control.Monad.Free as Free
import qualified Control.Monad.Free.Church as Church

import Test.QuickCheck
import Test.QuickCheck.Function
import Test.QuickCheck.Gen

import Distribution.TestSuite.QuickCheck

import Amb

{-# ANN axiomFunctorId "HLint: ignore Functor law" #-}
axiomFunctorId :: (Functor f, Eq (f a)) => f a -> Bool
axiomFunctorId fx = (id <$> fx) == fx

{-# ANN axiomFunctorComp "HLint: ignore Functor law" #-}
axiomFunctorComp :: (Functor f, Eq (f c)) => f a -> Fun a b -> Fun b c -> Bool
axiomFunctorComp fx (apply -> fn1) (apply -> fn2) = (fn2 . fn1 <$> fx) == (fmap fn2 . fmap fn1 $ fx)

{-# ANN axiomMonadLeftId "HLint: ignore Monad law, left identity" #-}
axiomMonadLeftId :: (Monad m, Eq (m b)) => m a -> a -> Fun a (m b) -> Bool
axiomMonadLeftId _mw x (apply -> f) = (return x >>= f) == f x

{-# ANN axiomMonadRightId "HLint: ignore Monad law, right identity" #-}
axiomMonadRightId :: (Monad m, Eq (m a)) => m a -> Bool
axiomMonadRightId mx = (mx >>= return) == mx

{-# ANN axiomMonadAssoc "HLint: ignore Functor law" #-}
axiomMonadAssoc :: (Monad m, Eq (m c)) => m a -> Fun a (m b) -> Fun b (m c) -> Bool
axiomMonadAssoc mx (apply -> mf) (apply -> mg) = ((mx >>= mf) >>= mg) == (mx >>= (mf >=> mg))

testMonad :: (Monad m, Arbitrary (m Int), Show (m Int), Eq (m Int)) => m Int -> String -> Test
testMonad _mw typeclass_desc = testGroup ("Monad axioms for " ++ typeclass_desc)
    [ testProperty "Functor identity law" $ typer axiomFunctorId
    , testProperty "Functor composition law" $ typer (axiomFunctorComp :: (Functor m, Eq (m Int)) => m Int -> Fun Int Int -> Fun Int Int -> Bool)
    , testProperty "Monad left identity law" $ typer (axiomMonadLeftId :: (Monad m, Eq (m Int)) => m Int -> Int -> Fun Int (m Int) -> Bool)
    , testProperty "Monad right identity law" $ typer axiomMonadRightId
    , testProperty "Monad associativity law" $ typer (axiomMonadAssoc :: (Monad m, Eq (m Int)) => m Int -> Fun Int (m Int) -> Fun Int (m Int) -> Bool)
  ]
  where typer f mx = f (mx `asTypeOf` _mw)

-- TODO: figure out a quickcheck harness for these.
-- axiomMTId :: (MonadTrans t, Monad m, Monad (t m), Eq (t m a)) => t m a -> Bool
-- axiomMTId tmx = tmx == (tmx >>= lift . return)
--
-- axiomMTDistributive :: (MonadTrans t, Monad m, Monad (t m), Eq (t m b)) => t m a -> m a -> Fun a (m b) -> Bool
-- -- Unfortunately we can't write these laws in terms of a given t m a, because we need a value m a to test these laws,
-- -- and there's no way to access the value m a inside a given value t m a.
-- axiomMTDistributive _wtma ma (apply -> mf) = lift (ma >>= mf) == (lift ma `asTypeOf` _wtma >>= (lift . mf))

newtype TransformerTestMonad a = TransformerTestMonad (Church.F [] a) deriving (Functor, Applicative, Monad)

-- TODO test this test
instance Eq a => Eq (TransformerTestMonad a) where
  (TransformerTestMonad x) == (TransformerTestMonad y) = eqtest (Church.fromF x) (Church.fromF y) where
    eqtest (Free.Pure x0) (Free.Pure y0) = x0 == y0
    eqtest (Free.Free xfs) (Free.Free yfs) = foldr (==) True $ zipWith eqtest xfs yfs
    eqtest _ _ = False

-- arbitraryTTM' :: TransformerTestMonad a
-- arbitraryTTM =
--
-- instance Arbitrary a => Arbitrary (TransformerTestMonad a) where
--   arbitrary = arbitraryTTM' <$> arbitrary

propAmbcat :: Amb Int -> [[Int]] -> Bool
propAmbcat _mw iss = (join . listToAmb $ listToAmb <$> iss) == listToAmb (concat iss) `asTypeOf` _mw

testAmb :: Amb Int -> String -> Test
testAmb _mw typeclass_desc = testGroup ("Tests for " ++ typeclass_desc)
  [ testMonad _mw typeclass_desc
  , testProperty "Join flattens amb" $ propAmbcat . (`asTypeOf` _mw)
  ]

instance Arbitrary a => Arbitrary (Amb a) where
  arbitrary = listToAmb <$> arbitrary
  shrink = (listToAmb <$>) . shrink . runIdentity . ambToList

tests :: IO [Test]
tests = return
  [ testAmb (return 1 :: Amb Int) " ScottAmb"
  ]
