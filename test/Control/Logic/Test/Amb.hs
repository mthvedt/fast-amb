{-# LANGUAGE
  FlexibleContexts,
  FlexibleInstances,
  GeneralizedNewtypeDeriving,
  TypeFamilies,
  ViewPatterns
#-}

module Control.Logic.Test.Amb (ambTests) where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans
import Control.Monad.Writer.Lazy
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
axiomFunctorId _fw fx = (id <$> fx) == fx

{-# ANN axiomFunctorComp "HLint: ignore Functor law" #-}
axiomFunctorComp :: (Functor f, Eq (f Int)) => f Int -> f Int -> Fun Int Int -> Fun Int Int -> Bool
axiomFunctorComp _fw fx (apply -> fn1) (apply -> fn2) = (fn2 . fn1 <$> fx) == (fmap fn2 . fmap fn1 $ fx)

{-# ANN axiomMonadLeftId "HLint: ignore Monad law, left identity" #-}
axiomMonadLeftId :: (Monad m, Eq (m Int)) => m Int -> Int -> Fun Int (m Int) -> Bool
axiomMonadLeftId _mw x (apply -> f) = (return x >>= f) == f x

{-# ANN axiomMonadRightId "HLint: ignore Monad law, right identity" #-}
axiomMonadRightId :: (Monad m, Eq (m Int)) => m Int -> m Int -> Bool
axiomMonadRightId _mw mx = (mx >>= return) == mx

{-# ANN axiomMonadAssoc "HLint: ignore Functor law" #-}
axiomMonadAssoc :: (Monad m, Eq (m Int)) => m Int -> m Int -> Fun Int (m Int) -> Fun Int (m Int) -> Bool
axiomMonadAssoc _mw mx (apply -> mf) (apply -> mg) = ((mx >>= mf) >>= mg) == (mx >>= (mf >=> mg))

testMonad :: (Monad m, Arbitrary (m Int), Show (m Int), Eq (m Int)) => m Int -> String -> Test
testMonad _mw typeclass_desc = testGroup ("Monad axioms for " ++ typeclass_desc)
    [ testProperty "Functor identity law" $ axiomFunctorId _mw
    , testProperty "Functor composition law" $ axiomFunctorComp _mw
    , testProperty "Monad left identity law" $ axiomMonadLeftId _mw
    , testProperty "Monad right identity law" $ axiomMonadRightId _mw
    , testProperty "Monad associativity law" $ axiomMonadAssoc _mw
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

-- newtype TransformerTestMonad a = TransformerTestMonad (Church.F [] a) deriving (Functor, Applicative, Monad)
--
-- -- TODO test this test
-- instance Eq a => Eq (TransformerTestMonad a) where
--   (TransformerTestMonad x) == (TransformerTestMonad y) = eqtest (Church.fromF x) (Church.fromF y) where
--     eqtest (Free.Pure x0) (Free.Pure y0) = x0 == y0
--     eqtest (Free.Free xfs) (Free.Free yfs) = foldr (==) True $ zipWith eqtest xfs yfs
--     eqtest _ _ = False

-- -- An Arbitrary implementation of a free monad.
-- instance (Arbitrary t) => Arbitrary (Church.F [] t) where
--   arbitrary = oneof [
--     -- One in two chance of getting either a return or a bind.
--     return <$> arbitrary,
--     do
--       -- For the bind, create a list of Church.F's, the children scaled down by some random size factor
--       -- (but always strictly less than the current size factor).
--       scaleFactor <- choose (0 :: Double, 1 :: Double)
--       unwrapped <- scale (\x -> floor (fromIntegral x * scaleFactor)) arbitrary
--       return $ Free.wrap unwrapped
--    ]
--   shrink f = snd $ Church.runF f rd bd where
--     -- Each destructor returns a pair of (unshrunken F, list of shrunken Fs). The list is usually discarded
--     -- except at the top level.
--     -- return destructor: return [], terminating the shrink
--     rd x = (return x, [])
--     -- bind destructor: we're getting a list of (unshrunken F, [shrunken F]) tuples. We discard the shrunken list.
--     bd tuples = (unshrunken, shrunkens) where
--       unshrunken = Free.wrap $ fst <$> tuples
--       shrunkens = Free.wrap <$> shrink (fst <$> tuples)

-- arbitraryTTM' :: TransformerTestMonad a
-- arbitraryTTM =
--
-- instance Arbitrary a => Arbitrary (TransformerTestMonad a) where
--   arbitrary = arbitraryTTM' <$> arbitrary

-- Tests that joining an Amb of Ambs is the same as running amb on joined lists.
propAmbcat :: (Amb a, Arbitrary (a Int), Eq (a Int), Show (a Int)) => a Int -> [[Int]] -> Bool
propAmbcat _mw iss = (join . amb $ amb <$> iss) == amb (concat iss) `asTypeOf` _mw

testAmb :: (Amb a, Arbitrary (a Int), Eq (a Int), Show (a Int)) => a Int -> String -> Test
testAmb _mw typeclass_desc = testGroup ("Tests for " ++ typeclass_desc)
  [ testMonad _mw typeclass_desc
  , testProperty "Join flattens amb" $ propAmbcat . (`asTypeOf` _mw)
  ]

ambArbitrary :: (Amb a, Arbitrary t) => Gen (a t)
ambArbitrary = ambMaybe <$> arbitrary

-- TODO: work on AmbResult class
ambShrink :: (Amb a, AmbFold a, Unlift a ~ Identity, Arbitrary t) => a t -> [a t]
ambShrink = (amb <$>) . shrink . toList . asFoldable

-- (Amb a, Arbitrary t) => Arbitrary (a t) is undecidable.
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

-- Helper to test the associativity and laziness of a monad transformer.
-- In these tests, we have a Writer monoid. The test is that Amb is properly depth-first in evaluation order,
-- obeys the monad laws, and does not strictly evaluate the monad for lazy folds.
-- TODO
data AmbTransTest a = AmbTransTest {
  -- The (Amb result, Int) pairs that we plan to evaluate. Might be smaller than the full Amb.
  count :: Int,
  pairs :: [(Int, Maybe Int)],
  m :: a (Writer [Int]) Int
}

ambTransTest :: (MonadTrans a, Amb (a (Writer [Int]))) => Int -> [(Int, Maybe Int)] -> AmbTransTest a
ambTransTest count pairs = let count = min count $ length pairs
                               ats = (\(w, mt) -> lift (tell [w]) >> maybe afail return mt) <$> pairs
                           in AmbTransTest {
                             count = count,
                             pairs = pairs,
                             m = join . amb $ ats
                           }

arbAmbTransTest :: (MonadTrans a, Amb (a (Writer [Int]))) => Gen (AmbTransTest a)
arbAmbTransTest = ambTransTest <$> arbitrary <*> arbitrary

shrinkAmbTransTest :: (MonadTrans a, Amb (a (Writer [Int]))) => AmbTransTest a -> [AmbTransTest a]
shrinkAmbTransTest ts = join [shrink1 ts, shrink2 ts] where
  shrink1 AmbTransTest { count = c0, pairs = p0 } = (`ambTransTest` p0) <$> shrink c0
  shrink2 AmbTransTest { count = c, pairs = p0 } = ambTransTest c <$> shrink p0

ambTests :: Test
ambTests = testGroup "Control.Logic.Amb"
  [ testAmb (return 1 :: ChurchAmb Int) "ChurchAmb"
  , testAmb (return 1 :: ScottAmb Int) "ScottAmb"
  , testAmb (return 1 :: ParigotAmb Int) "ParigotAmb"
  , testAmb (return 1 :: FastAmb Int) "FastAmb"
  ]
