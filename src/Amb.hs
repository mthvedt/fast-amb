{-# LANGUAGE
  FlexibleContexts,
  FlexibleInstances,
  RankNTypes,
  TypeFamilies
#-}

module Amb where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.State

import Data.Hashable
import Data.HashMap.Lazy (HashMap, alter, empty)
import Data.Int
import qualified Data.Vector as BoxedVectors
import qualified Data.Vector.Unboxed as UnboxedVectors

type BoxedVector = BoxedVectors.Vector
type UnboxedVector = UnboxedVectors.Vector

-- begin free monad experiment

-- Church-encoded free monad, accepting two continuations.
-- The first continuation deals with a pure 'boxed' value.
-- The second collapses the boxed f's inside the free monad.
-- newtype Free r f a = Free ((a -> r) -> (f r -> r) -> r)
--
-- runFree :: Free r f a -> (a -> r) -> (f r -> r) -> r
-- runFree (Free cxr) = cxr
--
-- instance Functor (Free r f) where
--   fmap = liftM
--
-- instance Applicative (Free r f) where
--   pure = return
--   (<*>) = ap
--
-- instance Monad (Free r f) where
--   return x = Free $ \jc _ -> jc x
--   (Free cxr) >>= bindf = Free $ \jc fc -> cxr (\x -> runFree (bindf x) jc fc) fc
--
-- instance MonadTrans (Free r) where
--    lift m = Free (\jc fc -> fc (jc <$> m))

-- end free monad experiment

-- This is the Scott encoding: a List represented as a manipulator of continuations.
-- For a nonempty list, we are provided a continuation that takes a head element and the rest of the list.
-- For the empty list, we are provided a 'failure continuation'; the second argument r.
-- The manipulator function is called the 'constructor'.
--
-- We don't bother making this a class since we will always use the Scott encoding,
-- which is the most general encoding we can use.
newtype AmbT m a = AmbT (forall r. (a -> AmbT m a -> m r) -> m r -> m r)

type Amb a = AmbT Identity a

listToAmb :: [a] -> AmbT m a
listToAmb = foldr ambcons ambnil

runAmb :: AmbT m a -> (a -> AmbT m a -> m r) -> m r -> m r
runAmb (AmbT cxr) = cxr

ambToList :: (Applicative m) => AmbT m a -> m [a]
ambToList mas = runAmb mas (\a mas1 -> (\as -> a:as) <$> ambToList mas1) (pure [])

instance Functor (AmbT f) where
  fmap fab (AmbT cxra) = AmbT $ \cb mb -> cxra (\a as -> cb (fab a) (fab <$> as)) mb

instance Applicative (AmbT a) where
  pure = return
  (<*>) = ap

instance Monad (AmbT m) where
  return x = listToAmb [x]
  as >>= famb = ambcat $ fmap famb as

instance MonadTrans AmbT where
  -- Interestingly, this is the only time we use m as a monad.
  lift m = AmbT $ \c i -> m >>= \x -> c x ambnil

ambnil :: AmbT m a
ambnil = AmbT $ \_ i -> i

ambcons :: a -> AmbT m a -> AmbT m a
ambcons x axs = AmbT $ \c _ -> c x axs
-- Given an amb-continuation c and an amb-of-amb axss,
-- creates a continuation that accepts a value a and concatenates the input amb to axss.
ambcatHelperInner :: (a -> AmbT m a -> m r) -> AmbT m (AmbT m a) -> a -> AmbT m a -> m r
ambcatHelperInner c axss x xs0 = c x $ ambcat $ ambcons xs0 axss
-- ambcatHelperInner c axss x xs0 = c x $ Amb $ \c i -> runAmb (ambcons xs0 axss) (ambcatHelper c i) i
-- ambcatHelperInner c axss x xs0 = c x $ Amb $ \c i -> ambcatHelper c i xs0 axss

-- We want to create a continuation Amb m a -> Amb m (Amb m a) -> m r
-- that uses the continuation c :: a -> Amb m a -> m r and the failure value m r.
ambcatHelper :: (a -> AmbT m a -> m r) -> m r -> AmbT m a -> AmbT m (AmbT m a) -> m r
ambcatHelper c i asx0 axss = runAmb asx0 (ambcatHelperInner c axss) (runAmb (ambcat axss) c i)

ambcat :: AmbT m (AmbT m a) -> AmbT m a
ambcat axaxs = AmbT $ \c i -> runAmb axaxs (ambcatHelper c i) i

instance Eq a => Eq (AmbT Identity a) where
  as == bs = runIdentity (ambToList as) == runIdentity (ambToList bs)

instance Show a => Show (AmbT Identity a) where
  show a = "Amb [" ++ show (ambToList a) ++ "]"

-- class FactQuery q where
--   type Result q
--   query :: (FactSystem m) => q -> m () -> Amb m (Result q)

-- A query is a function that returns a FactReader, Amb monad.

-- newtype Tuple = UnboxedVector Int
--
-- newtype FactKey = TupleKey String
--
-- class BaseFact t where
--   basekey :: t -> FactKey
--
-- data TupleFact = Fact {
--   factkey :: FactKey,
--   tuple :: Tuple
-- }
--
-- -- class FactTuple t where
-- --   tuplekey :: t -> TupleKey
--
-- data FactSubindexEntry = NoIndex | DirectIndex | SubIndex
--
-- newtype FactIndex = FactIndex {
--   subindices :: HashMap Entity (Maybe FactIndex)
-- }
--
-- newFactIndex :: FactIndex
-- newFactIndex = FactIndex empty
--
-- doPutFact :: [Entity] -> FactIndex -> FactIndex
-- doPutFact [] idx = idx
-- doPutFact (e:es) idx = FactIndex $ alter alterf e $ subindices idx where
--   alterf subs = Just . Just $ maybe newFactIndex (doPutFact es) $ join subs -- TODO: Just Nothing should error instead
--
-- newtype Entity = Entity Int32 deriving (Eq, Hashable, Ord)
--
-- class FactReader m where
--   type PartialResult m
--   queryFact :: Entity -> m (PartialResult m)
--   refineFact :: PartialResult m -> Entity -> m (PartialResult m)
--   allFacts :: (Amb PartialResult m -> AmbT m [Entity]
--
-- class FactWriter m where
--   putFact :: [Entity] -> m ()
--
-- newtype FactBase = FactBase {
--   baseIndex :: FactIndex
-- }
--
-- newtype FactState a = FactState (AmbT (State FactBase) a) deriving (Functor, Applicative, Monad)
--
-- instance Amb FactState where
--   amb = FactState . amb
--   ambcat (FactState f) = FactState . ambcat $ (\(FactState f) -> f) <$> f
--
-- instance FactWriter FactState where
--   putFact f = FactState . lift $ do
--     base <- get
--     put . FactBase . doPutFact f $ baseIndex base
--
-- instance FactReader FactState where
--   type PartialResult FactState =

-- instance FactReader FactState where
--   queryFact ::

-- newtype Fact f = Fact f

-- class FactCont m f where
  -- runFact :: m a -> Fact f -> a
