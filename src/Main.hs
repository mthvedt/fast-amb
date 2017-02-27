{-# LANGUAGE
  GeneralizedNewtypeDeriving,
  MultiParamTypeClasses,
  RankNTypes,
  ScopedTypeVariables,
  TypeFamilies
#-}

module Main where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.State

import Data.HashMap.Lazy (HashMap)
import qualified Data.Vector as BoxedVectors
import qualified Data.Vector.Unboxed as UnboxedVectors

type BoxedVector = BoxedVectors.Vector
type UnboxedVectors = UnboxedVectors.Vector

-- We might extend this later
-- This is the Scott encoding: a List represented as a manipulator of continuations.
-- For a nonempty list, we are provided a continuation that takes a head element and the rest of the list.
-- For the empty list, we are provided a 'failure continuation'; the second argument r.
-- The manipulator function is called the 'constructor'.
newtype Amb m a = Amb (forall r. (a -> Amb m a -> m r) -> m r -> m r)

runAmb :: Amb m a -> (a -> Amb m a -> m r) -> m r -> m r
runAmb (Amb cxr) = cxr

ambnil :: Amb m a
ambnil = Amb $ \_ i -> i

ambcons :: a -> Amb m a -> Amb m a
ambcons x axs = Amb $ \c _ -> c x axs

ambone :: a -> Amb m a
ambone x = ambcons x ambnil

-- ambcons :: (Monad m) => m a -> Amb m a -> Amb m a
-- Given a continuation a -> Amb m a -> m r, we call it with the given mx and axs.
-- ambcons mx axs = Amb $ \c _ -> mx >>= \x -> c x axs

amblist :: [x] -> Amb m x
amblist = foldr ambcons (Amb (\ _ i -> i))

ambcat :: Amb m (Amb m a) -> Amb m a
-- We want to create a continuation Amb m a -> Amb m (Amb m a) -> m r
-- that uses the continuation c :: a -> Amb m a -> m r.
ambcat axaxs = Amb $ \c i -> runAmb axaxs
  -- We want to create a continuation Amb m a -> Amb m (Amb m a) -> m r
  -- that uses the continuation c :: a -> Amb m a -> m r.
  -- In this continuation, axs0 is the first element of the amb of ambs, and axss the rest.
  -- We want to run the continuation, c, on the first element of axs0, and ambcat the rest of axs0 with axss.
  -- If axs0 is empty, we recurse to axss.
  (\axs0 axss -> runAmb axs0
      (\x xs0 -> c x $ ambcat $ ambcons xs0 axss)
      (runAmb (ambcat axss) c i))
  i

instance (Functor f) => Functor (Amb f) where
  fmap fab (Amb cxra) = Amb $ \cb mb -> cxra (\a as -> cb (fab a) (fmap fab as)) mb

instance (Applicative a) => Applicative (Amb a) where
  pure = ambone
  afs <*> axs = ambcat $ fmap (`fmap` axs) afs

instance (Monad m) => Monad (Amb m) where
  return = pure
  as >>= famb = ambcat $ fmap famb as

-- data AmbListImpl m a = AmbNil | AmbCons a (AmbList m a)
-- newtype AmbList m a = AmbList (m (AmbListImpl m a))
--
-- instance (Functor f) => Functor (AmbImpl f) where
--   fmap f (AmbImpl m) = AmbImpl $ fmap f2 m where
--     f2 AmbNil = AmbNil
--     f2 (AmbCons x xs) = AmbCons (f x) $ fmap f xs
--
-- instance (Applicative a) => Applicative (AmbImpl a) where
--   pure x = AmbImpl . pure $ AmbCons x (AmbImpl $ pure AmbNil)
--   (AmbImpl f) <*> (AmbImpl x) = innerap f x where
--     innerap AmbNil _ = AmbNil
--     innerap _ AmbNil = AmbNil
--     innerap (AmbCons f fs) xs = AmbCons ()
--
-- instance (Monad m) => Monad (AmbImpl m) where
--   return x = AmbImpl . return $ AmbCons x (AmbImpl $ return AmbNil)

-- type AmbResult m where
  -- runAmb :: m a -> m (Maybe (AmbResult m, m a))

-- class FactQuery q where
--   type Result q
--   query :: (FactSystem m) => q -> m () -> Amb m (Result q)

newtype Entity = Entity Int

newtype Tuple = UnboxedVector Int

newtype FactKey = TupleKey String

class BaseFact t where
  basekey :: t -> FactKey

data TupleFact = Fact {
  factkey :: FactKey,
  tuple :: Tuple
}

-- class FactTuple t where
--   tuplekey :: t -> TupleKey

data FactSubindexEntry = NoIndex | DirectIndex | SubIndex

data FactIndex = FactIndex {
  subindices :: BoxedVector FactSubindexEntry
}

{-
What characterizes a fact?
Queries and facts should be their own class, representable in a FactSystem.
-}
class FactQuery f where
  type FactType f
  type QueryInfo f
  queryFact :: f -> QueryInfo f -> FactType f

class Monad m => FactReader m where
  -- queryFact :: (FactQuery f) => f -> m r

class FactReader m => FactWriter m where
  putFact :: (BaseFact t) => t -> m ()

data FactBase = FactBase {
  -- bases :: HashMap BaseFact FactIndex
}

-- doQueryFact :: FactBase -> (r, FactBase)
--
-- doPutFact :: (BaseFact t) => FactBase -> t -> FactBase

-- impl

data FactSystemImpl = FactSystemImpl {
  persistentsystem :: FactBase,
  tempsystem :: ()
}

newtype FactSystem m a = FactSystem (StateT FactSystemImpl m a) deriving (Functor, Applicative, Monad)



-- newtype Fact f = Fact f

-- class FactCont m f where
  -- runFact :: m a -> Fact f -> a

main :: IO ()
main = putStrLn "Hello, Haskell!"
