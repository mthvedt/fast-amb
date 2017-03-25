{-# LANGUAGE
  FlexibleContexts,
  FlexibleInstances,
  MultiParamTypeClasses,
  RankNTypes
#-}

module Amb where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import qualified Control.Monad.State as HState

import Data.Hashable
import qualified Data.HashMap.Lazy as Maps
import Data.Int
import qualified Data.Vector.Unboxed as Vectors

type Map = Maps.HashMap
type Vector = Vectors.Vector

-- class Suspension s where
--   type Input s
--
-- data Suspended e m t = Suspended {
--   suspension :: e,
--   resume :: Input e -> m t
-- }

class Monad m => AmbInterpreter m where
  interpret :: t -> t -> m t
  interpretFail :: t -> m t

class Monad a => AmbSeq a where
  -- The reason we use [], instead of the more general Foldable, is because amb must be strict in the LHS but not
  -- the RHS of the fold. The [] functor encapsulates this naturally.
  amb :: [t] -> a t

class AmbSeq a => Amb a where
  fail :: a ()

-- TODO: newtype ChurchList

-- class Amb m => AmbState m where
--   type State m
--   get :: m (State m)
--   put :: State m -> m ()
-- TODO: do we need the m?
-- TODO: is it faster if we don't use forall?

-- TODO: do we need the m?
-- TODO: is it faster if we don't use forall?
-- This is a slightly more complicated continuation-passing encoding of a Scott list with failure.
-- It's designed to combine the strictness and efficiency of foldl with the tail-recursion and laziness of foldr.
-- Alternately, combining the simplicity of a Foldable/Church list with the efficiency of a Scott list.
-- TODO: test the above assertions.
-- TODO: this doesn't work great. Does it make sense to use a State monad? How do we do state here?
-- newtype AmbT m t = AmbT { runAmbT :: forall r. (m r -> t -> AmbT m t -> m r) -> (m r -> AmbT m t -> m r) -> m r -> m r }
newtype AmbT m t = AmbT { runAmbT :: forall r. (t -> m r -> m r) -> (m r -> m r) -> m r -> m r }

type AmbM t = AmbT Identity t

-- TODO: how about Maybe a?
-- ambToList :: (Applicative m) => AmbT m a -> m [a]
-- ambToList mas = runAmb mas (\a mas1 -> (\as -> a:as) <$> ambToList mas1) (\mas1 -> ambToList mas1) (pure [])

instance Functor (AmbT f) where
  fmap = liftM

instance Applicative (AmbT a) where
  pure = return
  (<*>) = ap

instance Monad (AmbT m) where
  return x = amb [x]
  -- note that f is called for failures in both the lhs and the rhs.
  -- Also, because both the outer and inner runAmbs are right-associative, we have proper right-associativity
  -- which yields the laziness and O(n) asymptotics we need.
  -- TODO: test both above assertions.
  xs >>= fxys = AmbT $ \c f z0 -> runAmbT xs (\x z1 -> runAmbT (fxys x) c f z1) f z0

instance AmbSeq (AmbT m) where
  -- TODO: something more efficient
  amb ts = AmbT $ \c _ z -> foldr c z ts

instance Amb (AmbT m) where
  fail = AmbT $ \_ f z -> f z

instance MonadTrans AmbT where
  -- Interestingly, this is the only time we use m as a monad.
  lift mx = AmbT $ \c _ z -> mx >>= \x -> c x z

ambToList :: Monad m => AmbT m t -> m [t]
ambToList a = runAmbT a mcons id (return []) where
  mcons x xs = (x:) <$> xs

instance Eq a => Eq (AmbT Identity a) where
  as == bs = runIdentity (ambToList as) == runIdentity (ambToList bs)

instance Show a => Show (AmbT Identity a) where
  show a = "Amb [" ++ show (ambToList a) ++ "]"
