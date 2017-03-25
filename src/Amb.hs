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

class Monad a => Amb a where
  -- The reason we use [], instead of the more general Foldable, is because amb must be strict in the LHS but not
  -- the RHS of the fold. The [] functor encapsulates this naturally.
  -- TODO: that's not really what we want. We want a more general "ChurchScott" amb, which can be folded either way.
  -- It can opt to use the Church fold or a destructive Scott encoding. In particular, we need destructo-Scott
  -- for continuations to work.
  amb :: [t] -> a t
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

-- TODO: This is the Church amb, which should be the fastest Amb. Test it.
-- We put m r everywhere so ChurchAmbT never has to use the underlying bind.
newtype ChurchAmbT m t = ChurchAmbT { runAmbT :: forall r. (t -> m r -> m r) -> (m r -> m r) -> m r -> m r }

-- TODO: how about Maybe a?
-- ambToList :: (Applicative m) => AmbT m a -> m [a]
-- ambToList mas = runAmb mas (\a mas1 -> (\as -> a:as) <$> ambToList mas1) (\mas1 -> ambToList mas1) (pure [])

type ChurchAmb = ChurchAmbT Identity

instance Functor (ChurchAmbT f) where
  fmap = liftM

instance Applicative (ChurchAmbT a) where
  pure = return
  (<*>) = ap

instance Monad (ChurchAmbT m) where
  return x = amb [x]
  -- note that f is called for failures in both the lhs and the rhs.
  -- Also, because both the outer and inner runAmbs are right-associative, we have proper right-associativity
  -- which yields the laziness and O(n) asymptotics we need.
  -- TODO: test both above assertions.
  -- TODO: test the underlying binding is correct. It should be. See 'ListT done right' for test ideas.
  xs >>= fxys = ChurchAmbT $ \c f z0 -> runAmbT xs (\x z1 -> runAmbT (fxys x) c f z1) f z0

instance Amb (ChurchAmbT m) where
  amb xs = ChurchAmbT $ \c _ z -> foldr c z xs
  fail = ChurchAmbT $ \_ f z -> f z

instance MonadTrans ChurchAmbT where
  -- Interestingly, this is the only time we use m as a monad.
  lift mx = ChurchAmbT $ \c _ z -> mx >>= \x -> c x z

ambToList :: Monad m => ChurchAmbT m t -> m [t]
ambToList a = runAmbT a (fmap . (:)) id (return [])

instance Eq a => Eq (ChurchAmbT Identity a) where
  as == bs = runIdentity (ambToList as) == runIdentity (ambToList bs)

instance Show a => Show (ChurchAmbT Identity a) where
  show a = "Amb [" ++ show (ambToList a) ++ "]"
