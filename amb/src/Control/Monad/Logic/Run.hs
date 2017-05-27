{-# LANGUAGE
  ConstraintKinds,
  FlexibleContexts,
  FunctionalDependencies,
  MultiParamTypeClasses
#-}

module Control.Monad.Logic.Run where

import Control.Monad.Identity
import Data.Foldable (toList)

import Control.Monad.Logic.Class

class (Monad m, MonadLogic l) => RunLogicT m l | l -> m where
  runLogicT :: (t -> m r -> m r) -> m r -> l t -> m r

type RunLogic = RunLogicT Identity

-- TODO test all of these
runLogicLT' :: RunLogicT m l => (m r -> t -> m r) -> m r -> l t -> m r
{-# INLINABLE runLogicLT' #-}
-- Inline/specialize based on choice of c0
runLogicLT' c0 = go where
  -- This transforms a list into a series of (strict) updates on the initial value z.
  -- We note that the function cont, of type m r -> m r, is finitely bounded because foldr is lazy.
  -- So a foldr is turned into a strict foldl in finite space.
  -- c :: t -> (m r -> m r) -> m r -> m r
  go mz = unwrap . runLogicT mc (return id) where
    -- unwrap :: m (m r -> m r) -> m r
    unwrap zl = join $ (\f -> f mz) <$> zl
  c x cont acc = cont $! c0 acc x
  -- mc :: t -> m (m r -> m r) -> m (m r -> m r)
  mc x mcont = c x <$> mcont

runLogicM :: RunLogicT m l => (t -> r -> m r) -> r -> l t -> m r
{-# INLINABLE runLogicM #-}
runLogicM c0 = runLogicT c . return where
  c x mr = mr >>= c0 x

runLogicLM' :: RunLogicT m l => (r -> t -> m r) -> r -> l t -> m r
{-# INLINABLE runLogicLM' #-}
runLogicLM' c0 = runLogicLT' c . return where
  c mr x = mr >>= \r -> c0 r x

-- TODO: is A things appropriate? or maybe Traversable?
runLogicLift :: RunLogicT m l => (t -> r -> r) -> r -> l t -> m r
{-# INLINABLE runLogicLift #-}
runLogicLift c = runLogicM $ \t r -> return $ c t r

runLogicLiftL' :: RunLogicT m l => (r -> t -> r) -> r -> l t -> m r
{-# INLINABLE runLogicLiftL' #-}
runLogicLiftL' c = runLogicLM' $ \t r -> return $ c t r

runLogic :: RunLogic l => (t -> r -> r) -> r -> l t -> r
{-# INLINABLE runLogic #-}
-- Inline/specialize based on choice of c
runLogic c = go where go z = runIdentity . runLogicLift c z

runLogicL' :: RunLogic l => (r -> t -> r) -> r -> l t -> r
{-# INLINABLE runLogicL' #-}
-- Inline/specialize based on choice of c
runLogicL' c = go where go z = runIdentity . runLogicLiftL' c z

logicToList :: RunLogicT m l => l t -> m [t]
logicToList = runLogicLift (:) []

logicEq :: (RunLogicT m a, RunLogicT m b, Eq t) => a t -> b t -> m Bool
logicEq as bs = (==) <$> logicToList as <*> logicToList bs

logicShow :: (RunLogicT m l, Show t) => l t -> m String
logicShow as = show <$> logicToList as
