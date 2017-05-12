{-# LANGUAGE
  FlexibleContexts,
  FlexibleInstances,
  MultiParamTypeClasses,
  RankNTypes,
  TypeFamilies
#-}

-- Continuation-passing implementation of Amb.
-- Inspired by https://ifl2014.github.io/submissions/ifl2014_submission_13.pdf.

module Amb where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans
import Data.Foldable (toList)

-- TODO: no reason not to use fundeps here
-- TODO: call it AmbFoldable
class (Monad m, m ~ Target f) => AmbResult f m where
  type Target f :: * -> *
  ambFoldRT :: (t -> r -> r) -> (r -> r) -> r -> f t -> m r

-- TODO test all of these
ambFoldLT' :: (AmbResult f m) => (r -> t -> r) -> (r -> r) -> r -> f t -> m r
ambFoldLT' cf ff z f = ambFoldRT cfl ffl id f <*> return z where
  -- This transforms a list into a series of (strict) updates on the initial value z.
  -- Because foldr is lazy, the value cl is only partially evaluated when it is (tail-recursively)
  -- applied to the strict value (cf zl x).
  cfl x cl zl = cl $! cf zl x
  ffl cl zl = cl $! ff zl

ambFoldR :: (AmbResult f Identity) => (t -> r -> r) -> (r -> r) -> r -> f t -> r
ambFoldR cf ff z ts = runIdentity $ ambFoldRT cf ff z ts

ambFoldL' :: (AmbResult f Identity) => (r -> t -> r) -> (r -> r) -> r -> f t -> r
ambFoldL' cf ff z ts = runIdentity $ ambFoldLT' cf ff z ts

newtype ChurchFoldable t = ChurchFoldable (forall r. (t -> r -> r) -> r -> r)

asFoldable :: (AmbResult a Identity) => a t -> ChurchFoldable t
asFoldable a = ChurchFoldable $ \f z -> runIdentity $ ambFoldRT f id z a

instance Foldable ChurchFoldable where
  foldr fn z (ChurchFoldable f) = f fn z

asMaybeFoldable :: (AmbResult a Identity) => a t -> ChurchFoldable (Maybe t)
asMaybeFoldable a = ChurchFoldable $ \f z -> runIdentity $ ambFoldRT (f . Just) (f Nothing) z a

ambEq :: (AmbResult a Identity, AmbResult b Identity, Eq t) => a t -> b t -> Bool
ambEq as bs = toList (asMaybeFoldable as) == toList (asMaybeFoldable bs)

ambShow :: (AmbResult a Identity, Show t) => String -> a t -> String
ambShow name as = name ++ "[" ++ (show . toList $ asMaybeFoldable as) ++ "]"

-- TODO: foldable
-- TODO invent some invariants for Amb as a transformer
-- Amb laws: join (amb <$> fs) == amb (join fs) where fs is a list of Foldables.
-- When a is a monad transformer, the transformed monad must be sequenced depth-first. TODO: test.
class Monad a => Amb a where
  -- The reason we use [], instead of the more general Foldable, is because amb must be strict in the LHS but not
  -- the RHS of the fold. The [] functor encapsulates this naturally.
  -- TODO: consider using Foldable anyway.
  amb :: [t] -> a t
  afail :: a t

ambzero :: Amb a => a t
ambzero = amb []

ambMaybe :: Amb a => [Maybe t] -> a t
ambMaybe mts = join . amb $ f <$> mts where
  f (Just x) = return x
  f Nothing = afail

ambcat :: Amb a => [a t] -> a t
ambcat = join . amb

-- To support fair choice, an Amb needs one more property.
class Amb a => AmbLogic a where
  -- Pronounced "a-un-cons". Gets the first and rest of an AmbLogic.
  auncons :: a t -> (t -> a t -> a t) -> a t

-- TODO: This is the Church amb, which should be the fastest Amb. Test it.
-- We put m r everywhere so ChurchAmbT never has to use the underlying bind.
-- We need m in the ChurchAmb type so we can make it a monad transformer later.
-- As a bonus, no property of t, m or r is used 'behind' the forall, so any bind/return/&c takes place
-- in the destructor.
newtype ChurchAmbT m t = ChurchAmbT { runChurchAmbT :: forall r. (t -> m r -> m r) -> (m r -> m r) -> m r -> m r }

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
  xs0 >>= fxys = ChurchAmbT $ \c f z0 -> runChurchAmbT xs0 (\x z1 -> runChurchAmbT (fxys x) c f z1) f z0

instance Amb (ChurchAmbT m) where
  amb xs = ChurchAmbT $ \c _ z -> foldr c z xs
  afail = ChurchAmbT $ \_ f z -> f z

instance MonadTrans ChurchAmbT where
  -- The only time we use m as a monad.
  lift mx = ChurchAmbT $ \c _ z -> mx >>= \x -> c x z

instance Monad m => AmbResult (ChurchAmbT m) m where
  type Target (ChurchAmbT m) = m
  ambFoldRT cf ff z xs = runChurchAmbT xs (fmap . cf) (fmap ff) (return z)

instance Eq a => Eq (ChurchAmbT Identity a) where
  (==) = ambEq

instance Show a => Show (ChurchAmbT Identity a) where
  show = ambShow "ChurchAmb"

splitChurch :: Monad m => ChurchAmbT m t -> m (ChurchAmbT m (t, ChurchAmbT m t))
splitChurch a0 = runChurchAmbT a0 c0 f0 z0 where
  -- The goal of c0 and f0 are to turn our original amb, a0, into an amb of type
  -- m (ChurchAmbT m (t, ChurchAmbT m t)).
  -- c0, of course, accepts a t and an m (ChurchAmbT m (t, ChurchAmbT m t)) argument.
  -- Our goal is to convert those into m (ChurchAmbT m (t, ChurchAmbT m t)) arguments.
  c0 x msplitrest = return split where
    -- asplit :: ChurchAmbT' m (t, ChurchAmbT' m t)
    split = ChurchAmbT $ \csplit _ r -> csplit (x, rest) r where
      -- rest :: ChurchAmbT' m t, the rest of our original amb
      -- recall that splitrest is what happens when c0 is folded over the rest of our original amb.
      -- It is of type m (ChurchAmbT' m (t, ChurchAmbT' m t)).
      -- We need to turn it into a ChurchAmbT' m t.
      rest = ChurchAmbT $ \c f r' -> msplitrest >>= let
        -- TODO: figure out what to do with fail continuations!
        unwrap splitrest = runChurchAmbT splitrest unsplit f r'
        unsplit (x1, rest') _ = c x1 $ runChurchAmbT rest' c f r'
        in unwrap
  -- f0 punts, except we must make sure to call the failure continuation.
  f0 msplitrest = combine <$> msplitrest where
    combine splitrest = ChurchAmbT $ \c f r -> runChurchAmbT splitrest c f $ f r
  z0 = return afail

instance Monad m => AmbLogic (ChurchAmbT m) where
  auncons a0 combinef = ChurchAmbT $ \c f z -> let
    -- We want to unwrap a0 into m (ChurchAmbT m (t, ChurchAmbT m t)),
    -- then use combinef, c and z to make it of type m r.
    acombinef (first, rest) _ = runChurchAmbT (combinef first rest) c f z
    runCombine split = runChurchAmbT split acombinef f z
    in splitChurch a0 >>= runCombine

-- ScottAmb is in some respects an asymptotic improvement over ChurchAmb. The reducing function, instead of being a fold,
-- gets a (first, rest) representation of the amb, which yields O(n) access to n elements. But:
-- * All operations are slower, because constructing the tail of a ScottAmb is expensive.
-- * Binds multiply all operations by a constant factor of O(n).
-- As a consequence, prepends are O(n) in the number of prepended elements.
newtype ScottAmbT m t = ScottAmbT {
  runScottAmbT :: forall r. (t -> ScottAmbT m t -> m r) -> (ScottAmbT m t -> m r) -> m r -> m r
}

type ScottAmb = ScottAmbT Identity

instance Functor (ScottAmbT f) where
  -- Need to define fmap because we use it in >>=
  fmap f xs = ScottAmbT $ \cy fy z -> let
    cx x xs1 = cy (f x) $ f <$> xs1
    fx xs1 = fy $ f <$> xs1
    in runScottAmbT xs cx fx z

instance Applicative (ScottAmbT a) where
  pure = return
  (<*>) = ap

instance Monad (ScottAmbT m) where
  return x = amb [x]
  -- TODO: test laziness, asymptotics
  xs >>= fxys = scottJoin $ fxys <$> xs where
    scottJoin xss0 = ScottAmbT $ \c0 f0 z0 -> let
      cxs xs0 xss = let cx x xs1 = c0 x $ combine xs1 xss
                        fx xs1 = f0 $ combine xs1 xss
                        zx = runScottAmbT xss cxs fxs z0
                        combine a as = scottJoin $ ScottAmbT $ \ca _ _ -> ca a as
                    in runScottAmbT xs0 cx fx zx
      fxs xss = f0 $ scottJoin xss
      in runScottAmbT xss0 cxs fxs z0

instance Amb (ScottAmbT m) where
  amb [] = ScottAmbT $ \_ _ z -> z
  amb (x:xs) = ScottAmbT $ \c _ _ -> c x $ amb xs
  afail = ScottAmbT $ \_ f _ -> f ambzero

-- TODO: test auncons
instance AmbLogic (ScottAmbT m) where
  auncons xs0 mf = ScottAmbT $ \cf0 ff0 z0 -> let
    cf x xs = runScottAmbT (mf x xs) cf0 ff0 z0
    ff xs = ff0 $ auncons xs mf
    in runScottAmbT xs0 cf ff z0

instance MonadTrans ScottAmbT where
  -- The only time we use m as a monad.
  lift mx = ScottAmbT $ \c _ _ -> mx >>= \x -> c x ambzero

instance Monad m => AmbResult (ScottAmbT m) m where
  type Target (ScottAmbT m) = m
  ambFoldRT cf ff z xs = runScottAmbT xs cf1 ff1 (return z) where
    cf1 first rest = cf first <$> ambFoldRT cf ff z rest
    ff1 = ambFoldRT cf ff z

instance Eq a => Eq (ScottAmbT Identity a) where
  (==) = ambEq

instance Show a => Show (ScottAmbT Identity a) where
  show = ambShow "ScottAmb"

-- The best of both worlds--most operations are simple folds, but we always pass in a (lazy) tail
-- in case we need it. The efficiency of a Church list with an O(1) tail operation.
newtype ParigotAmbT m t = ParigotAmbT {
  runParigotAmbT :: forall r. (t -> ParigotAmbT m t -> m r -> m r) -> (ParigotAmbT m t -> m r -> m r) -> m r -> m r
}

type ParigotAmb = ParigotAmbT Identity

instance Functor (ParigotAmbT f) where
  -- Need to define fmap because we use it in >>=
  -- Note that though this looks similarly expensive to ScottAmb, in the case where fmap is inlined
  -- in the same context as the amb value xs,
  -- the expensive part is the boxing/unboxing terms `xs1` and `f <$> xs1`.
  -- In most Parigot folds neither are evaluated.
  fmap f xs = ParigotAmbT $ \cy fy z -> let
    cx x xs1 = cy (f x) $ f <$> xs1
    fx xs1 = fy $ f <$> xs1
    in runParigotAmbT xs cx fx z

instance Applicative (ParigotAmbT a) where
  pure = return
  (<*>) = ap

instance Monad (ParigotAmbT m) where
  return x = amb [x]
  -- TODO: test laziness, asymptotics
  -- The expensive boxing/unboxing terms, here `combine`, are not usually evaluated.
  -- However, when not inlined, there is a layer of indirection executed once per element
  -- of the inner monad. Contrast to ChurchAmb where that
  -- layer is only executed once per element of the outer monad.
  xs >>= fxys = parigotJoin $ fxys <$> xs where
    parigotJoin yss0 = ParigotAmbT $ \cy fy z -> let
      cys ys0 yss = let cx y ys = cy y $ combine ys yss
                        fx ys = fy $ combine ys yss
                        combine w ws = parigotJoin $ ParigotAmbT $ \cw _ zw -> cw w ws zw
                      in runParigotAmbT ys0 cy fy
      fys xss = fy $ parigotJoin xss
      in runParigotAmbT yss0 cys fys z

instance Amb (ParigotAmbT m) where
  amb [] = ParigotAmbT $ \_ _ z -> z
  amb (x:xs) = ParigotAmbT $ \c _ z -> c x axs $ runParigotAmbT axs c undefined z where axs = amb xs
  afail = ParigotAmbT $ \_ f z -> f ambzero z

instance AmbLogic (ParigotAmbT m) where
  auncons xs0 mf = ParigotAmbT $ \cf0 ff0 z0 -> let
    cf x xs = runParigotAmbT (mf x xs) cf0 ff0
    ff xs = ff0 $ auncons xs mf
    in runParigotAmbT xs0 cf ff z0

instance MonadTrans ParigotAmbT where
  -- The only time we use m as a monad.
  lift mx = ParigotAmbT $ \c _ z -> mx >>= \x -> c x ambzero z

instance Monad m => AmbResult (ParigotAmbT m) m where
  type Target (ParigotAmbT m) = m
  ambFoldRT cf ff z0 xs0 =
    -- Here we see the advantage of laziness: _xs is never used.
    runParigotAmbT xs0 (\x _xs z -> cf x <$> z) (\_xs z -> ff <$> z) $ return z0

instance Eq a => Eq (ParigotAmbT Identity a) where
  (==) = ambEq

instance Show a => Show (ParigotAmbT Identity a) where
  show = ambShow "ParigotAmb"

newtype FastAmbT m t = FastAmbT {
  runFastAmbT :: forall r. FastAmbT m t ->
                             (t -> FastAmbT m t -> m r -> m r) ->
                             (FastAmbT m t -> m r -> m r) -> m r -> m r
}

type FastAmb = FastAmbT Identity

instance Functor (FastAmbT f) where
  -- Need to define fmap because we use it in >>=
  -- Note that though this looks similarly expensive to ScottAmb, in the case where fmap is inlined
  -- in the same context as the amb value xs,
  -- the expensive part is the boxing/unboxing terms `xs1` and `f <$> xs1`.
  -- In most Parigot folds neither are evaluated.
  fmap = liftM
  -- fmap f xs = ParigotAmbT $ \cy fy z -> let
  --   cx x xs1 = cy (f x) $ f <$> xs1
  --   fx xs1 = fy $ f <$> xs1
  --   in runParigotAmbT xs cx fx z

instance Applicative (FastAmbT a) where
  pure = return
  (<*>) = ap

instance Monad (FastAmbT m) where
  return x = amb [x]
  -- The crucial improvement here is that the inner runFastAmbT is executed directly on the continuations
  -- cy and fy.
  xs0 >>= fxys = FastAmbT $ \rest cy fy z0 -> let
    makerest xrest = ambcat [xrest >>= fxys, rest]
    cx x xrest = runFastAmbT (fxys x) (makerest xrest) cy fy
    fx = fy . makerest
    in runFastAmbT xs0 undefined cx fx z0

instance Amb (FastAmbT m) where
  amb [] = FastAmbT $ \_ _ _ z -> z
  amb (x:xs) = FastAmbT $ \rest c _ z -> c x (ambcat [axs, rest]) $ runFastAmbT axs rest c undefined z where
    axs = amb xs
  afail = FastAmbT $ \rest _ f z -> f rest z

instance AmbLogic (FastAmbT m) where
  auncons xs0 mf = FastAmbT $ \rest cf0 ff0 z0 -> let
    cf x xs = runFastAmbT (mf x xs) rest cf0 ff0
    -- TODO: test this, is it right?
    ff xs = ff0 $ auncons xs mf
    in runFastAmbT xs0 undefined cf ff z0

instance MonadTrans FastAmbT where
  -- The only time we use m as a monad.
  lift mx = FastAmbT $ \rest c _ z -> mx >>= \x -> c x rest z

instance Monad m => AmbResult (FastAmbT m) m where
  type Target (FastAmbT m) = m
  ambFoldRT cf ff z0 xs0 =
    -- Here we see the advantage of laziness: the _xs args are never used.
    runFastAmbT xs0 ambzero (\x _xs z -> cf x <$> z) (\_xs z -> ff <$> z) $ return z0

instance Eq a => Eq (FastAmbT Identity a) where
  (==) = ambEq

instance Show a => Show (FastAmbT Identity a) where
  show = ambShow "FastAmb"
