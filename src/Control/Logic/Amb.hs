{-# LANGUAGE
  FlexibleContexts,
  FlexibleInstances,
  FunctionalDependencies,
  MultiParamTypeClasses,
  RankNTypes,
  TypeFamilies
#-}

-- Continuation-passing implementation of Amb.
-- Inspired by https://ifl2014.github.io/submissions/ifl2014_submission_13.pdf.

module Control.Logic.Amb where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans
import Data.Foldable (toList)

class (Amb a, Monad m) => AmbFold m a | a -> m where
  ambFoldRT :: (t -> r -> m r) -> (r -> m r) -> r -> a t -> m r

-- TODO test all of these
ambFoldLT' :: AmbFold m a => (r -> t -> m r) -> (r -> m r) -> r -> a t -> m r
ambFoldLT' c0 f0 z xs = unwrap $ ambFoldRT mc mf id xs where
  -- This transforms a list into a series of (strict) updates on the initial value z.
  -- We note that the function cont, of type m r -> m r, is finitely bounded because foldr is lazy.
  -- So a foldr is turned into a strict foldl in finite space.
  -- c :: Monad m => t -> (m r -> m r) -> m r -> m r
  c x cont macc = cont $! macc >>= \acc -> c0 acc x
  -- mc :: Monad m => t -> (m r -> m r) -> m (m r -> m r)
  mc x cont = return $ c x cont
  -- f :: Monad m => (m r -> m r) -> m r -> m r
  f cont macc = cont $! macc >>= f0
  -- mf :: Monad m => (m r -> m r) -> m (m r -> m r)
  mf = return . f
  -- unwrap :: Monad m => r -> m (m r -> m r) -> m r
  unwrap zl = join $ zl <*> return (return z)

ambFoldR :: AmbFold Identity a => (t -> r -> r) -> (r -> r) -> r -> a t -> r
ambFoldR c f z a = runIdentity $ ambFoldRT (\t r -> return $ c t r) (return . f) z a

ambFoldL' :: AmbFold Identity a => (r -> t -> r) -> (r -> r) -> r -> a t -> r
ambFoldL' c f z a = runIdentity $ ambFoldLT' (\r t -> return $ c r t) (return . f) z a

newtype ChurchFoldable t = ChurchFoldable (forall r. (t -> r -> r) -> r -> r)

instance Foldable ChurchFoldable where
  foldr c z (ChurchFoldable f) = f c z

asFoldable :: AmbFold Identity a => a t -> ChurchFoldable t
asFoldable a = ChurchFoldable $ \f z -> runIdentity $ let
  mf t r = return $ f t r
  in ambFoldRT mf return z a

asMaybeFoldable :: AmbFold Identity a => a t -> ChurchFoldable (Maybe t)
asMaybeFoldable a = ChurchFoldable $ \f z -> runIdentity $ let
  mfjust t r = return $ f (Just t) r
  mfnothing r = return $ f Nothing r
  in ambFoldRT mfjust mfnothing z a

toMaybeListM :: AmbFold m a => a t -> m [Maybe t]
toMaybeListM = ambFoldRT (\x xs -> return $ Just x:xs) (\xs -> return $ Nothing:xs) []

ambEq :: (AmbFold Identity a, AmbFold Identity b, Eq t) => a t -> b t -> Bool
ambEq as bs = toList (asMaybeFoldable as) == toList (asMaybeFoldable bs)

ambShow :: (AmbFold Identity a, Show t) => String -> a t -> String
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

-- An AmbLogic is an Amb that supports uncons: getting a first and a rest.
-- Minimal complete definition: ambuncons | ambpeek.
class Amb a => AmbLogic a where
  ambpeek :: a t -> (t -> a t -> a r) -> a r
  ambpeek a f =  ambuncons a >>= uncurry f
  ambuncons :: a t -> a (t, a t)
  ambuncons a = ambpeek a $ curry return

-- -- TODO: testme
-- -- TODO: class or func?
-- class (Monad (MorphSrc f), Monad (MorphDest f)) => MonadMorph f where
--   type MorphSrc f :: * -> *
--   type MorphDest f :: * -> *
--   morphM :: f -> (MorphSrc f) x -> (MorphDest f) x
--
-- newtype MorphMBox m n = MorphMBox (forall x. m x -> n x)
--
-- instance (Monad m, Monad n) => MonadMorph (MorphMBox m n) where
--   type MorphSrc (MorphMBox m n) = m
--   type MorphDest (MorphMBox m n) = n
--   morphM (MorphMBox f) = f
--
-- asMorphM :: (forall x. m x -> n x) -> MorphMBox m n
-- asMorphM = MorphMBox

-- -- TODO use MFunctor instead
-- -- A MonadFunc is a functor on the category of monads. A {function, natural transformation, morphism of monads}
-- -- can be lifted into the MonadFunc.
-- -- fmapM must obey the functor laws:
-- -- fmapM id == id
-- -- fmapM (f . g) == fmap f . fmap g
-- -- and lift must be a map of functors (alternatively, lift itself is a natural endotransformation on monads)
-- -- obeying fmapM t . lift = lift . t
-- -- From this we can deduce that when f is a {function, natural transformation, monad morphism},
-- -- `fmapT f` is one also.
-- -- TODO: testme
-- class MonadTrans t => MonadFunc t where
--   fmapT :: (Monad m, Monad n) => (forall x. m x -> n x) -> t m v -> t n v

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

instance MonadTrans ChurchAmbT where
  -- The only time we use m as a monad.
  lift mx = ChurchAmbT $ \c _ z -> mx >>= \x -> c x z

instance Amb (ChurchAmbT m) where
  amb xs = ChurchAmbT $ \c _ z -> foldr c z xs
  afail = ChurchAmbT $ \_ f z -> f z

-- instance MonadFunc ChurchAmbT where
--   fmapT n a = ChurchAmbT $ \c0 f0 z0 -> let
--     -- We run the original amb a with a return type m (n r),
--     -- then use join . nat to strip away the extra m.
--     -- c0 :: a -> n r -> n r. We need to make something of type a -> m (n r) -> m (n r)
--     c x mnz = c0 x <$> mnz
--     f mnz = f0 <$> mnz
--     z = return z0
--     in join . n $ runChurchAmbT a c f z

instance Monad m => AmbFold m (ChurchAmbT m) where
  ambFoldRT cf ff z xs = runChurchAmbT xs (\t mr -> mr >>= cf t) (>>= ff) (return z)

instance Monad m => AmbLogic (ChurchAmbT m) where
  ambuncons a0 = join . lift $ runChurchAmbT a0 c0 f0 z0 where
    -- The goal of c0 and f0 are to turn our original amb, a0, into an amb of type
    -- m (ChurchAmbT m (t, ChurchAmbT m t)), and then join it.
    -- c0, accepts a `t` and an `m (ChurchAmbT m (t, ChurchAmbT m t))` argument.
    -- Our goal is to convert those into `m (ChurchAmbT m (t, ChurchAmbT m t))`.
    c0 x msplitrest = return split where
      -- asplit :: ChurchAmbT m (t, ChurchAmbT m t)
      split = ChurchAmbT $ \csplit _ z -> csplit (x, rest) z where
        -- rest :: ChurchAmbT' m t, the rest of our original amb
        -- recall that splitrest is what happens when c0 is folded over the rest of our original amb.
        -- It is of type m (ChurchAmbT m (t, ChurchAmbT m t)).
        -- We need to turn it into a ChurchAmbT m t.
        rest = ChurchAmbT $ \c f z' -> msplitrest >>= let
          unwrap splitrest = runChurchAmbT splitrest unsplit f z'
          unsplit (x1, rest') _ = c x1 $ runChurchAmbT rest' c f z'
          in unwrap
    -- f0 punts, except we must make sure to call the failure continuation.
    f0 msplitrest = combine <$> msplitrest where
      combine splitrest = ChurchAmbT $ \c f z -> runChurchAmbT splitrest c f $ f z
    z0 = return afail

instance Eq a => Eq (ChurchAmbT Identity a) where
  (==) = ambEq

instance Show a => Show (ChurchAmbT Identity a) where
  show = ambShow "ChurchAmb"

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

instance MonadTrans ScottAmbT where
  -- The only time we use m as a monad.
  lift mx = ScottAmbT $ \c _ _ -> mx >>= \x -> c x ambzero

instance Amb (ScottAmbT m) where
  amb [] = ScottAmbT $ \_ _ z -> z
  amb (x:xs) = ScottAmbT $ \c _ _ -> c x $ amb xs
  afail = ScottAmbT $ \_ f _ -> f ambzero

-- TODO: test ambpeek
instance AmbLogic (ScottAmbT m) where
  ambpeek xs0 mf = ScottAmbT $ \cf0 ff0 z0 -> let
    cf x xs = runScottAmbT (mf x xs) cf0 ff0 z0
    ff xs = ff0 $ ambpeek xs mf
    in runScottAmbT xs0 cf ff z0

instance Monad m => AmbFold m (ScottAmbT m) where
  ambFoldRT cf ff z xs = runScottAmbT xs cf1 ff1 (return z) where
    cf1 first rest = ambFoldRT cf ff z rest >>= cf first
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

instance MonadTrans ParigotAmbT where
  -- The only time we use m as a monad.
  lift mx = ParigotAmbT $ \c _ z -> mx >>= \x -> c x ambzero z

instance Amb (ParigotAmbT m) where
  amb [] = ParigotAmbT $ \_ _ z -> z
  amb (x:xs) = ParigotAmbT $ \c _ z -> c x axs $ runParigotAmbT axs c undefined z where axs = amb xs
  afail = ParigotAmbT $ \_ f z -> f ambzero z

instance AmbLogic (ParigotAmbT m) where
  ambpeek xs0 mf = ParigotAmbT $ \cf0 ff0 z0 -> let
    cf x xs = runParigotAmbT (mf x xs) cf0 ff0
    ff xs = ff0 $ ambpeek xs mf
    in runParigotAmbT xs0 cf ff z0

instance Monad m => AmbFold m (ParigotAmbT m) where
  ambFoldRT cf ff z0 xs0 =
    -- Here we see the advantage of laziness: _xs is never used.
    runParigotAmbT xs0 (\x _xs z -> z >>= cf x) (\_xs z -> z >>= ff) $ return z0

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
  fmap = liftM

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

instance MonadTrans FastAmbT where
  -- The only time we use m as a monad.
  lift mx = FastAmbT $ \rest c _ z -> mx >>= \x -> c x rest z

instance Amb (FastAmbT m) where
  amb [] = FastAmbT $ \_ _ _ z -> z
  amb (x:xs) = FastAmbT $ \rest c _ z -> c x (ambcat [axs, rest]) $ runFastAmbT axs rest c undefined z where
    axs = amb xs
  afail = FastAmbT $ \rest _ f z -> f rest z

instance AmbLogic (FastAmbT m) where
  ambpeek xs0 mf = FastAmbT $ \rest cf0 ff0 z0 -> let
    cf x xs = runFastAmbT (mf x xs) rest cf0 ff0
    -- TODO: test this, is it right?
    ff xs = ff0 $ ambpeek xs mf
    in runFastAmbT xs0 undefined cf ff z0

instance Monad m => AmbFold m (FastAmbT m) where
  ambFoldRT cf ff z0 xs0 =
    -- Here we see the advantage of laziness: the _xs args are never used.
    runFastAmbT xs0 ambzero (\x _xs z -> z >>= cf x) (\_xs z -> z >>= ff) (return z0)

instance Eq a => Eq (FastAmbT Identity a) where
  (==) = ambEq

instance Show a => Show (FastAmbT Identity a) where
  show = ambShow "FastAmb"
