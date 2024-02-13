{-# LANGUAGE
ConstraintKinds
, DefaultSignatures
, FlexibleInstances
, FunctionalDependencies
, ImpredicativeTypes
, MultiParamTypeClasses
, PolyKinds
, QuantifiedConstraints
, RankNTypes
, ScopedTypeVariables
, TypeApplications
, TypeOperators
, UndecidableInstances
, UndecidableSuperClasses
#-}

module Control.Constrained.Transformer
  ( Unconstrained
  , (:&&)
  , Forgetful
  , CFunctor (cmap)
  , CTrans (creturn)
  , CFoldable (cram), cjoin, cbind, cextract
  , CFree, cduplicate, cextend, toCFree
  , C1Homomorphism (trans)
  , C1Functor (hoist)
  , C1Trans (lift)
  , C1Foldable (crush), squash, embed, lower
  , C1Free, copulate, expand, toC1Free
  ) where

import Control.Comonad
import qualified Control.Comonad.Trans.Class as Trans
import Control.Monad.Codensity
import Control.Monad.Cont
import qualified Control.Monad.Morph as Morph
import Control.Monad.State (MonadState(..))
import qualified Control.Monad.Trans.Class as Trans
import qualified Control.Monad.Trans.State.Lazy as State
import qualified Control.Monad.Trans.State.Strict as State'
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Kind

class Unconstrained t
instance Unconstrained t

class (c t, d t) => (c :&& d) t
instance (c t, d t) => (c :&& d) t

type Forgetful d c = forall x. d x => c x :: Constraint

class (forall a. c a => d (f a))
  => CFunctor c d f | f -> c, f -> d where
    -- prop> cmap id = id
    -- prop> cmap (g . f) = cmap g . cmap f
    cmap :: (c a, c b) => (a -> b) -> f a -> f b
    default cmap :: Functor f => (a -> b) -> f a -> f b
    cmap = fmap
instance CFunctor Unconstrained Monoid []
instance CFunctor Ord (Ord :&& Monoid) Set where cmap = Set.map

class CFunctor c d f
  => CTrans c d f where
    -- prop> cmap f . creturn = creturn . f
    creturn :: c a => a -> f a
    default creturn :: Applicative f => a -> f a
    creturn = pure
instance CTrans Unconstrained Monoid []
instance CTrans Ord (Ord :&& Monoid) Set where creturn = Set.singleton

class CFunctor c d f
  => CFoldable c d f where
    -- prop> cram f . single = f
    -- prop> cextract = cram id
    cram :: (c a, d b) => (a -> b) -> f a -> b
instance CFoldable Unconstrained Monoid [] where cram = foldMap
instance CFoldable Ord (Ord :&& Monoid) Set where cram = foldMap

cbind :: (CFoldable c d f, c a, c b) => (a -> f b) -> f a -> f b
cbind = cram

cextract :: (Forgetful d c, CFoldable c d f, d a) => f a -> a
cextract = cram id

cjoin :: (Forgetful d c, CFoldable c d f, c a) => f (f a) -> f a
cjoin = cextract

-- prop> cram f . creturn = f
type CFree c d free =
  ( CTrans c d free
  , CFoldable c d free
  , Forgetful d c
  ) :: Constraint

cduplicate :: (CFree c d f, c a) => f a -> f (f a)
cduplicate = cmap creturn

cextend :: (CFree c d f, c a, c b) => (f a -> b) -> f a -> f b
cextend f a = cmap f (cduplicate a)

toCFree
  :: (CFoldable c d f, CFree c d free, c a)
  => f a -> free a
toCFree = cram creturn

class C1Homomorphism c t | t -> c where
  trans
    :: c f
    => (forall x. f x -> f x)
    -> t f a -> t f a
instance C1Homomorphism Monad (State'.StateT s) where trans = hoist
instance C1Homomorphism Monad (State.StateT s) where trans = hoist
instance C1Homomorphism Monad Codensity where
  trans f (Codensity k) = Codensity (f . k)
instance C1Homomorphism MonadCont (ContT r) where
  trans f (ContT k) = ContT (f . k)

class (C1Homomorphism c t, forall f. c f => d (t f))
  => C1Functor c d t | t -> d where
    -- prop> trans = hoist
    -- prop> hoist id = id
    -- prop> hoist (g . f) = hoist g . hoist f
    hoist
      :: (c f, c g)
      => (forall x. f x -> g x)
      -> t f a -> t g a
    default hoist
      :: (Morph.MFunctor t, Monad f)
      => (forall x. f x -> g x)
      -> t f a -> t g a
    hoist = Morph.hoist
instance C1Functor Monad (MonadState s) (State'.StateT s)
instance C1Functor Monad (MonadState s) (State.StateT s)

class C1Homomorphism c t => C1Trans c t where
  -- prop> trans f . lift = lift . f
  lift :: c f => f a -> t f a
  default lift :: (Trans.MonadTrans t, Monad f) => f a -> t f a
  lift = Trans.lift
instance C1Trans Monad (State'.StateT s)
instance C1Trans Monad (State.StateT s)
instance C1Trans Monad Codensity
instance C1Trans MonadCont (ContT r)

class
  ( C1Homomorphism c t
  , forall f. c f => d (t f)
  ) => C1Foldable c d t | t -> d where
    crush
      :: (c f, d g)
      => (forall x. f x -> g x)
      -> t f a -> g a
    default crush
      :: (Trans.ComonadTrans t, Comonad f)
      => (forall x. f x -> g x)
      -> t f a -> g a
    crush f t = f (Trans.lower t)
instance C1Foldable Monad (MonadState s) (State'.StateT s) where
  crush f st = do
    s <- get
    (a, s') <- State'.runStateT (hoist f st) s
    put s'
    return a
instance C1Foldable Monad (MonadState s) (State.StateT s) where
  crush f st = do
    s <- get
    (a, s') <- State.runStateT (hoist f st) s
    put s'
    return a
instance C1Foldable Monad Monad Codensity where
  crush f (Codensity k) = f (k return)

embed
  :: (C1Foldable c d t, c f, c g)
  => (forall x. f x -> t g x)
  -> t f a -> t g a
embed = crush

-- prop> lower = crush id
-- prop> lower . trans f = f . lower
lower
  :: (Forgetful d c, C1Foldable c d t, d f)
  => t f a -> f a
lower = crush id

-- prop> squash = lower
squash
  :: (Forgetful d c, C1Foldable c d t, c f)
  => t (t f) a -> t f a
squash = lower

-- prop> crush f . lift = f
type C1Free c d free =
  ( C1Functor c d free
  , C1Trans c free
  , C1Foldable c d free
  , Forgetful d c
  ) :: Constraint

copulate :: (C1Free c d t, c f) => t f a -> t (t f) a
copulate = hoist lift

expand
  :: (C1Free c d t, c f, c g)
  => (forall x. t f x -> g x)
  -> t f a -> t g a
expand f a = hoist f (copulate a)

toC1Free
  :: forall t free c d f a. (C1Foldable c d t, C1Free c d free, c f)
  => t f a -> free f a
toC1Free = crush lift
