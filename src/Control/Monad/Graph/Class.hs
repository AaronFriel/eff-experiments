{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}

{-# LANGUAGE KindSignatures #-}

module Control.Monad.Graph.Class where

import GHC.Exts (Constraint)
import Control.Monad.Indexed

import Data.Kind (type (*))
import Data.Type.Equality

-- Not yet totally satisfied with this.
-- Better than associated types right now, though.
type family PurishCxt (i :: k) = (r :: Constraint)
type family Fmapish (i :: k) = (r :: k)
type family ApCxt (i :: ki) (j :: kj) (r :: kr) = (cxt :: Constraint)
type family BindCxt (i :: ki) (j :: kj) (r :: kr) = (cxt :: Constraint)

class Apish k where
    type Ap (i :: k) (j :: k)

-- type ApIx ('Ix i j') ('Ix j' k) = Ix i k

-- type family ApIx a b where
--     ApIx (Ix i j') (Ix j' k) = Ix i k


-- type family Ap (i :: k) (j :: k) = (r :: k)

-- An alternative would be to make GFunctor, et al, require `f` to be a data family
-- with these operations defined? That might be better.

class GFunctor (f :: k -> * -> *) where
    gmap :: (a -> b) -> f i a -> f (Fmapish i) b

class GFunctor f => GPointed (f :: k -> * -> *) where
    greturn :: PurishCxt i => a -> f i a

class GPointed f => GApplicative (f :: k -> * -> *) where
    gap :: ApCxt i j (r :: k) => f i (a -> b) -> f j a -> f r b

class GApplicative m => GMonad (m :: k -> * -> *) where
    -- type Bind (a :: k) (b :: k) :: (c :: k)
    gbind :: BindCxt i j (r :: k) => (a -> m j b) -> m i a -> m r b

newtype WrappedMonad m (p :: ()) a = WrappedMonad { unwrapM :: m a }

type instance PurishCxt () = ()
type instance Fmapish () = ()
type instance ApCxt () () () = ()
type instance BindCxt () () () = ()

deriving instance Show (m a) => Show (WrappedMonad m '() a)
deriving instance Eq (m a) => Eq (WrappedMonad m '() a)
deriving instance Ord (m a) => Ord (WrappedMonad m '() a)

instance Functor f => GFunctor (WrappedMonad f) where
    gmap f (WrappedMonad m) = WrappedMonad $ fmap f m

instance Applicative f => GPointed (WrappedMonad f) where
    greturn a = WrappedMonad (pure a)

instance Applicative f => GApplicative (WrappedMonad f) where
    gap (WrappedMonad u) (WrappedMonad v) = WrappedMonad (u <*> v)

instance Monad m => GMonad (WrappedMonad m) where
    k `gbind` (WrappedMonad m) = WrappedMonad (m >>= (\(WrappedMonad m') -> m') . k)

data Ix a b = Ix a b

-- data Ix a b where
--     Ix :: a -> b -> Ix a b 

newtype Wix m (i :: ()) (j :: ()) a = Wix { unWix :: m a }

type instance PurishCxt (a :: Ix i j) = (i ~~ j)
type instance Fmapish (a :: (Ix i j)) = (a :: Ix i j)
type instance ApCxt (a :: Ix i j) (b :: Ix j' k) (r :: Ix i' k') = (j ~~ j', i ~~ i', k ~~ k')
type instance BindCxt (a :: Ix i j) (b :: Ix j' k) (r :: Ix i' k') = (j ~~ j', i ~~ i', k ~~ k')


instance Functor m => IxFunctor (Wix m) where
    imap f (Wix m) = Wix (fmap f m)
instance Applicative m => IxPointed (Wix m) where
    ireturn a = Wix (pure a)
instance Applicative m => IxApplicative (Wix m) where
    iap (Wix m) (Wix k) = Wix (m <*> k)
instance Monad m => IxMonad (Wix m) where
    ibind k (Wix m) = Wix $ (\a -> case k a of Wix k' -> k') =<< m

newtype WrappedIx m (p :: Ix i j) a = WrappedIx { unwrapIx :: m i j a }

instance IxFunctor f => GFunctor (WrappedIx f) where
    gmap f (WrappedIx m) = WrappedIx (imap f m)

instance IxPointed f => GPointed (WrappedIx f) where
    greturn a = WrappedIx $ ireturn a

instance IxApplicative f => GApplicative (WrappedIx f) where
    gap (WrappedIx u) (WrappedIx v) = WrappedIx (iap u v)

instance IxMonad m => GMonad (WrappedIx m) where
    k `gbind` (WrappedIx m) = WrappedIx $ (\a -> (case k a of WrappedIx k' -> k')) `ibind` m
