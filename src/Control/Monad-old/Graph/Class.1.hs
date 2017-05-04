{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Control.Monad.Graph.Class where

import GHC.Exts (Constraint)
import Control.Monad.Indexed

class GFunctor (f :: k -> * -> *) where
    type Mapish (i :: k) :: k
    gmap :: (a -> b) -> f i a -> f (Mapish i) b

class GFunctor f => GPointed i (f :: k -> * -> *) where
    type EmptyishC (i :: k) :: Constraint
    greturn :: EmptyishC i => a -> f i a

class GPointed j f => GApplicative j (f :: k -> * -> *) where
    type ApishC (i :: k) (j :: k) :: Constraint
    type Apish (i :: k) (j :: k) :: k
    gap :: ApishC (i :: k) (j :: k) => f i (a -> b) -> f j a -> f (Apish i j) b

class GApplicative j m => GMonad j (m :: k -> * -> *) where
    type BindishC (i :: k) (j :: k) :: Constraint
    type Bindish (i :: k) (j :: k) :: k
    gbind :: BindishC (i :: k) j => (a -> m j b) -> m i a -> m (Bindish i j) b

data WrappedMonad m i a where
    WrappedMonad :: m a -> WrappedMonad m () a

instance Functor f => GFunctor (WrappedMonad f) where
    type Mapish () = ()
    gmap f (WrappedMonad m) = WrappedMonad $ fmap f m

instance Applicative f => GPointed () (WrappedMonad f) where
    type EmptyishC () = ()
    greturn a = WrappedMonad (pure a)

instance Applicative f => GApplicative () (WrappedMonad f) where
    type Apish () () = ()
    type ApishC () () = ()
    gap (WrappedMonad u) (WrappedMonad v) = WrappedMonad (u <*> v)

instance Monad m => GMonad () (WrappedMonad m) where
    type Bindish () () = ()
    type BindishC () () = ()
    k `gbind` (WrappedMonad m) = WrappedMonad (m >>= (\(WrappedMonad m') -> m') . k)

data Ix a b = Ix a b

data WrappedIx m p a where
    WrappedIx :: m i j a -> WrappedIx m (Ix i j) a

instance IxFunctor f => GFunctor (WrappedIx f) where
    type Mapish (Ix i j) = Ix i j
    gmap f (WrappedIx m) = WrappedIx (imap f m)

instance IxPointed f => GPointed (Ix a b) (WrappedIx f) where
    type EmptyishC (Ix i j) = (i ~ j)
    greturn a = WrappedIx $ ireturn a

instance IxApplicative f => GApplicative (Ix a b) (WrappedIx f) where
    type ApishC (Ix i j1) (Ix j2 k) = (j1 ~ j2)
    type Apish  (Ix i j1) (Ix j2 k) = Ix i k
    gap (WrappedIx u) (WrappedIx v) = WrappedIx (iap u v)

instance IxMonad m => GMonad (Ix a b) (WrappedIx m) where
    type BindishC (Ix i j1) (Ix j2 k) = (j1 ~ j2)
    type Bindish  (Ix i j1) (Ix j2 k) = Ix i k
    k `gbind` (WrappedIx m) = WrappedIx $ (\a -> (case k a of WrappedIx k' -> k')) `ibind` m
