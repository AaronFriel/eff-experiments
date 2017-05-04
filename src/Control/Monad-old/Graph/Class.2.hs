{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeApplications #-}

module Control.Monad.Graph.Class where

import GHC.Exts (Constraint)
import Control.Monad.Indexed

-- import Data.Constraint
import Data.Type.Equality
import Data.Kind (type (*))

-- fooIx :: (j ~ WrappedMonad m i a) :- (i ~ ())
-- fooIx = Sub Dict

type family Purish (i :: k) :: Constraint

class G (f :: * -> * -> *) where
    type P f :: k

class GFunctor (f :: * -> * -> *) where
    type Mapish f (i :: k) :: k
    gmap :: (a -> b) -> f i a -> f (Mapish f i) b

class GPointed (f :: * -> * -> *) where
    type PurishC f (i :: k) :: Constraint
    greturn :: PurishC f i => a -> f i a

class GPointed f => GApplicative (f :: * -> * -> *) where
    type Apish f (i :: k) (j :: k) (r :: k) :: Constraint
    gap :: Apish f i j r => f i (a -> b) -> f j a -> f r b

-- class GApplicative m => GMonad (m :: k -> * -> *) where
--     type BindishC m (i :: k) (j :: k) :: Constraint
--     type Bindish m (i :: k) (j :: k) :: k
--     gbind :: BindishC m (i :: k) j => (a -> m j b) -> m i a -> m (Bindish m i j) b

-- data WrappedMonad m (i :: ()) a = WrappedMonad (m a)

-- instance Functor f => GFunctor (WrappedMonad f) where
--     type Mapish (WrappedMonad f) () = ()
--     gmap f (WrappedMonad m) = WrappedMonad $ fmap f m

-- instance Applicative f => GPointed (WrappedMonad f) () where
--     -- type PurishC (WrappedMonad f) () = ()
--     greturn a = WrappedMonad (pure a)

-- instance Applicative f => GApplicative (WrappedMonad f) () where
--     type Apish (WrappedMonad f) () () = ()
--     type ApishC (WrappedMonad f) () () = ()
--     gap (WrappedMonad u) (WrappedMonad v) = WrappedMonad (u <*> v)

-- instance Monad m => GMonad (WrappedMonad m) () where
--     type Bindish (WrappedMonad m) () () = ()
--     type BindishC (WrappedMonad m) () () = ()
--     k `gbind` (WrappedMonad m) = WrappedMonad (m >>= (\(WrappedMonad m') -> m') . k)

data Ix k1 k2 (a :: k1) (b :: k2) = Ix

-- type FstIx (i :: Ix k1 k2 a b) = a
type FstIx (i :: (k1, k2, a, b)) = a
type SndIx (i :: (k1, k2, a, b)) = b
-- type family SndIx (i :: Ix k1 k2) where
--     SndIx ('Ix a b) = b

data TrivialIx (i :: k1) (j :: k2) a where
    TrivialIx :: a -> TrivialIx i j a 

newtype WrappedIx m p a = WrappedIx { unwrapIx :: m (FstIx p) (SndIx p) a }
-- data WrappedIx m p a = forall i j. (p ~ (Ix i j)) => WrappedIx (m i j a)

-- class PurishC 

-- type instance Purish (Ix a b) = (FstIx (Ix a b) ~ SndIx (Ix a b))
-- data WrappedIx m p a where
--     WrappedIx :: m i j a -> WrappedIx m (Ix i j) a

instance IxFunctor f => GFunctor (WrappedIx f) where
    gmap f (WrappedIx m) = WrappedIx $ imap f m 

type EmptyishIx (p :: Ix k1 k2 i j) = (k1 ~~ k2, i ~~ j)
type ApishCIx (a :: Ix ki kj1 i j1) (b :: Ix kj2 kk j2 k) = (kj1 ~~ kj2, j1 ~~ j2)
type ApishRIx (a :: Ix ki kj1 i j1) (b :: Ix kj2 kk j2 k) (c :: Ix kri krj ri rj) 
    = (kj1 ~~ kj2, j1 ~~ j2, kri ~~ ki, ri ~~ i, krj ~~ kk, rj ~~ k)
-- type ApishIx (a :: Ix ki kj1 i j1) (b :: Ix kj2 kk j2 k) = (c :: Ix ki kk i k)

instance IxPointed f => GPointed (WrappedIx f) where
    type PurishC (WrappedIx f) p = EmptyishIx p
    greturn a = WrappedIx $ ireturn a

instance IxFunctor (TrivialIx) where
    imap a = undefined
instance IxPointed (TrivialIx) where
    ireturn a = undefined
instance IxApplicative (TrivialIx) where
    iap a b = undefined

instance IxApplicative f => GApplicative (WrappedIx f) where
    type Apish (WrappedIx f) i j r = ApishRIx i j r
    -- type Apish (WrappedIx f)  p1 p2 = ApishIx p1 p2
    gap (WrappedIx u) (WrappedIx v) = WrappedIx (iap u v)

tf :: TrivialIx String Int (a -> b -> (a, b))
tf = undefined

ta :: TrivialIx Int String (Int, Int)
ta = undefined

tb :: TrivialIx Float Double (Double, Double)
tb = undefined


-- instance IxMonad m => GMonad (WrappedIx m) (Ix a b) where
--     type BindishC (WrappedIx m) (Ix i j1) (Ix j2 k) = (j1 ~ j2)
--     type Bindish (WrappedIx m)  (Ix i j1) (Ix j2 k) = Ix i k
--     k `gbind` (WrappedIx m) = WrappedIx $ (\a -> (case k a of WrappedIx k' -> k')) `ibind` m
