{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- Makes for nicer type families where Plus is reused.
{-# LANGUAGE UndecidableInstances #-}

module Control.Monad.Graph.Class where

import Data.Kind (Constraint, type (*))
import Control.Monad.Indexed
import Data.Type.Equality
import GHC.Base (Any)

class KEffect (f :: k -> * -> *) where
    type Unit f :: k
    type Inv f (i :: k) (j :: k) :: Constraint
    type family Plus f (i :: k) (j :: k) :: k

type family Fmap (f :: k -> * -> *) (i :: k) :: k
type family Ap (f :: k -> * -> *) (i :: k) (j :: k) :: k
type family Bind (f :: k -> * -> *) (i :: k) (j :: k) :: k

class KEffect f => KPointed (f :: k -> * -> *) where
    kreturn :: a -> f (Unit f) a

class KEffect f => KFunctor (f :: k -> * -> *) where
    kmap :: (a -> b) -> f i a -> f (Fmap f i) b

class (KFunctor f, KPointed f) => KApplicative (f :: k -> * -> *) where
    kap :: Inv f i j => f i (a -> b) -> f j a -> f (Ap f i j) b

class KApplicative f => KMonad (f :: k -> * -> *) where
    kbind :: Inv f i j => f i a -> (a -> f j b) -> f (Bind f i j) b

-- Wrapping a non-indexed type: 

newtype WrappedM (m :: * -> *) (p :: ()) a where
    WrappedM :: forall (m :: * -> *) (p :: ()) a. m a -> WrappedM m p a

unM :: WrappedM m p a -> m a
unM (WrappedM m) = m

instance KEffect (WrappedM m :: () -> * -> *) where
    type Unit (WrappedM m) = '()
    type Inv  (WrappedM m) i j = (i ~ '(), j ~ '())
    type Plus (WrappedM m) i j = '()

type instance Fmap (WrappedM m) i = i
type instance Ap (WrappedM m) i j = Plus (WrappedM m) i j
type instance Bind (WrappedM m) i j = Plus (WrappedM m) i j 

instance Applicative m => KPointed (WrappedM m) where
    kreturn = WrappedM . pure

instance Functor m => KFunctor (WrappedM m) where
    kmap f = WrappedM . fmap f . unM

instance Applicative m => KApplicative (WrappedM m) where
    kap (WrappedM m) (WrappedM k) = WrappedM $ m <*> k

instance Monad m => KMonad (WrappedM m) where
    kbind (WrappedM m) k = WrappedM $ m >>= (\a -> (case k a of WrappedM k' -> k'))

-- Wrapping an indexed type with two phantom parameters, parameters form a category.
newtype IxEff (m :: * -> *) (p :: CatArr i j) (a :: *) = IxEff { unIx :: m a }

data CatArr a b where
    CatId :: CatArr a b
    CArrow  :: a -> b -> CatArr a b

instance KEffect (IxEff m :: CatArr i j -> * -> *) where
    type Unit (IxEff m) = 'CatId
    type Inv  (IxEff m) ('CArrow a b) ('CArrow c d) = b ~~ c
    type Plus (IxEff m) ('CatId     ) ('CatId     ) = 'CatId 
    type Plus (IxEff m) ('CArrow a b) ('CArrow c d) = 'CArrow a d
    type Plus (IxEff m) ('CArrow a b) ('CatId     ) = 'CArrow a b
    type Plus (IxEff m) ('CatId     ) ('CArrow c d) = 'CArrow c d

type instance Fmap (IxEff m) i = i
type instance Ap (IxEff m) i j = Plus (IxEff m) i j
type instance Bind (IxEff m) i j = Plus (IxEff m) i j 

type family FstArr (p :: CatArr i j) where
    FstArr ('CArrow a b) = a
    FstArr ('CatId :: CatArr i j) = (Any :: i)

type family SndArr (p :: CatArr i j) where
    SndArr ('CArrow a b) = b
    SndArr ('CatId :: CatArr i j) = (Any :: j)

instance Applicative m => KPointed (IxEff m) where
    kreturn = IxEff . pure

instance Functor m => KFunctor (IxEff m) where
    kmap f = IxEff . fmap f . unIx

instance Applicative m => KApplicative (IxEff m) where
    kap (IxEff m) (IxEff k) = IxEff $ m <*> k

instance Monad m => KMonad (IxEff m) where
    kbind (IxEff m) k = IxEff $ m >>= (\a -> (case k a of IxEff k' -> k'))

-- Wrapped IxMonad from Control.Monad.Indexed

newtype WrappedIx (m :: k -> k -> * -> *) (p :: CatArr k k) a = WrappedIx { unWix :: m (FstArr p) (SndArr p) a }

instance KEffect (WrappedIx m) where
    type Unit (WrappedIx m) = 'CatId
    type Inv  (WrappedIx m) i j = (SndArr i ~~ FstArr j)
    type Plus (WrappedIx m) i j  = 'CArrow (FstArr i) (SndArr j)  

type instance Fmap (WrappedIx m) i = i
type instance Ap (WrappedIx m) i j = Plus (WrappedIx m) i j
type instance Bind (WrappedIx m) i j = Plus (WrappedIx m) i j 

instance IxPointed m => KPointed (WrappedIx m) where
    kreturn = WrappedIx . ireturn

instance IxFunctor m => KFunctor (WrappedIx m) where
    kmap f = WrappedIx . imap f . unWix

instance IxApplicative m => KApplicative (WrappedIx m) where
    kap (WrappedIx m) (WrappedIx k) = WrappedIx $ m `iap` k

instance IxMonad m => KMonad (WrappedIx m) where
    kbind (WrappedIx m) k = WrappedIx $ (\a -> (case k a of WrappedIx k' -> k')) `ibind` m
