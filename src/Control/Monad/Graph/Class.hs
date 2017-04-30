{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DefaultSignatures #-}

-- Makes for nicer type families where Plus is reused.
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE StrictData #-}

module Control.Monad.Graph.Class where

import Data.Kind (Constraint, type (*))
import Control.Monad
-- import Control.Monad.Indexed
import Data.Type.Equality
import GHC.Base (Any)

class KEffect (f :: k -> * -> *) where
    type Unit f :: k
    type Inv f (i :: k) (j :: k) :: Constraint
    type family Plus f (i :: k) (j :: k) :: k

class Fmappable (f :: k -> * -> *) where
    type family Fmap (f :: k -> * -> *) (i :: k) :: k
    type instance Fmap f i = i

    type family Fconst f (i :: k) :: k
    type instance Fconst f i = Fmap f i

class KEffect f => Applyable (f :: k -> * -> *) where
    type family Apply (f :: k -> * -> *) (i :: k) (j :: k) :: k
    type instance Apply f i j = Plus f i j

    type family Then f (i :: k) (j :: k) :: k
    type instance Then f i j = Apply f (Fconst f i) j

    type family But f (i :: k) (j :: k) :: k
    type instance But f i j = Apply f (Apply f (Unit f) i) j

class KEffect f => Bindable (f :: k -> * -> *) where
    type family Bind (f :: k -> * -> *) (i :: k) (j :: k) :: k
    type instance Bind f i j = Plus f i j

    type family Join (f :: k -> * -> *) (i :: k) (j :: k) :: k
    type instance Join f i j = Bind f i j

class KEffect f => Fallible (f :: k -> * -> *) where
    type family Fail (f :: k -> * -> *) :: k
    type instance Fail f = Unit f

class KEffect f => KPointed (f :: k -> * -> *) where
    kreturn :: a -> f (Unit f) a

class KEffect f => KFunctor (f :: k -> * -> *) where
    kmap :: (a -> b) -> f i a -> f (Fmap f i) b

    {-# INLINABLE kconst #-}
    kconst :: a -> f i b -> f (Fconst f i) a
    default kconst :: (Fconst f i ~ Fmap f i) => a -> f i b -> f (Fconst f i) a
    kconst = kmap . const

class (KFunctor f, KPointed f) => KApplicative (f :: k -> * -> *) where
    kap :: Inv f i j => f i (a -> b) -> f j a -> f (Apply f i j) b

    -- *>
    {-# INLINE kthen #-}
    kthen :: Inv f i j => f i a -> f j b -> f (Then f i j) b
    default kthen :: (Apply f (Fconst f i) j ~ Then f i j, Inv f (Fconst f i) j)
                  => f i a -> f j b -> f (Then f i j) b
    kthen a b = (id `kconst` a) `kap` b

    -- <*
    {-# INLINE kbut #-}
    kbut :: Inv f i j => f i a -> f j b -> f (But f i j) a
    default kbut :: (Apply f (Apply f (Unit f) i) j ~ But f i j, Inv f (Unit f) i, Inv f (Apply f (Unit f) i) j) 
                 => f i a -> f j b -> f (But f i j) a
    kbut a b = kreturn const `kap` a `kap` b

class KApplicative f => KMonad (f :: k -> * -> *) where
    kbind :: Inv f i j => f i a -> (a -> f j b) -> f (Bind f i j) b

    {-# INLINE kjoin #-}
    kjoin :: (Inv f i j) => f i (f j b) -> f (Join f i j) b
    default kjoin :: (Bind f i j ~ Join f i j, Inv f i j) => f i (f j b) -> f (Join f i j) b
    kjoin x = x `kbind` id

class KMonad f => KMonadFail (f :: k -> * -> *) where
    kfail :: String -> f (Fail f) a

-- Wrapping a non-indexed type: 
newtype WrappedM (m :: * -> *) (p :: ()) a where
    WrappedM :: m a -> WrappedM m p a

unM :: WrappedM m p a -> m a
unM (WrappedM m) = m

liftWM :: m a -> WrappedM m '() a
liftWM = WrappedM

instance KEffect (WrappedM m :: () -> * -> *) where
    type Unit (WrappedM m) = '()
    type Inv  (WrappedM m) i j = (i ~ '(), j ~ '())
    type Plus (WrappedM m) i j = '()

instance Fmappable (WrappedM m)
instance Applyable (WrappedM m)
instance Bindable (WrappedM m)

instance Applicative m => KPointed (WrappedM m) where
    kreturn = WrappedM . pure

instance Functor m => KFunctor (WrappedM m) where
    kmap f = WrappedM . fmap f . unM

instance Applicative m => KApplicative (WrappedM m) where
    kap (WrappedM m) (WrappedM k) = WrappedM $ m <*> k
    kthen (WrappedM m) (WrappedM k) = WrappedM $ m *> k
    kbut (WrappedM m) (WrappedM k) = WrappedM $ m <* k

instance Monad m => KMonad (WrappedM m) where
    kbind (WrappedM m) k = WrappedM $ m >>= unM . k

instance Monad m => KMonadFail (WrappedM m) where
    kfail = WrappedM . fail

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

instance Fmappable (IxEff m)
instance Applyable (IxEff m) where
    type But (IxEff m) i j = Plus (IxEff m) i j
instance Bindable (IxEff m)

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
    kthen (IxEff m) (IxEff k) = IxEff $ (m *> k)
    kbut (IxEff m) (IxEff k) = IxEff $ (m <* k)

instance Monad m => KMonad (IxEff m) where
    kbind (IxEff m) k = IxEff $ m >>= unIx . k

instance MonadPlus m => KMonadFail (IxEff m) where
    kfail _ = IxEff $ mzero
