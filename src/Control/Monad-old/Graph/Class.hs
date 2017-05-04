{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- Makes for nicer type families where Combine is reused.
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE StrictData #-}

{-# LANGUAGE Safe #-}

module Control.Monad.Graph.Class where

import Data.Kind (Constraint, type (*))
import Control.Monad (MonadPlus, mzero)
import Data.Type.Equality (type (~~))

class KEffect (f :: k -> * -> *) where
    type Unit f :: k
    type Inv f (i :: k) (j :: k) :: Constraint
    type family Combine f (i :: k) (j :: k) :: k

class KEffect f => KPointed (f :: k -> * -> *) where
    kreturn :: a -> f (Unit f) a

class KEffect f => KFunctor (f :: k -> * -> *) where
    type family Fmap f (i :: k) :: k
    type instance Fmap f i = i

    type family Fconst f (i :: k) :: k
    type instance Fconst f i = Fmap f i

    kmap :: (a -> b) -> f i a -> f (Fmap f i) b

    {-# INLINABLE kconst #-}
    kconst :: a -> f i b -> f (Fconst f i) a
    default kconst :: (Fconst f i ~ Fmap f i) => a -> f i b -> f (Fconst f i) a
    kconst = kmap . const

class (KFunctor f, KPointed f) => KApplicative (f :: k -> * -> *) where
    type family Apply f (i :: k) (j :: k) :: k
    type instance Apply f i j = Combine f i j

    type family Then f (i :: k) (j :: k) :: k
    type instance Then f i j = Apply f (Fconst f i) j

    type family But f (i :: k) (j :: k) :: k
    type instance But f i j = Apply f (Apply f (Unit f) i) j

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
    type family Bind f (i :: k) (j :: k) :: k
    type instance Bind f i j = Combine f i j

    type family Join f (i :: k) (j :: k) :: k
    type instance Join f i j = Bind f i j

    kbind :: Inv f i j => f i a -> (a -> f j b) -> f (Bind f i j) b

    {-# INLINE kjoin #-}
    kjoin :: (Inv f i j) => f i (f j b) -> f (Join f i j) b
    default kjoin :: (Bind f i j ~ Join f i j, Inv f i j) => f i (f j b) -> f (Join f i j) b
    kjoin x = x `kbind` id

class KMonad f => KMonadFail (f :: k -> * -> *) where
    type family Fail f :: k
    type instance Fail f = Unit f

    kfail :: String -> f (Fail f) a

    default kfail :: (KMonadZero f, Unit f ~ Fail f) => String -> f (Fail f) a
    kfail _ = kzero

class KMonad f => KMonadZero (f :: k -> * -> *) where
    kzero :: f (Unit f) a

-- Should satisfy left distribution, use the operator <+>
class KMonad f => KMonadPlus (f :: k -> * -> *) where
    type family Plus f (i :: k) (j :: k) :: k
    type instance Plus f i j = Combine f i j

    kplus :: Inv f i j => f i a -> f j a -> f (Plus f i j) a

-- Should satisfy left catch, use the operator <|>
class KMonad f => KMonadOr (f :: k -> * -> *) where
    type family Or f (i :: k) (j :: k) :: k
    type instance Or f i j = Combine f i j

    korelse :: Inv f i j => f i a -> f j a -> f (Or f i j) a

class KMonad f => KMonadFix (f :: k -> * -> *) where
    type family Fix f (i :: k) :: k

    kfix :: (a -> f i a) -> f (Fix f i) a

-- Wrapping a non-indexed type: 
newtype WrappedM (m :: * -> *) (p :: ()) a where
    WrappedM :: m a -> WrappedM m p a

unM :: WrappedM m p a -> m a
unM (WrappedM m) = m

liftWM :: m a -> WrappedM m '() a
liftWM = WrappedM

instance KEffect (WrappedM m :: () -> * -> *) where
    type Unit (WrappedM _) = '()
    type Inv  (WrappedM _) i j = (i ~ '(), j ~ '())
    type Combine (WrappedM _) _ _ = '()

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
newtype WrappedIx (m :: * -> *) (p :: CatArr i j) (a :: *) = WrappedIx { unIx :: m a }

data CatArr a b where
    CatId :: CatArr a b
    CArrow  :: a -> b -> CatArr a b

instance KEffect (WrappedIx m :: CatArr i j -> * -> *) where
    type Unit (WrappedIx _) = 'CatId
    type Inv  (WrappedIx _) ('CArrow _ b) ('CArrow c _) = b ~~ c
    type Combine (WrappedIx _) ('CatId     ) ('CatId     ) = 'CatId 
    type Combine (WrappedIx _) ('CArrow a _) ('CArrow _ d) = 'CArrow a d
    type Combine (WrappedIx _) ('CArrow a b) ('CatId     ) = 'CArrow a b
    type Combine (WrappedIx _) ('CatId     ) ('CArrow c d) = 'CArrow c d

type family FstArr (p :: CatArr i j) where
    FstArr ('CArrow a _) = a

type family SndArr (p :: CatArr i j) where
    SndArr ('CArrow _ b) = b

instance Applicative m => KPointed (WrappedIx m) where
    kreturn = WrappedIx . pure

instance Functor m => KFunctor (WrappedIx m) where
    kmap f = WrappedIx . fmap f . unIx

instance Applicative m => KApplicative (WrappedIx m) where
    type But (WrappedIx m) i j = Combine (WrappedIx m) i j

    kap (WrappedIx m) (WrappedIx k) = WrappedIx $ m <*> k
    kthen (WrappedIx m) (WrappedIx k) = WrappedIx $ (m *> k)
    kbut (WrappedIx m) (WrappedIx k) = WrappedIx $ (m <* k)

instance Monad m => KMonad (WrappedIx m) where
    kbind (WrappedIx m) k = WrappedIx $ m >>= unIx . k

instance MonadPlus m => KMonadFail (WrappedIx m) where
    kfail _ = WrappedIx $ mzero
