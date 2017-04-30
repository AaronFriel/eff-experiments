{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DefaultSignatures #-}

-- Makes for nicer type families where Plus is reused.
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE StrictData #-}

module Control.Monad.Graph.Class.Indexed where

import Control.Monad.Graph.Class
import Data.Kind (Constraint, type (*))
import Control.Monad
import Control.Monad.Indexed
import Data.Type.Equality
import GHC.Base (Any)

-- Wrapped IxMonad from Control.Monad.Indexed
newtype WrappedIx (m :: k -> k -> * -> *) (p :: CatArr k k) a = WrappedIx { unWix :: m (FstArr p) (SndArr p) a }

instance KEffect (WrappedIx m) where
    type Unit (WrappedIx m) = 'CatId
    type Inv  (WrappedIx m) i j = (SndArr i ~~ FstArr j)
    type Plus (WrappedIx m) i j  = 'CArrow (FstArr i) (SndArr j)  

instance Fmappable (WrappedIx m)
instance Applyable (WrappedIx m) where
    type Then (WrappedIx m) i j = Plus (WrappedIx m) i j
    type But (WrappedIx m) i j = Plus (WrappedIx m) i j
instance Bindable (WrappedIx m)

instance IxPointed m => KPointed (WrappedIx m) where
    kreturn = WrappedIx . ireturn

instance IxFunctor m => KFunctor (WrappedIx m) where
    kmap f = WrappedIx . imap f . unWix

instance IxApplicative m => KApplicative (WrappedIx m) where
    kap (WrappedIx m) (WrappedIx k) = WrappedIx $ m `iap` k
    kthen (WrappedIx m) (WrappedIx k) = WrappedIx $ (imap . const) id m `iap` k
    kbut (WrappedIx m) (WrappedIx k) = WrappedIx $ ireturn const `iap` m `iap` k

instance IxMonad m => KMonad (WrappedIx m) where
    kbind (WrappedIx m) k = WrappedIx $ (unWix . k) `ibind` m

instance IxMonadZero m => KMonadFail (WrappedIx m) where
    kfail _ = WrappedIx $ imzero
