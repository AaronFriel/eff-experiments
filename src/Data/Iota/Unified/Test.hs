{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RankNTypes, TypeInType, TypeOperators, ExplicitNamespaces
  #-}

{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ApplicativeDo #-}

{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.Iota.Unified.Test where

import Prelude hiding (return, (>>=), (>>), fail, fmap, pure, (<*>))
import qualified Prelude as P (return, (>>=), (>>), fail, fmap, pure, (<*>))
import Control.Monad (ap)
import Data.Singletons.Prelude.List
import Data.Iota.Unified.Indexed
import Data.Kind (type (*))
import Control.Monad.Indexed

import Data.Singletons
import Data.Singletons.TH


$(singletons [d|
  data TQueue (arr :: *) a b where
    TLeaf :: arr -> TQueue arr a b
    TNode :: TQueue arr1 a x -> TQueue arr2 x b -> TQueue arr a b

  data IViewL
  |])


class IxMonad m => IxFail m where
  ifail :: String -> m i j a
  ifail = error

newtype WF f x y a = LiftWF { runWF :: f a }

instance Functor f => IxFunctor (WF f) where
  imap f x = LiftWF (f `P.fmap` runWF x)

newtype WA f x y a = LiftWA { runWA :: f a }

instance Functor f => IxFunctor (WA f) where
  imap f x = LiftWA (f `P.fmap` runWA x)

instance Applicative m => IxPointed (WA m) where
    ireturn x = LiftWA (P.pure x)

instance Applicative m => IxApplicative (WA m) where
    iap f x = LiftWA (runWA f P.<*> runWA x)

newtype WM m x y a = LiftWM { runWM :: m a }

instance Functor f => IxFunctor (WM f) where
  imap f x = LiftWM (f `P.fmap` runWM x)

instance Applicative m => IxPointed (WM m) where
    ireturn x = LiftWM (P.pure x)

instance Applicative m => IxApplicative (WM m) where
    iap f x = LiftWM (runWM f P.<*> runWM x)

instance Monad m => IxMonad (WM m) where
    ibind f m = LiftWM (runWM m P.>>= runWM . f)

instance Monad m => IxFail (WM m) where
    ifail str = LiftWM (P.fail str)

fmap :: IxFunctor f => forall a b (j :: k) (k2 :: k1). (a -> b) -> f j k2 a -> f j k2 b
fmap = imap

pure :: IxPointed m => forall a (i :: k). a -> m i i a
pure = ireturn

(<*>) :: IxApplicative m => m i j (a -> b) -> m j k1 a -> m i k1 b
(<*>) = iap

join :: IxMonad m => forall a (i :: k) (j :: k) (k1 :: k). m i j (m j k1 a) -> m i k1 a
join = ibind id

return
    :: IxPointed m
    => forall a (i :: k). a -> m i i a
return = ireturn

(>>=)
    :: forall k (m :: k -> k -> * -> *) (i :: k) (j :: k) a (k1 :: k) b.
       IxMonad m
    => m i j a -> (a -> m j k1 b) -> m i k1 b
(>>=) = (>>>=)

(>>)
    :: forall k (m :: k -> k -> * -> *) (i :: k) (j :: k) a (k1 :: k) b.
       IxMonad m
    => m i j a -> m j k1 b -> m i k1 b
m >> n = m >>= const n

fail :: IxFail m => forall (i :: k) (j :: k) a. String -> m i j a
fail = ifail

f m = (<*>) (fmap (,) m) m

fPure' m = join ( (<*>) (fmap (\a b -> pure (a, b)) m) m )

fReturn' m = join ( (<*>) (fmap (\a b -> pure (a, b)) m) m )

fPure m = do
  a <- m
  b <- m
  return $ (a, b)

fReturn m = do
  a <- m
  b <- m
  return (a, b)

--
-- t1' :: Eff r i (i :++ '[ '(Reader Int, FindElem (Reader Int) r)]) Int
-- t1' = do
--   a :: Int <- ask
--   return (a + (1 :: Int))
