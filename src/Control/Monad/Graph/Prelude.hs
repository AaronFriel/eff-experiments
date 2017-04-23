{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ApplicativeDo #-}

{-# LANGUAGE PartialTypeSignatures #-}

{-# LANGUAGE GADTs #-}

-- Needed for poly-kinded "f :: k -> * -> *"
{-# LANGUAGE PolyKinds #-}

{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Control.Monad.Graph.Prelude (
    -- Functor
    fmap, (<$), (<$>),
    -- Applicative
    pure, (<*>), (*>), (<*), 
    -- Monad
    return, (>>=), (=<<), (>>),
    -- Extra operators:
    (<**>), liftA, liftA2, liftA3,
    join, liftM, liftM2, liftM3, liftM4, liftM5, ap,

    mapM_, sequence_
    ) where

import Prelude hiding (
    -- Functor
    fmap, (<$), (<$>),
    -- Applicative
    pure, (<*>), (*>), (<*), 
    -- Monad
    return, (>>=), (=<<), (>>),

    mapM_, sequence_
    )

import Control.Monad.Graph.Class

infixl 4  <$
infixl 1  >>, >>=
infixr 1  =<<
infixl 4 <*>, <*, *>, <**>

fmap :: KFunctor f => (a -> b) -> f i a -> f (Fmap f i) b
fmap = kmap

(<$) :: KFunctor f => b -> f i a -> f (Fmap f i) b
(<$) = kmap . const

(<$>) :: KFunctor f => (a -> b) -> f i a -> f (Fmap f i) b
(<$>) = fmap

pure :: KPointed f => a -> f (Unit f) a
pure = kreturn

(<*>) :: (KApplicative f, _) => f i (a -> b) -> f j a -> f (Apply f i j) b
(<*>) = kap

(*>) :: (KApplicative f, _) => f i a -> f j b -> f (Apply f (Fmap f i) j) b
a1 *> a2 = (id <$ a1) <*> a2

(<*) :: (KApplicative f, _) => f j1 b1 -> f j b -> f (Apply f (Apply f (Unit f) j1) j) b1
(<*) = liftA2 const

return :: KPointed f => a -> f (Unit f) a
return = kreturn

(=<<) :: (KMonad f, Inv f i j) => (a -> f j b) -> f i a -> f (Bind f i j) b
(=<<) = flip (>>=)

(>>=) :: (KMonad f, Inv f i j) => f i a -> (a -> f j b) -> f (Bind f i j) b
(>>=) = kbind

-- Simplified binding, what GHC.Base would like to do but cannot for backwards compatbility.
(>>) :: (KApplicative f, _) => f i a -> f j b -> f (Apply f (Fmap f i) j) b
(>>) = (*>)

(<**>) :: (KApplicative f, _) => f j1 a -> f j (a -> b) -> f (Apply f (Apply f (Unit f) j1) j) b
(<**>) = liftA2 (flip ($))

liftA :: (KApplicative f, _) => (a -> b) -> f j a -> f (Apply f (Unit f) j) b
liftA f a = pure f <*> a

liftA2 :: (KApplicative f, _) => (a1 -> a -> b) -> f j1 a1 -> f j a -> f (Apply f (Apply f (Unit f) j1) j) b
liftA2 f a b = pure f <*> a <*> b

liftA3 :: (KApplicative f, _) => (a2 -> a1 -> a -> b) -> f j2 a2 -> f j1 a1 -> f j a -> f (Apply f (Apply f (Apply f (Unit f) j2) j1) j) b
liftA3 f a b c = pure f <*> a <*> b <*> c

join :: (KMonad f, Inv f i j) => f i (f j b) -> f (Bind f i j) b
join x = x >>= id

liftM :: (KApplicative f, _) => (t -> b) -> f j t -> f (Fmap f j) b
liftM f m1              = do { x1 <- m1; return (f x1) }

liftM2 :: (KApplicative f, _)
       => (t1 -> t -> b)
       -> f j1 t1
       -> f j t
       -> f (Apply f (Fmap f j1) j) b
liftM2 f m1 m2          = do { x1 <- m1; x2 <- m2; return (f x1 x2) }

liftM3 :: (KApplicative f, _)
       => (t2 -> t1 -> t -> b)
       -> f j2 t2
       -> f j1 t1
       -> f j t
       -> f (Apply f (Apply f (Fmap f j2) j1) j) b
liftM3 f m1 m2 m3       = do { x1 <- m1; x2 <- m2; x3 <- m3; return (f x1 x2 x3) }

liftM4 :: (KApplicative f, _)
       => (t3 -> t2 -> t1 -> t -> b)
       -> f i t3
       -> f j2 t2
       -> f j1 t1
       -> f j t
       -> f (Apply f (Apply f (Apply f (Fmap f i) j2) j1) j) b
liftM4 f m1 m2 m3 m4    = do { x1 <- m1; x2 <- m2; x3 <- m3; x4 <- m4; return (f x1 x2 x3 x4) }

liftM5 :: (KApplicative f, _) 
       => (t4 -> t3 -> t2 -> t1 -> t -> b)
       -> f i t4
       -> f j3 t3
       -> f j2 t2
       -> f j1 t1
       -> f j t
       -> f (Apply f (Apply f (Apply f (Apply f (Fmap f i) j3) j2) j1) j) b
liftM5 f m1 m2 m3 m4 m5 = do { x1 <- m1; x2 <- m2; x3 <- m3; x4 <- m4; x5 <- m5; return (f x1 x2 x3 x4 x5) }

ap :: (KApplicative f, Inv f (Fmap f i) j) => f i (t -> b) -> f j t -> f (Apply f (Fmap f i) j) b
ap m1 m2 = do { x1 <- m1; x2 <- m2; return (x1 x2) }

-- Recursive bindings may be impossible. This type is inferred, but not always satisfiable.
-- We will need to implement our own folds and control flow.
mapM_ :: (KApplicative f, Foldable t, Apply f (Fmap f i) (Unit f) ~ Unit f, _)
      => (a1 -> f i a) -> t a1 -> f (Unit f) ()
mapM_ f = foldr ((>>) . f) (return ())

-- As above.
sequence_ :: (KApplicative f, Foldable t, Apply f (Fmap f i) (Unit f) ~ Unit f, _)
          => t (f i a) -> f (Unit f) ()
sequence_ = foldr (>>) (return ())
