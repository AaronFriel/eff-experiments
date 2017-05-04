{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ApplicativeDo #-}

{-# LANGUAGE PartialTypeSignatures #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

-- Needed for poly-kinded "f :: k -> * -> *"
{-# LANGUAGE PolyKinds #-}

{-# LANGUAGE StrictData #-}

{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Control.Monad.Graph.Prelude (
    -- Functor
    fmap, (<$), (<$>),
    -- Applicative
    pure, (<*>), (*>), (<*), 
    -- Monad
    return, (>>=), (=<<), (>>),
    -- MonadFail
    fail,
    -- MonadPlus, MonadOr    
    (<+>), (<|>),
        
    -- Extra operators:
    (<**>), liftA, liftA2, liftA3,
    join, liftM, liftM2, liftM3, liftM4, liftM5, ap,

    mapM_, sequence_,

    module X
    ) where

import Prelude as X hiding (
    -- Functor
    fmap, (<$), (<$>),
    -- Applicative
    pure, (<*>), (*>), (<*), 
    -- Monad
    return, (>>=), (=<<), (>>),
    -- MonadFail
    fail,

    mapM_, sequence_
    )

import Control.Monad.Graph.Class

infixl 4  <$
infixl 1  >>, >>=
infixr 1  =<<
infixl 4 <*>, <*, *>, <**>

fmap :: KFunctor f => (a -> b) -> f i a -> f (Fmap f i) b
fmap = kmap

(<$) :: KFunctor f => b -> f i a -> f (Fconst f i) b
(<$) = kconst

(<$>) :: KFunctor f => (a -> b) -> f i a -> f (Fmap f i) b
(<$>) = fmap

pure :: KPointed f => a -> f (Unit f) a
pure = kreturn

(<*>) :: (KApplicative f, _) => f i (a -> b) -> f j a -> f (Apply f i j) b
(<*>) = kap

(*>) :: (KApplicative f, _) => f i a -> f j b -> f (Then f i j) b
(*>)= kthen

(<*) :: (KApplicative f, _) => f i a -> f j b -> f (But f i j) a
(<*) = kbut

return :: KPointed f => a -> f (Unit f) a
return = kreturn

(>>=) :: (KMonad f, Inv f i j) => f i a -> (a -> f j b) -> f (Bind f i j) b
(>>=) = kbind

(=<<) :: (KMonad f, Inv f i j) => (a -> f j b) -> f i a -> f (Bind f i j) b
(=<<) = flip (>>=)

fail :: KMonadFail f => String -> f (Fail f) i
fail = kfail

(<+>) :: (KMonadPlus f, _) => f i a -> f j a -> f (Plus f i j) a
(<+>) = kplus

(<|>) :: (KMonadOr f, _) => f i a -> f j a -> f (Or f i j) a
(<|>) = korelse

-- Simplified binding, what GHC.Base would like to do but cannot for backwards compatbility.
(>>) :: (KApplicative f, _) => f i a -> f j b -> f (Then f i j) b
(>>) = kthen

join :: (KMonad f, Inv f i j) => f i (f j b) -> f (Join f i j) b
join = kjoin

(<**>) :: (KApplicative f, _) => f i1 a -> f i2 (a -> b) -> f (Apply f (Apply f (Unit f) i1) i2) b
(<**>) = liftA2 (flip ($))

liftA :: (KApplicative f, _) => (a -> b) -> f i1 a -> f (Apply f (Unit f) i1) b
liftA f a = pure f <*> a

liftA2 :: (KApplicative f, _) => (a1 -> a2 -> b) -> f i1 a1 -> f i2 a2 -> f (Apply f (Apply f (Unit f) i1) i2) b
liftA2 f a b = pure f <*> a <*> b

liftA3 :: (KApplicative f, _) => (a1 -> a2 -> a3 -> b) -> f i1 a1 -> f i2 a2 -> f i3 a3 -> f (Apply f (Apply f (Apply f (Unit f) i1) i2) i3) b
liftA3 f a b c = pure f <*> a <*> b <*> c

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
