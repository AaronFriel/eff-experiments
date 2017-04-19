{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
-- {-# LANGUAGE RebindableSyntax #-}
-- {-# LANGUAGE ApplicativeDo #-}
-- {-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- {-# LANGUAGE TypeFamilies #-}
-- {-# LANGUAGE TypeApplications #-}
-- {-# LANGUAGE TypeOperators #-}
-- {-# LANGUAGE MultiParamTypeClasses #-}
-- {-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE FlexibleContexts #-}
-- {-# LANGUAGE UndecidableInstances #-}
-- {-# LANGUAGE TypeInType #-}
-- {-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Control.Monad.Graph.Prelude where

-- import Control.Monad.Graph.Eff
import Control.Monad.Graph.Class

import Prelude hiding (
    -- Functor
    fmap, (<$), (<$>),
    -- Applicative
    pure, (<*>), (*>), (<*), 
    -- Monad
    return, (>>=), (=<<), (>>)
    )

fmap :: GFunctor f => (a -> b) -> f i a -> f (Fmapish i) b
fmap = gmap

(<$) :: GFunctor f => b -> f i a -> f (Fmapish i) b
(<$) = gmap . const

(<$>) :: GFunctor f => (a -> b) -> f i a -> f (Fmapish i) b
(<$>) = fmap

pure :: (GPointed f, PurishCxt i) => a -> f i a
pure = greturn

(<*>) :: (GApplicative f, ApCxt i j r) => f i (a -> b) -> f j a -> f r b
(<*>) = gap
infixl 4 <*>

(*>) :: (GApplicative f, ApCxt (Fmapish i) j r) => f i a -> f j b -> f r b
a1 *> a2 = (id <$ a1) <*> a2

-- -- (<*) :: GraphEff u i a -> GraphEff u j b -> GraphEff u (Apish (Mapish i) j) a
-- (<*) :: (GApplicative f, PurishCxt i, ApCxt i j1 i1, ApCxt i1 j r) => f j1 b1 -> f j b -> f r b1
-- (<*) = liftA2 const

-- -- return :: a -> GraphEff u 'Empty a
-- return :: (GPointed f i, EmptyishC f i) => a -> f i a
return = greturn

-- -- (=<<) :: (a -> GraphEff u j b) -> GraphEff u i a -> GraphEff u (Bindish i j) b
(=<<) = gbind

-- -- -- (>>=) :: GraphEff u i a -> (a -> GraphEff u j b) -> GraphEff u (Bindish i j) b
(>>=) = flip (=<<)

-- -- -- Simplified binding, what GHC.Base would like to do but cannot for backwards compatbility.
-- -- -- (>>) :: GraphEff u i a -> GraphEff u j b -> GraphEff u (Apish (Mapish i) j) b
(>>) = (*>)

-- -- -- With the above definitions, all types below are inferred.

-- -- -- liftA :: (a -> b) -> GraphEff u j a -> GraphEff u (Mapish j) b
liftA :: forall f i j r a b. (GApplicative f, ApCxt i j r, PurishCxt i) 
      => (a -> b) -> f j a -> f r b
liftA f a = pure @_ @i f <*> a

-- -- -- liftA2 :: (a -> b -> c) -> GraphEff u i a -> GraphEff u j b -> GraphEff u (Apish (Mapish i) j) c
-- liftA2 :: (EmptyishC f i0, GApplicative f i, GApplicative f j) 
--        => (a1 -> a -> b) -> f i a1 -> f j a -> f (Apish f (Apish f i0 i) j) b
liftA2 :: forall f i j j1 i1 r a1 a b. (GApplicative f, PurishCxt j1, ApCxt i j1 i1, ApCxt i1 j r)
       => (a1 -> a -> b) -> f j1 a1 -> f j a -> f r b
liftA2 f a b = pure @_ @i f <*> a <*> b

-- liftA3 :: (a -> b -> c -> d) -> GraphEff u i a -> GraphEff u j b -> GraphEff u k c -> GraphEff u (Apish (Apish (Mapish i) j) k) d
-- liftA3 :: forall f i j j1 j2 i1 i2 r a1 a2 a b. (GApplicative f, PurishCxt i, ApCxt i j2 i1, ApCxt i1 j1 i2, ApCxt i2 j r)
--        => (a2 -> a1 -> a -> b) -> f j2 a2 -> f j1 a1 -> f j a -> f r b
-- liftA3 f a b c = pure @_ @i1 f <*> a <*> b <*> c

liftM :: (GPointed f, Monad (f i), PurishCxt i)
       => (t -> b)
       -> f i t -> f i b
liftM f m1              = do { x1 <- m1; return (f x1) }

liftM2 :: (GPointed f, Monad (f i), PurishCxt i)
       => (t1 -> t -> b)
       -> f i t1 -> f i t -> f i b
liftM2 f m1 m2          = do { x1 <- m1; x2 <- m2; return (f x1 x2) }

-- liftM3 :: (a1 -> a2 -> a3 -> r) -> GraphEff u i1 a1 -> GraphEff u i2 a2 -> GraphEff u i3 a3 -> GraphEff u (Apish (Apish (Mapish i1) i2) i3) r
liftM3 :: (GPointed f, Monad (f i), PurishCxt i)
       => (t2 -> t1 -> t -> b)
       -> f i t2 -> f i t1 -> f i t -> f i b
liftM3 f m1 m2 m3       = do { x1 <- m1; x2 <- m2; x3 <- m3; return (f x1 x2 x3) }

liftM4 :: (GPointed f, Monad (f i), PurishCxt i)
       => (t3 -> t2 -> t1 -> t -> b)
       -> f i t3 -> f i t2 -> f i t1 -> f i t -> f i b
liftM4 f m1 m2 m3 m4    = do { x1 <- m1; x2 <- m2; x3 <- m3; x4 <- m4; return (f x1 x2 x3 x4) }

liftM5 :: (GPointed f, Monad (f i), PurishCxt i)
       => (t4 -> t3 -> t2 -> t1 -> t -> b)
       -> f i t4 -> f i t3 -> f i t2 -> f i t1 -> f i t -> f i b
liftM5 f m1 m2 m3 m4 m5 = do { x1 <- m1; x2 <- m2; x3 <- m3; x4 <- m4; x5 <- m5; return (f x1 x2 x3 x4 x5) }

ap :: (GPointed f, Monad (f i), PurishCxt i) => f i (t -> b) -> f i t -> f i b
ap m1 m2 = do { x1 <- m1; x2 <- m2; return (x1 x2) }


-- Recursive bindings may be impossible. This type is inferred, but not always satisfiable.
-- We will need to implement our own folds and control flow.
-- E.g., with GraphEff: ApCxt (Mapish i) 'Empty => Mapish i != 'Empty 
-- mapM_bad :: (Apish (Mapish i) 'Empty ~ 'Empty, Foldable t) 
--          => (a1 -> GraphEff u i a) -> t a1 -> GraphEff u 'Empty ()
mapM_ :: (GApplicative f, Foldable t, PurishCxt j, ApCxt (Fmapish i) j j)
      => (a1 -> f i a) -> t a1 -> f j ()
mapM_ f = foldr ((>>) . f) (return ())

-- As above.
sequence_Bad :: (GApplicative f, Foldable t, PurishCxt j, ApCxt (Fmapish i) j j) => t (f i a) -> f j ()
sequence_Bad = foldr (>>) (return ())
