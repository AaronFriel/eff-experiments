{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE PartialTypeSignatures #-}

module Control.Monad.Graph.Playground where

import Control.Monad.Graph.Eff
import Control.Monad.Graph.Class

import GHC.Exts (Constraint)

import GHC.TypeLits hiding (type (*))
import Data.Kind (type (*))

import Data.Singletons.Prelude
-- import Data.Singletons.Prelude.Bool
-- import Data.Singletons.TypeLits
import Data.Singletons.Decide
import Unsafe.Coerce

-- import Debug.Trace

import Prelude hiding (
    -- Functor
    fmap, (<$), (<$>),
    -- Applicative
    pure, (<*>), (*>), (<*), 
    -- Monad
    return, (>>=), (=<<), (>>)
    )

fmap :: (a -> b) -> GraphEff u i a -> GraphEff u (GraphMap i) b
fmap = gmap

(<$) :: b -> GraphEff u i a -> GraphEff u (GraphMap i) b
(<$) = fmap . const

(<$>) :: (a -> b) -> GraphEff u i a -> GraphEff u (GraphMap i) b
(<$>) = fmap

pure :: a -> GraphEff u 'Empty a
pure = greturn

(<*>) :: GraphEff u i (a -> b) -> GraphEff u j a -> GraphEff u (GraphAp i j) b
(<*>) = gap

(*>) :: GraphEff u i a -> GraphEff u j b -> GraphEff u (GraphAp (GraphMap i) j) b
a1 *> a2 = (id <$ a1) <*> a2

(<*) :: GraphEff u i a -> GraphEff u j b -> GraphEff u (GraphAp (GraphMap i) j) a
(<*) = liftA2 const

return :: a -> GraphEff u 'Empty a
return = greturn

(=<<) :: (a -> GraphEff u j b) -> GraphEff u i a -> GraphEff u (GraphBind i j) b
(=<<) = gbind

(>>=) :: GraphEff u i a -> (a -> GraphEff u j b) -> GraphEff u (GraphBind i j) b
(>>=) = flip (=<<)

-- Simplified binding, what GHC.Base would like to do but cannot for backwards compatbility.
(>>) :: GraphEff u i a -> GraphEff u j b -> GraphEff u (GraphAp (GraphMap i) j) b
(>>) = (*>)

-- With the above definitions, all types below are inferred.

liftA :: (a -> b) -> GraphEff u j a -> GraphEff u (GraphMap j) b
liftA f a = pure f <*> a

liftA2 :: (a -> b -> c) -> GraphEff u i a -> GraphEff u j b -> GraphEff u (GraphAp (GraphMap i) j) c
liftA2 f a b = pure f <*> a <*> b

liftA3 :: (a -> b -> c -> d) -> GraphEff u i a -> GraphEff u j b -> GraphEff u k c -> GraphEff u (GraphAp (GraphAp (GraphMap i) j) k) d
liftA3 f a b c = pure f <*> a <*> b <*> c

-- [Note: lifTM Types]
liftM :: (a1 -> r) -> GraphEff u i a1 -> GraphEff u (GraphMap i) r
liftM f m1              = do { x1 <- m1; return (f x1) }

liftM2 :: (a1 -> a2 -> r) -> GraphEff u i1 a1 -> GraphEff u i2 a2 -> GraphEff u (GraphAp (GraphMap i1) i2) r
liftM2 f m1 m2          = do { x1 <- m1; x2 <- m2; return (f x1 x2) }

liftM3 :: (a1 -> a2 -> a3 -> r) -> GraphEff u i1 a1 -> GraphEff u i2 a2 -> GraphEff u i3 a3 -> GraphEff u (GraphAp (GraphAp (GraphMap i1) i2) i3) r
liftM3 f m1 m2 m3       = do { x1 <- m1; x2 <- m2; x3 <- m3; return (f x1 x2 x3) }

liftM4 :: (a1 -> a2 -> a3 -> a4 -> r) -> GraphEff u i1 a1 -> GraphEff u i2 a2 -> GraphEff u i3 a3 -> GraphEff u i4 a4 -> GraphEff u (GraphAp (GraphAp (GraphAp (GraphMap i1) i2) i3) i4) r
liftM4 f m1 m2 m3 m4    = do { x1 <- m1; x2 <- m2; x3 <- m3; x4 <- m4; return (f x1 x2 x3 x4) }

liftM5 :: (a1 -> a2 -> a4 -> a5 -> a6 -> r) -> GraphEff u i1 a1 -> GraphEff u i2 a2 -> GraphEff u i3 a4 -> GraphEff u i4 a5 -> GraphEff u i5 a6 -> GraphEff u (GraphAp (GraphAp (GraphAp (GraphAp (GraphMap i1) i2) i3) i4) i5) r
liftM5 f m1 m2 m3 m4 m5 = do { x1 <- m1; x2 <- m2; x3 <- m3; x4 <- m4; x5 <- m5; return (f x1 x2 x3 x4 x5) }

ap :: GraphEff u i (a -> b) -> GraphEff u j a -> GraphEff u (GraphAp (GraphMap i) j) b
ap m1 m2 = do { x1 <- m1; x2 <- m2; return (x1 x2) }


-- Recursive bindings are (naively) impossible. This type is inferred, but unsatisfiable.
-- We will need to implement our own folds and control flow.
-- GraphAp (GraphMap i) 'Empty => GraphMap i != 'Empty 
mapM_bad :: (GraphAp (GraphMap i) 'Empty ~ 'Empty, Foldable t)
      => (a1 -> GraphEff u i a) -> t a1 -> GraphEff u 'Empty ()
mapM_bad f = foldr ((>>) . f) (return ())

-- We can fix the types to allow recursive pure folds:
mapM_pure :: (Foldable t) => (a1 -> GraphEff u 'Empty a) -> t a1 -> GraphEff u 'Empty ()
mapM_pure f = foldr ((>>) . f) (return ())

-- As above.
sequence_Bad :: (GraphAp (GraphMap i) 'Empty ~ 'Empty, Foldable t) => t (GraphEff u i a) -> GraphEff u 'Empty ()
sequence_Bad = foldr (>>) (return ())

sequence_Pure :: (Foldable t) => t (GraphEff u 'Empty a) -> GraphEff u 'Empty ()
sequence_Pure = foldr (>>) (return ())

{-       ######## ######## ######## ########  ######  ########  ######  
         ##       ##       ##       ##       ##    ##    ##    ##    ## 
         ##       ##       ##       ##       ##          ##    ##       
         ######   ######   ######   ######   ##          ##     ######  
         ##       ##       ##       ##       ##          ##          ## 
         ##       ##       ##       ##       ##    ##    ##    ##    ## 
         ######## ##       ##       ########  ######     ##     ######        -}


type family EffectDepth u e where
    EffectDepth '[              '[] ] e = TypeError (
                                            'Text "The effect " ':<>: 'ShowType e 
                                            ':<>: 'Text " has not been handled.")
    EffectDepth  (       '[]  ': ts )  e = 1 + (EffectDepth ts e)
    EffectDepth  (  (e ': rs) ': ts )  e = 0
    EffectDepth  (  (x ': rs) ': ts )  e = EffectDepth ( rs ': ts ) e

type family RunEffect' u es where
    RunEffect'   u   '[] = u
    RunEffect' efx  (e ': es) = RunEffect' (e ': efx) es

type family RunEffect u es where
    RunEffect ('Graph ps efx)    es = 'Graph ps (RunEffect' efx es)

class HasEffect u i e

data TrivialData
type Trivial = TrivialData ~ TrivialData

type family HasEffectTree i e :: Constraint where
    HasEffectTree (    'Do e) e = Trivial
    HasEffectTree (i ':>>= j) e = (HasEffectTree i e, HasEffectBindTree j e)

type family HasEffectBindTree i e :: Constraint where
    HasEffectBindTree ('TLeaf i)   e = HasEffectTree i e
    HasEffectBindTree ('TNode i j) e = (HasEffectBindTree i e, HasEffectBindTree j e)

prepare :: GraphEff ('Graph '[] '[]) i a -> GraphEff ('Graph '[] '[]) i a
prepare a = a

type EmptyU' = 'Graph '[] '[]

data Reader e where
    Ask :: Reader e
type instance Output (Reader e) = e

ask :: forall e u. GraphEff u ('Do (Reader e)) e
ask = send Ask

data Writer o where
    Tell :: o -> Writer o
type instance Output (Writer o) = ()

tell :: o -> GraphEff u ('Do (Writer o)) ()
tell = send . Tell

data Get s = Get
data Put s = Put !s

get :: forall e u. GraphEff u ('Do (Get e)) e
get = send Get
put :: forall e u. e -> GraphEff u ('Do (Put e)) ()
put = send . Put

type instance Output (Get s) = s
type instance Output (Put s) = ()


data Call (n :: Nat) a where
    Call :: GraphEff u i a -> Call n a

call :: forall n u i a. GraphEff u i a -> GraphEff u ('Do (Call n a)) a
call = send . Call

type instance Output (Call i a) = a

-- Type is inferred.
-- t1 :: GraphEff u ('Aps ('Aps ('Do (Reader Int)) ('Do (Reader Float))) ('Do (Reader String))) (Int, Float, String)
t1 :: GraphEff U (('Do (Reader Int) ':<*> 'Do (Reader Float)) ':<*> 'Do (Reader String)) (Int, Float, String)
t1 = simple $ do
    a <- ask @Int
    b <- ask @Float
    c <- ask @String
    return (a, b, c)

t2 :: GraphEff U ('Do (Reader Int) ':>>= 'TLeaf ('Do (Writer String))) Int
t2 = simple $ do
    a <- ask @Int
    tell (show a)
    return (a + 1)

simple :: GraphEff U i a -> GraphEff U i a
simple a = a

auto :: ((GraphEff u i a -> GraphEff u ('Do (Call 0 a)) a) -> GraphEff u i a) -> GraphEff u i a
auto m = m undefined

tloop :: GraphEff u ('Do (Writer [Char]) ':<*> 'Do (Call 0 a)) a
tloop = auto $ \cc -> do
    tell "Foobar"
    cc tloop

type family TDecomp i e where
    TDecomp 'Empty      e = ()
    TDecomp (i ':>>= j) e = Either (Decomp i e :~: 'False)  (i :~: ('Do e))
    TDecomp i           e = Either (Decomp i e :~: 'False)  (i :~: ('Do e))
    -- TDecomp (i ':<*> j) e = ( Either (Decomp i e :~: 'False)      (i :~: ('Do e))
    --                         , Either (Decomp i e :~: 'False)      (i :~: ('Do e))
    --                         )

type family Decomp i e where
    Decomp ('Do e) e     = 'True
    Decomp (i ':>>= j) e = Decomp i e
    Decomp (i ':<*> j) e = Decomp i e
    Decomp 'Empty      _ = 'False
    Decomp _           _ = 'False

decompE :: forall e u i a. _
       => GraphEff u i a
       -> Either (Decomp i e :~: 'False) (i :~: 'Do e)
decompE m = case STrue %~ sing @Bool @(Decomp i e) of
    Proved _ -> Right $ unsafeCoerce Refl
    _ -> Left $ unsafeCoerce Refl

decompB :: forall e u i j a. _
       => GraphEff u (i :>>= j) a
       -> Either (Decomp (i :>>= j) e :~: 'False) (Decomp (i :>>= j) e :~: 'True, (i :>>= j) :~: ('Do e :>>= j))
decompB m = case STrue %~ sing @Bool @(Decomp (i :>>= j) e) of
    Proved _ -> Right $ (unsafeCoerce Refl, unsafeCoerce Refl)
    _ -> Left $ unsafeCoerce Refl

type WriterOutput o a = (a, [o])

type family RunSimple' g e d o where
    RunSimple' (GraphEff u    'Empty  a) e          _ o = GraphEff (RunEffect u '[e]) 'Empty (a, o)
    RunSimple' (GraphEff u    ('Do e) a) e      'True o = GraphEff (RunEffect u '[e]) 'Empty (a, o)
    RunSimple' (GraphEff u    ('Do x) a) e     'False o = GraphEff (RunEffect u '[e]) ('Do x) (a, o)
    RunSimple' (GraphEff u   (i ':>>= j) a) e   'True o = (GraphEff u (FViewL j) a, o)
    RunSimple' (GraphEff u   (i ':>>= j) a) e  'False o = GraphEff (RunEffect u '[e]) (i :>>= j) (a, o)
    -- RunSimple' (GraphEff u i a) e         decomp     = GraphEff (RunEffect u '[e]) i

type family RunSimple g e o where
    RunSimple (GraphEff u i a) e o = RunSimple' (GraphEff u i a) e (Decomp i e) o

runWriter :: forall o u i a. SingI (Decomp i (Writer o)) 
          => GraphEff u i a
          -> [o]
          -> RunSimple (GraphEff u i a) (Writer o) [o] -- (RunEffect u '[ Writer o ]) i (a, [o])
runWriter m o = case m of
    (V x)   -> V (x, o)
    (E u q) -> case (decompE @(Writer o) m, u) of
        (Right Refl, Tell o') -> V (q (), o' : o)
        -- (Left Refl,  _      ) -> gmap (\r -> (r, o)) (E u q)
    (B u q) -> case (decompB @(Writer o) m, u) of
        (Right (Refl, Refl), E (Tell o') q') -> case tviewl $ q of
            TOne f -> (f (q' ()), o' : o)
        (Left Refl, _) -> error "Bad branch"

twr m = run $ flip runWriter ["World!"] $ m

tw1 = pure "Hello, "
trw1 = twr tw1
tw2 = tell "Hello, " >>= (const $ V '!')
trw2 = run $ uncurry runWriter $ flip runWriter ["World!"] $ tw2

tw3 = tell "Beautiful, " >>= \_ -> tell "Hello " >>= \_ -> return 42
trw3 = run $ uncurry runWriter $ uncurry runWriter $ flip runWriter ["World!"] $ tw3

runReader :: GraphEff u i a -> e -> GraphEff (RunEffect u '[ Reader e ]) i a
runReader = undefined


run :: GraphEff u 'Empty a -> a
run (V a) = a

{- Note [Lawful instances]
~~~~~~~~~~~~~~~~~~~~~~~~~~

The types for all GraphEff operations have an additional two parameters over
what other monads do. For the sake of considering Monad, Applicative, and
Functor laws, we should disregard the second parameter (typically i). It's
_almost_ a phantom parameter, but it's used primarily for nice pattern matching.

-}

{- Note [liftM Types]
~~~~~~~~~~~~~~~~~~~~~

The types for liftM, liftMn are inferred with or without ApplicativeDo, but the
types change because of the second type parameter to GraphEff changing depending
on the operations performed (Functor vs Applicative vs Monad).

With ApplicativeDo, liftM becomes goes from:
  liftf m1 = { x1 <- m1; return (f x1) }
to:
  liftf m1 = fmap f m1

Here are the types inferred without ApplicativeDo:

liftM :: (t -> b) -> GraphEff u i t -> GraphEff u (GraphBind i 'Empty) b
liftM2 :: (t1 -> t -> b) -> GraphEff u i1 t1 -> GraphEff u i t -> GraphEff u (GraphBind i1 (GraphBind i 'Empty)) b
liftM3 :: (t2 -> t1 -> t -> b) -> GraphEff u i2 t2 -> GraphEff u i1 t1 -> GraphEff u i t -> GraphEff u (GraphBind i2 (GraphBind i1 (GraphBind i 'Empty))) b
liftM4 :: (t3 -> t2 -> t1 -> t -> b) -> GraphEff u i3 t3 -> GraphEff u i2 t2 -> GraphEff u i1 t1 -> GraphEff u i t -> GraphEff u (GraphBind i3 (GraphBind i2 (GraphBind i1 (GraphBind i 'Empty)))) b
liftM5 :: (t4 -> t3 -> t2 -> t1 -> t -> b) -> GraphEff u i4 t4 -> GraphEff u i3 t3 -> GraphEff u i2 t2 -> GraphEff u i1 t1 -> GraphEff u i t -> GraphEff u (GraphBind i4 (GraphBind i3 (GraphBind i2 (GraphBind i1 (GraphBind i 'Empty))))) b
ap :: GraphEff u j (a -> b) -> GraphEff u i a -> GraphEff u (GraphBind j (GraphBind i 'Empty)) b

-}
