{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ApplicativeDo #-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeInType #-}

{-# LANGUAGE FlexibleContexts #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE LiberalTypeSynonyms #-}

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}

{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -Wno-unticked-promoted-constructors -Wno-missing-signatures -Wno-unused-imports -Wno-type-defaults -Wno-partial-type-signatures #-}

module Control.Monad.Graph.Playground where

import Control.Monad.Graph.Eff

import qualified Control.Monad.Graph.Prelude as G

import GHC.Exts (Constraint)

import GHC.TypeLits hiding (type (*))
import Data.Kind (type (*))
import Data.Proxy
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Bool
-- import Data.Singletons.TypeRepStar
import Data.Singletons.Decide
import Unsafe.Coerce
import Control.Lens hiding ((%~))

-- import Debug.Trace

import Prelude hiding (
    -- Functor
    fmap, (<$), (<$>),
    -- Applicative
    pure, (<*>), (*>), (<*), 
    -- Monad
    return, (>>=), (=<<), (>>)
    )

infixl 4  <$
infixl 1  >>, >>=
infixr 1  =<<
infixl 4 <*>, <*, *>, <**>

fmap :: (a -> b) -> GraphEff u i a -> GraphEff u (GraphMap i) b
fmap = G.fmap

(<$) :: b -> GraphEff u i a -> GraphEff u (GraphMap i) b
(<$) = G.fmap . const

(<$>) :: (a -> b) -> GraphEff u i a -> GraphEff u (GraphMap i) b
(<$>) = G.fmap

pure :: a -> GraphEff u 'Pure a
pure = G.pure

(<*>) :: GraphEff u i (a -> b) -> GraphEff u j a -> GraphEff u (GraphAp i j) b
(<*>) = (G.<*>)

return :: a -> GraphEff u 'Pure a
return = G.pure

(>>=) :: GraphEff u i a -> (a -> GraphEff u j b) -> GraphEff u (GraphBind i j) b
(>>=) = (G.>>=)

-- With the above definitions, all types below are inferred.
liftA :: (a -> b) -> GraphEff u j a -> GraphEff u (GraphMap j) b
liftA f a = pure f <*> a

liftA2 :: (a -> b -> c) -> GraphEff u i a -> GraphEff u j b -> GraphEff u (GraphAp (GraphMap i) j) c
liftA2 f a b = pure f <*> a <*> b

liftA3 :: (a -> b -> c -> d) -> GraphEff u i a -> GraphEff u j b -> GraphEff u k c -> GraphEff u (GraphAp (GraphAp (GraphMap i) j) k) d
liftA3 f a b c = pure f <*> a <*> b <*> c

(<*) :: GraphEff u i a -> GraphEff u j b -> GraphEff u (GraphAp (GraphMap i) j) a
(<*) = liftA2 const

(*>) :: GraphEff u i a -> GraphEff u j b -> GraphEff u (GraphAp (GraphMap i) j) b
a1 *> a2 = (id <$ a1) <*> a2

(<**>) :: GraphEff u i a -> GraphEff u j (a -> b) -> GraphEff u (GraphAp (GraphMap i) j) b
(<**>) = liftA2 (flip ($))

(>>) :: GraphEff u i a -> GraphEff u j b -> GraphEff u (GraphAp (GraphMap i) j) b
(>>) = (*>)

(=<<) :: (a -> GraphEff u j b) -> GraphEff u i a -> GraphEff u (GraphBind i j) b
(=<<) = flip (>>=)

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
-- GraphAp (GraphMap i) 'Pure => GraphMap i != 'Pure 
mapM_bad :: (GraphAp (GraphMap i) 'Pure ~ 'Pure, Foldable t)
      => (a1 -> GraphEff u i a) -> t a1 -> GraphEff u 'Pure ()
mapM_bad f = foldr ((>>) . f) (return ())

-- We can fix the types to allow recursive pure folds:
mapM_pure :: (Foldable t) => (a1 -> GraphEff u 'Pure a) -> t a1 -> GraphEff u 'Pure ()
mapM_pure f = foldr ((>>) . f) (return ())

-- As above.
sequence_Bad :: (GraphAp (GraphMap i) 'Pure ~ 'Pure, Foldable t) => t (GraphEff u i a) -> GraphEff u 'Pure ()
sequence_Bad = foldr (>>) (return ())

sequence_Pure :: (Foldable t) => t (GraphEff u 'Pure a) -> GraphEff u 'Pure ()
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

type NilU' = 'Graph '[] '[]

data Reader e where
    Ask :: Reader e
type instance Output (Reader e) = e

ask :: forall e u. GraphEff u ('Do (Reader e)) e
ask = send Ask

data Writer o where
    Tell :: o -> Writer o
    deriving (Show)

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
t1 = simpleEff $ do
    a <- ask @Int
    b <- ask @Float
    c <- ask @String
    return (a, b, c)

t2 :: GraphEff U ('Do (Reader Int) ':>>= 'TLeaf ('Do (Writer String))) Int
t2 = simpleEff $ do
    a <- ask @Int
    tell (show a)
    return (a + 1)

simpleEff :: GraphEff U i a -> GraphEff U i a
simpleEff a = a

auto :: ((GraphEff u i a -> GraphEff u ('Do (Call 0 a)) a) -> GraphEff u i a) -> GraphEff u i a
auto m = m undefined

tloop :: GraphEff u ('Do (Writer [Char]) ':<*> 'Do (Call 0 a)) a
tloop = auto $ \cc -> do
    tell "Foobar"
    cc tloop

data HVect (ts :: [*]) where
    HNil  :: HVect '[]
    (:&:) :: !t -> !(HVect ts) -> HVect (t ': ts)

newtype Tagged (t :: *) where Tagged :: TagData t -> Tagged t

instance Show (TagData t) => Show (Tagged t) where
    show (Tagged a) = show a

head :: HVect (t ': ts) -> t
head (a :&: b) = a

class HasTag t ts where
    getVec :: HVect ts -> TagData t
    putVec :: TagData t -> HVect ts -> HVect ts
    mutVec :: (TagData t -> TagData t) -> HVect ts -> HVect ts

instance {-# OVERLAPPING #-} HasTag t (Tagged t ': xs) where
    getVec   ((Tagged a) :&:  _) = a
    putVec a (        _  :&: xs) = (Tagged a) :&: xs
    mutVec f ((Tagged a) :&: xs) = (Tagged $ f a) :&: xs

instance {-# OVERLAPPABLE #-} HasTag t xs => HasTag t (Tagged t1 ': xs) where
    getVec   (a :&: xs) = getVec @t xs
    putVec a (b :&: xs) = b :&: putVec @t a xs 
    mutVec f (b :&: xs) = b :&: mutVec @t f xs

type family TagData (effect :: *) :: *

type instance TagData (Writer a) = [a]
type instance TagData (Reader e) = Output (Reader e)

mkTag :: forall effect. TagData effect -> Tagged effect
mkTag = Tagged

testVec = mkTag @(Writer String) ["Foobar"] :&: HNil

testGetter = getVec @(Writer String)

testVecGet = testGetter testVec

class HasAlg e es where
    getAlg :: HVect es -> EffectAlgebra' e

instance {-# OVERLAPPING #-} HasAlg e (EffectAlgebra' e ': xs) where
    getAlg (a :&:  _) = a

instance {-# OVERLAPPABLE #-} HasAlg e es => HasAlg e (EffectAlgebra' e' ': es) where
    getAlg (a :&: xs) = getAlg @e xs

type EffectAlgebra effect = forall s b. HasTag effect s => effect -> (Output effect -> b) -> (HVect s -> (b, HVect s))

newtype EffectAlgebra' effect where EffectAlgebra' :: EffectAlgebra effect -> EffectAlgebra' effect

-- algWriter :: forall o s b. HasTag (Writer o) s => (Writer o) -> (Output (Writer o) -> b) -> (HVect s -> (b, HVect s))
algWriter :: forall o. EffectAlgebra (Writer o)
algWriter (Tell o') q = \s -> (q (), mutVec @(Writer o) (o' :) s)

algReader :: forall e. EffectAlgebra (Reader e)
algReader (Ask) q = \s -> (q (getVec @(Reader e) s), s)

genWriter :: HVect ts -> HVect (Tagged (Writer o) ': ts)
genWriter = (Tagged [] :&:)

genReader :: e -> HVect ts -> HVect (Tagged (Reader e) ': ts)
genReader e = (Tagged e :&:)

genInit :: HVect '[]
genInit = HNil

class StepEffect i j e where
    step :: (HasTag e ts, HasAlg e algs) => HVect ts -> HVect algs -> GraphEff u i a -> GraphEff u j a

instance StepEffect 'Pure 'Pure e where
    step _ _ = id

instance StepEffect ('Do e) 'Pure e where
    step ts algs (E u q) = 
        let (EffectAlgebra' alg) = getAlg @e algs
        in V . fst $ ((alg u q) ts)

instance (FViewL j ~ r) => StepEffect ('Do e :>>= j) r e where
    step ts algs (B (E u f) q) = 
        let (EffectAlgebra' alg) = getAlg @e algs
        in case tviewl q of 
            TOne q' -> let r = fst $ (alg u f) ts in q' r

