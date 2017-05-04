{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE ExplicitNamespaces     #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StrictData             #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module Control.Eff.Internal.Eff where

import Control.Eff.Internal.FTCQueue
import Control.Eff.Internal.Types

import Control.Graphted hiding (Pure, Zero)
import Prelude.Graphted

import GHC.Types

data Graph v = Graph {
    gpaths    :: [(Nat, EffTree v)],
    ghandlers :: [(Effect, Handler)]
}

type U = 'Graph '[] '[]

type Arrs u i a b = FTCQueue (Eff u) i a b

data Eff (u :: Graph Effect) (i :: EffTree Effect) b where
    Z :: ctor -> Eff u ('Zero i) a
    V :: b -> Eff u 'Pure b
    E :: ctor -> Eff u (Do ctor) (EffectResult ctor)
    F :: Eff u i a -> (a -> b) -> Eff u ('Fmapped i) b
    -- TODO: Replace with alternate Arrs
    A :: Eff u i (a -> b) -> Eff u j a -> Eff u (i :<*> j) b
    B :: Eff u i a -> Arrs u j a b -> Eff u (i :>>= j) b
    O :: Eff u i a -> Eff u j a -> Eff u (i :<|> j) a

instance Graphted (Eff u) where
    type Unit (Eff u) = 'Pure
    type Inv  (Eff u) i j = ()
    type Combine (Eff u) i j = GraphBind i j

-- Closed type families, which allow overlapping:
type family GraphMap (i :: k) :: k where
    GraphMap        Pure  = Pure
    GraphMap       (Do i) = Fmapped (Do i)
    GraphMap  (Fmapped i) = Fmapped i
    GraphMap   (i :<*> j) = (GraphMap i) :<*> j
    GraphMap   (i :>>= j) = i :>>= ('TNode j ('TLeaf 'Pure))
    GraphMap   (i :<|> j) = (GraphMap i :<|> GraphMap j)
    GraphMap     (Zero i) = Zero i

type family GraphAp (i :: k) (j :: k) :: k where
    GraphAp       Pure       k   = GraphMap k
    GraphAp      (Do i)      k   = Do i :<*> k
    GraphAp   (Zero i)       k   = Zero i
    GraphAp (Fmapped i)   Pure   = Fmapped i
    GraphAp  (i :<*> j)   Pure   = (GraphMap i) :<*> j
    GraphAp  (i :>>= j)   Pure   = i :>>= (TNode j (TLeaf Pure))
    GraphAp  (i :<|> j)   Pure   = (GraphMap i) :<|> (GraphMap j)
    GraphAp          i    Pure   = i
    GraphAp          i (Zero k)  = Zero k
    GraphAp          i       k   = i :<*> k

type family GraphBind (i :: k) (j :: k) :: k where
    GraphBind        Pure   Pure  =  Pure
    GraphBind        Pure      k  = k
    GraphBind  (x :>>= xs)     k  = x :>>= (TNode xs (TLeaf k))
    GraphBind   (i :<|> j)     k  = (GraphBind i k) :<|> (GraphBind j k)
    GraphBind     (Zero i)     k  = Zero i
    GraphBind           i      k  = i :>>= TLeaf k

instance GFunctor (Eff u) where
    type Fmap    (Eff u) i = GraphMap i

    {-# INLINE gmap #-}
    gmap _ (Z u)    = Z u
    gmap f (V x)    = V (f x)
    gmap f (E u)    = F (E u) f
    gmap f (F m g)  = F m (f . g)
    gmap f (A a as) = A (gmap (f .) a) as
    gmap f (B u q)  = B u (q |> (V . f))
    gmap f (O a b)  = O (gmap f a) (gmap f b)

instance GPointed (Eff u) where
    {-# INLINE gpure #-}
    gpure = V

    -- gpure' :: forall t a. PureCxt f t => a -> f t a
    gpure' = undefined

instance GApplicative (Eff u) where
    type Apply (Eff u) i j = GraphAp i j

    {-# INLINE gap #-}

    Z u `gap` _ = Z u
    V f `gap` k = gmap f k
    F a h `gap` k = case k of
      Z u   -> Z u
      V x   -> F a (\a1 -> (h a1) x)
      E _   -> A (F a h) k
      F _ _ -> A (F a h) k
      A _ _ -> A (F a h) k
      B _ _ -> A (F a h) k
      O _ _ -> A (F a h) k
    E u `gap` k = A (E u) k
    A i j `gap` k = case k of
      Z u   -> Z u
      V x   -> A (gmap (\f -> flip f $ x) i) j
      E _   -> A (A i j) k
      F _ _ -> A (A i j) k
      A _ _ -> A (A i j) k
      B _ _ -> A (A i j) k
      O _ _ -> A (A i j) k
    B u q `gap` k = case k of
      Z u'  -> Z u'
      V x   -> B u (q |> (V . ($ x)))
      E _   -> A (B u q) k
      F _ _ -> A (B u q) k
      A _ _ -> A (B u q) k
      B _ _ -> A (B u q) k
      O _ _ -> A (B u q) k
    O a b `gap` k = case k of
      Z u   -> Z u
      V x   -> O (gmap ($ x) a) (gmap ($ x) b)
      E _   -> A (O a b) k
      F _ _ -> A (O a b) k
      B _ _ -> A (O a b) k
      A _ _ -> A (O a b) k
      O _ _ -> A (O a b) k

instance GMonad (Eff u) where
    type Bind  (Eff u) i j = GraphBind i j

    {-# INLINE gbind #-}
    (Z u)    `gbind` _ = Z u
    (V x)    `gbind` k = k x
    (E u)    `gbind` k = B (E u) (tsingleton k)
    (F a h)  `gbind` k = B (F a h) (tsingleton k)
    (A a as) `gbind` k = B (A a as) (tsingleton k)
    (B u q)  `gbind` k = B u (q |> k)
    (O a b)  `gbind` k = O (a `gbind` k) (b `gbind` k)

-- TODO: Nondeterminism
instance GMonadZero (Eff u) where
    gzero = undefined

instance GMonadOr (Eff u) where
    type Or  (Eff u) i j = i :<|> j

    gorelse m k = O m k

instance GMonadFail (Eff u) where
    gfail = error

{-# INLINE send #-}
send :: ctor -> Eff u (Do ctor) (EffectResult ctor)
send t = E t

newtype Exc t a where Exc :: t -> Exc t a

type instance EffectResult (Exc t a) = a

data TestExc = TestExc

ifThenElse :: Bool -> t -> t -> t
ifThenElse True  a _ = a
ifThenElse False _ b = b

excep :: ctor -> Eff u j a -> Eff u ('Zero ctor :<|> j) a
excep a b = (<|>) (Z a) b
