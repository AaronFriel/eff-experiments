{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module Control.Monad.Graph.Eff where

import Control.Monad.Graph.Class
import Data.Kind (type (*))

data Tree a = Empty | Do a | (Tree a) :<*> (Tree a) | Tree a :>>= BindTree a
infixl 1 :>>=
infixl 4 :<*>

data BindTree a = TLeaf (Tree a) | TNode (BindTree a) (BindTree a)  

data Graph v = Graph {
    gpaths     :: [Tree v],
    ghandled   :: [v]
}

type U = 'Graph '[] '[]

type Effect  = *

type family Output e = r

type Arrs u i a b = FTCQueue (GraphEff u) i a b

data GraphEff (u :: Graph Effect) (i :: Tree Effect) b where
    V :: b -> GraphEff u Empty b
    E :: ctor ->  (Output ctor -> b) -> GraphEff u (Do ctor) b
    -- TODO: Replace with alternate Arrs
    A :: GraphEff u i (a -> b) -> GraphEff u j a -> GraphEff u (i :<*> j) b
    B :: GraphEff u i a ->  Arrs u j a b -> GraphEff u (i :>>= j) b

type family GraphMap (i :: k) :: k where
    GraphMap      Empty  = Empty
    GraphMap      (Do i) = Do i 
    GraphMap  (i :<*> j) = (GraphMap i) :<*> j
    GraphMap  (i :>>= j) = i :>>= (TNode j (TLeaf Empty))

type family GraphAp (i :: k) (j :: k) :: k where
    GraphAp      Empty       k = GraphMap k
    GraphAp  (i :<*> j)  Empty = (GraphMap i) :<*> j
    GraphAp  (i :>>= j)  Empty = i :>>= (TNode j (TLeaf Empty))
    GraphAp          i   Empty = i
    GraphAp          i       j = i :<*> j

type family GraphBind (i :: k) (j :: k) :: k where
    GraphBind        Empty  Empty =  Empty
    GraphBind        Empty      j = j
    GraphBind  (x :>>= xs)      j = x :>>= (TNode xs (TLeaf j))
    GraphBind           i       j = i :>>= TLeaf j

instance GFunctor (GraphEff u) where
    type Mapish j = GraphMap j
    gmap f (V x)    = V (f x)
    gmap f (E u q)  = E u (f . q)
    gmap f (A a as) = A (gmap (f .) a) as
    gmap f (B u q)  = B u (q |> (V . f))

instance GPointed i (GraphEff u) where
    type EmptyishC i = i ~ Empty 
    greturn = V

instance GApplicative j (GraphEff u) where
    type Apish i j = GraphAp i j
    type ApishC i j = ()

    V f `gap` m = gmap f m
    E u q `gap` k = case k of
      V x   -> E u (\o -> (q o) x)
      E _ _ -> A (E u q) k
      A _ _ -> A (E u q) k
      B _ _ -> A (E u q) k
    A i j `gap` k = case k of
      V x   -> A (gmap (\f -> flip f $ x) i) j
      E _ _ -> A (A i j) k
      B _ _ -> A (A i j) k
      A _ _ -> A (A i j) k
    B u q `gap` k = case k of
      V x   -> B u (q |> (V . ($ x)))
      E _ _ -> A (B u q) k
      B _ _ -> A (B u q) k
      A _ _ -> A (B u q) k

instance GMonad j (GraphEff u) where
    type Bindish i j = GraphBind i j
    type BindishC i j = ()

    k `gbind` (V x)    = k x
    k `gbind` (E u q)  = B (E u q) (tsingleton k)
    k `gbind` (A a as) = B (A a as) (tsingleton k)
    k `gbind` (B u q)  = B u (q |> k)

-- type role FTCQueue representational phantom representational nominal
data FTCQueue m (i :: BindTree Effect) a b where
        Leaf :: (a -> m i b) -> FTCQueue m (TLeaf i) a b
        Node :: FTCQueue m i a x -> FTCQueue m j x b -> FTCQueue m (TNode i j) a b

{-# INLINE tfmap #-}
tfmap :: (a -> m Empty b) -> FTCQueue m (TLeaf Empty) a b
tfmap r = Leaf r

{-# INLINE tsingleton #-}
tsingleton :: (a -> m i b) -> FTCQueue m (TLeaf i) a b
tsingleton r = Leaf r

-- snoc: clearly constant-time
{-# INLINE (|>) #-}
(|>) :: FTCQueue m i a x -> (x -> m j b) -> FTCQueue m (TNode i (TLeaf j)) a b
t |> r = Node t (Leaf r)

-- append: clearly constant-time
{-# INLINE (><) #-}
(><) :: FTCQueue m i a x -> FTCQueue m j x b -> FTCQueue m (TNode i j) a b
t1 >< t2 = Node t1 t2

data ViewL m i a b where
    TOne :: (a -> m i b) -> ViewL m i a b
    (:<) :: (a -> m i x) -> (FTCQueue m j x b) -> ViewL m (i :>>= j) a b

type family FViewL' i j where
    FViewL' (TLeaf r)       tr = r :>>= tr
    FViewL' (TNode tl1 tl2) tr = FViewL' tl1 (TNode tl2 tr)

type family FViewL i where
    FViewL (TLeaf r)       = r
    FViewL (TNode tl1 tl2) = FViewL' tl1 tl2

tviewl :: FTCQueue m i a b -> ViewL m (FViewL i) a b
tviewl (Leaf r) = TOne r
tviewl (Node t1 t2) = go t1 t2
    where
      go :: FTCQueue m i a x -> FTCQueue m j x b -> ViewL m (FViewL' i j) a b
      go (Leaf r) tr = r :< tr
      go (Node tl1 tl2) tr = go tl1 (Node tl2 tr)

send :: ctor -> GraphEff u (Do ctor) (Output ctor)
send t = E t id

-- type family BindView i where
--     BindView (TLeaf r)       = r
--     BindView (TNode tl1 tl2) = BindView' tl1 tl2

-- type family BindView' i where
--     BindView (TLeaf r)       tr = r :>>= tr
--     BindView (TNode tl1 tl2) tr = FViewL' tl1 tl2
