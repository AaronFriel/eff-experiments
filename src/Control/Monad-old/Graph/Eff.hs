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
-- {-# LANGUAGE TemplateHaskell #-}
-- {-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

{-# LANGUAGE StrictData #-}

module Control.Monad.Graph.Eff where

import Control.Graphted
import Control.Monad.Graph.Internal.Eff
-- import Data.Singletons.TH
import Data.Kind (type (*))

import GHC.Types

data EffTree a = Pure | Do a | (EffTree a) :<*> (EffTree a) | EffTree a :>>= EffQueue a

data EffQueue a = TLeaf (EffTree a) | TNode (EffQueue a) (EffQueue a)  

infixl 1 :>>=
infixl 4 :<*>

type Handler = *
type Effect  = *

data Graph v = Graph {
    gpaths     :: [(Nat, EffTree v)],
    ghandlers  :: [(Effect, Handler)]
}

type U = 'Graph '[] '[]

type Arrs u i a b = FTCQueue (Eff u) i a b

data Eff (u :: Graph Effect) (i :: EffTree Effect) b where
    V :: b -> Eff u Pure b
    E :: ctor ->  (Output ctor -> b) -> Eff u (Do ctor) b
    -- TODO: Replace with alternate Arrs
    A :: Eff u i (a -> b) -> Eff u j a -> Eff u (i :<*> j) b
    B :: Eff u i a ->  Arrs u j a b -> Eff u (i :>>= j) b

instance KEffect (Eff u) where
    type Unit (Eff u) = 'Pure
    type Inv  (Eff u) i j = ()
    type Plus (Eff u) i j = GraphBind i j

instance Fmappable (Eff u) where
    type Fmap    (Eff u) i = GraphMap i

instance Applyable (Eff u) where
    type Apply (Eff u) i j = GraphAp i j

instance Bindable (Eff u) where
    type Bind  (Eff u) i j = GraphBind i j

type family GraphMap (i :: k) :: k where
    GraphMap   'Pure        = Pure
    GraphMap      (Do i)    = Do i 
    GraphMap  (i :<*> j)    = (GraphMap i) :<*> j
    GraphMap  (i :>>= j)    = i :>>= (TNode j (TLeaf Pure))

type family GraphAp (i :: k) (j :: k) :: k where
    GraphAp      Pure    k     = GraphMap k
    GraphAp  (i :<*> j) Pure   = (GraphMap i) :<*> j
    GraphAp  (i :>>= j) Pure   = i :>>= (TNode j (TLeaf Pure))
    GraphAp          i   Pure  = i
    GraphAp          i   k     = i :<*> k

type family GraphBind (i :: k) (j :: k) :: k where
    GraphBind        Pure  'Pure =  Pure
    GraphBind        Pure      k = k
    GraphBind  (x :>>= xs)     k = x :>>= (TNode xs (TLeaf k))
    GraphBind           i      k = i :>>= TLeaf k

instance KFunctor (Eff u) where
    {-# INLINE kmap #-}
    kmap f (V x) = V (f x)
    kmap f (E u q)  = E u (f . q)
    kmap f (A a as) = A (kmap (f .) a) as
    kmap f (B u q)  = B u (q |> (V . f))

instance KPointed (Eff u) where
    {-# INLINE kreturn #-}
    kreturn = V

instance KApplicative (Eff u) where
    {-# INLINE kap #-}
    V f `kap` m = kmap f m
    E u q `kap` k = case k of
      V x   -> E u (\o -> (q o) x)
      E _ _ -> A (E u q) k
      A _ _ -> A (E u q) k
      B _ _ -> A (E u q) k
    A i j `kap` k = case k of
      V x   -> A (kmap (\f -> flip f $ x) i) j
      E _ _ -> A (A i j) k
      B _ _ -> A (A i j) k
      A _ _ -> A (A i j) k
    B u q `kap` k = case k of
      V x   -> B u (q |> (V . ($ x)))
      E _ _ -> A (B u q) k
      B _ _ -> A (B u q) k
      A _ _ -> A (B u q) k

instance KMonad (Eff u) where
    {-# INLINE kbind #-}
    (V x)    `kbind` k = k x
    (E u q)  `kbind` k = B (E u q) (tsingleton k)
    (A a as) `kbind` k = B (A a as) (tsingleton k)
    (B u q)  `kbind` k = B u (q |> k)

instance KMonadFail (Eff u) where
    kfail = error

-- class type role FTCQueue representational phantom representational nominal
data FTCQueue m (i :: EffQueue Effect) a b where
        Leaf :: (a -> m i b) -> FTCQueue m (TLeaf i) a b
        Node :: FTCQueue m i a x -> FTCQueue m j x b -> FTCQueue m (TNode i j) a b

{-# INLINE tfmap #-}
tfmap :: (a -> m Pure b) -> FTCQueue m (TLeaf Pure) a b
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

{-# INLINE tviewl #-}
tviewl :: FTCQueue m i a b -> ViewL m (FViewL i) a b
tviewl (Leaf r) = TOne r
tviewl (Node t1 t2) = go SPEC t1 t2
    where
      {-# INLINABLE go #-}
      go :: SPEC -> FTCQueue m i a x -> FTCQueue m j x b -> ViewL m (FViewL' i j) a b
      go sPEC (Leaf r) tr = r :< tr
      go sPEC (Node tl1 tl2) tr = go sPEC tl1 (Node tl2 tr)

{-# INLINE send #-}
send :: ctor -> Eff u (Do ctor) (Output ctor)
send t = E t id



