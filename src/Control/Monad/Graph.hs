{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- For unsafeSizeof
{-# LANGUAGE MagicHash, UnboxedTuples #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RoleAnnotations #-}

{-# OPTIONS_GHC -funbox-strict-fields #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors -Wno-missing-signatures -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Control.Monad.Graph where


import Data.Promotion.Prelude
import Data.Promotion.Prelude.Eq

import Data.Singletons
import Data.Singletons.Decide
import Data.Singletons.Prelude
import Data.Singletons.TH
import Data.Singletons.TypeLits
import Data.Type.Equality
import Data.List.NonEmpty

import Data.Typeable
import Data.Kind (Constraint, type (*), type Type)
import Data.Proxy (Proxy)
import GHC.TypeLits hiding (type (*))
import GHC.Prim (proxy#, Proxy#, type TYPE, coerce)
import GHC.Types (RuntimeRep (..))
import           Unsafe.Coerce               (unsafeCoerce)
-- import Control.Monad (join)
import Control.Monad.Indexed
import Data.Singletons.TypeRepStar
import Data.HVect hiding (Nat)

import qualified Debug.Trace as Debug

$(genPromotions [''NonEmpty])

$(promoteOnly [d|
  (<|) :: a -> NonEmpty a -> NonEmpty a
  a <| (b :| bs) = (a :| (b : bs))
  |])

$(singletons [d|
  data Tree a = Empty | Do a | Aps (Tree a) [Tree a] | Tree a :>>= Tree a
    deriving (Eq, Typeable)

  |])
infixl 4 :>>=

$(promote [d|

  data Graph v = Graph {
      ixpaths      :: [Tree v],
      ixeffects    :: [[v]]
    }

  emptyU = Graph []
  |])

type Effect  = *

type family Output e = r

type Arrs u i a b = FTCQueue (GraphEff u) i a b

-- type family Fn xs where
--   Fn '[GraphEff u i Empty (a -> w), GraphEff u j Empty a] = a -> w
--   Fn (GraphEff u i Empty b ': r) = b -> Fn r

-- type family Result xs where
--   Result '[GraphEff u i Empty (a -> w), GraphEff u j Empty a] = (a -> w)
--   Result (GraphEff u i Empty b ': r) = Result r

-- type family AddAp i j k where
--   AddAp (Aps f as) (Do ctor)

class FreeApplicative (xs :: [*]) where
  type Vect xs
  testFA :: HVect xs -> String

-- class SharedU' u a => SharedU u a

-- type family GraphOf m where
--   GraphOf (GraphEff u i 'Empty a) = u

-- type family SharedU' u g where
--   SharedU' u (GraphEff u' i 'Empty a) = u ~ u'

data T = T
type Trivial = 'T ~ 'T

-- Option A: Big set of constraints on HVect xs.
-- This leaves free only the tree parameter.
-- type family IsApplicative f xs (r :: *) :: Constraint where
--   IsApplicative (GraphEff u i (x' -> w)) (GraphEff u1 i1 y1 ': ys) r = (u ~ u1, x' ~ y1, IsApplicative (GraphEff u i w) ys r)
--   IsApplicative (GraphEff u i        w)                       '[]  r = (w ~ r)

-- type family BuildAps i0 xs tree :: Constraint where
--   BuildAps i0 (GraphEff _ i1 _ ': ys) tree = tree ~ (Aps i0 (i1 ':| CollectTrees ys))

-- type family CollectTrees xs where
--   CollectTrees (GraphEff _ i _ ': ys) = i ': CollectTrees ys
--   CollectTrees                 '[]  = '[]

-- type family CollectAps xs where
--   CollectAps (GraphEff _ i _ ': ys) = i :| CollectTrees ys

-- type family BuildFn r xs where
--   BuildFn r (GraphEff _ _ a ': ys) = a -> (BuildFn r ys)
--   BuildFn r                    '[] = r

-- type family ReduceFn w xs where
--   ReduceFn (a -> w) (GraphEff _ _ a ': ys) = BuildFn w ys
--   ReduceFn       w                    '[] = w

-- Option B: Injective type function to define HVect xs _from_ a list of trees and arguments
type family ApVect u i w args = xs | xs -> u i  args where
  ApVect u i (w -> r) (t1 ': ts) = GraphEff u i r  ': ApVect' u (w -> r) (t1 ': ts)

type family ApVect' u w tree_args = xs | xs -> tree_args where
  ApVect' u (yk -> w) ( '(ik, yk) ': ts ) = GraphEff u ik yk ': ApVect' u (yk -> w)  ts
  ApVect' u        w                '[]   = '[]

-- type family ApTrees i tree_args where
--   ApTrees i0 ( '(i1, _) ': is ) = Aps i0 (i1 :| ApTrees' is)

-- type family ApTrees' tree_args where
--   ApTrees' ( '(ik, yk) ': ts ) = ik ': ApTrees' ts
--   ApTrees'               '[]   = '[]

-- type family ApplicativeVect u xs = ys | ys -> u xs where
--   ApplicativeVect u ( '(i0, r) ': '(j1, y1) ': r) =  '[GraphEff u i0 'Empty (y1 -> r), GraphEff u j1 'Empty y1]
--   ApplicativeVect u '[ '(i0, r), '(j1, y1)] = '[GraphEff u i0 'Empty (y1 -> r), GraphEff u j1 'Empty y1]

-- type family ApplicativeVect js where
--   ApplicativeVect ()

-- instance FreeApplicative '[ GraphEff u i 'Empty (a -> w), GraphEff u j 'Empty a] where
--   type Vect '[GraphEff u i 'Empty (a -> w), GraphEff u j 'Empty a] = HVect '[GraphEff u i 'Empty (a -> w), GraphEff u j 'Empty a]
--   testFA _ = "Foobar"

-- instance (FreeApplicative r, Fn r ~ (b -> w)) => FreeApplicative (GraphEff u i Empty b ': r) where

-- type family GetTree g where
--   GetTree (GraphEff u i Empty w) = i

-- type family GetAps as where
--   GetAps (GraphEff u i Empty (a -> b) : GraphEff u j Empty a : r) = Aps i (j :| GetApTail r)

-- type family GetApTail as where
--   GetApTail      '[]  = '[]
--   GetApTail (a ': as) = GetTree a ': GetApTail as

data GraphEff (u :: Graph Effect) (i :: Tree Effect) b
  where
    V :: b -> GraphEff u Empty b
    E :: ctor ->  (Output ctor -> b) -> GraphEff u (Do ctor) b
    A :: !(GraphEff u i0 (MakeF rs r)) -> GVect u is rs -> (r -> w) -> GraphEff u (Aps i0 is) w
    B :: GraphEff u i a ->  Arrs u j a b -> GraphEff u (i :>>= j) b

-- testIap :: GraphEff u i1 String -> GraphEff u i2 String -> GraphEff u (Aps Empty (i1 :| '[i2])) (String, String)
-- testIap lhs rhs = A (V (,)) (lhs :&: rhs :&: HNil)

-- testIap1 = E (Ask @Double) (tsingleton (\a -> A (V (\b c -> (a,b,c))) (E (Ask @String) (tsingleton V) :&: E (Ask @Int) (tsingleton V) :&: HNil)))
-- testIap2 = A (V (,)) (E (Ask @String) (tsingleton V) :&: HNil) (tsingleton V)

-- testIap3 = case testIap2 of
--   A _ as q -> A (V (,)) (E (Ask @Int) (tsingleton V) :&: as) q

type family GraphAp (i :: k) (j :: k) :: k where
  GraphAp           (Do ctor)  Empty  = Do ctor
  GraphAp           (Do i)     (Do j) = Aps (Do i) '[Do j]
  GraphAp           (Do i) (Aps f as) = Aps (Do i) '[Aps f as]
  GraphAp           (Do i) (j :>>= k) = Aps (Do i) '[j :>>= k]
  GraphAp       (ctor :>>= i)      j  = ctor :>>= (GraphAp i j)
  GraphAp          (Aps f as)      Empty = Aps f (as :++ '[Empty])
  GraphAp          (Aps f as)     (Do j) = Aps f (as :++ '[Do j])
  GraphAp          (Aps f as) (Aps f as) = Aps f (as :++ '[Aps f as])
  GraphAp          (Aps f as) (j :>>= k) = Aps f (as :++ '[j :>>= k])
  GraphAp               Empty  Empty  = Empty
  GraphAp               Empty      j  = j

-- type family GraphBind (i :: k) (j :: k) :: k where
--   GraphBind           Empty       Empty = Empty
--   GraphBind           Empty           j = j
--   GraphBind               i       Empty = i
--   GraphBind      (x :>>= xs)          j = x :>>= (GraphBind xs j)
--   GraphBind       (Aps f as)          j = (Aps (GraphBind f j) as)

class GFunctor (f :: k -> * -> *) where
    gmap :: (a -> b) -> f p a -> f p b

class GFunctor f => GPointed p (f :: k -> * -> *) where
    type EmptyishC (p :: k) :: Constraint
    greturn :: EmptyishC p => a -> f p a

class GPointed p f => GApplicative p (f :: k -> * -> *) where
    type ApishC (i :: k) (j :: k) :: Constraint
    type Apish (i :: k) (j :: k) :: k
    gap :: ApishC (i :: k) (j :: k) => f i (a -> b) -> f j a -> f (Apish i j) b

class GApplicative p m => GMonad p (m :: k -> * -> *) where
    type BindishC (i :: k) (j :: k) :: Constraint
    type Bindish (i :: k) (j :: k) :: k
    gbind :: BindishC (i :: k) p => (a -> m p b) -> m i a -> m (Bindish i p) b

data WrappedMonad m i a where
  WrappedMonad :: m a -> WrappedMonad m () a

-- instance Functor f => GFunctor i (WrappedMonad f) where
--     gmap f (WrappedMonad m) = WrappedMonad $ fmap f m

-- instance Applicative f => GPointed (WrappedMonad f) where
--   greturn a = WrappedMonad (pure a)

-- instance Applicative f => GApplicative (WrappedMonad f) where
--   type Apish (WrappedMonad f) () () = ()
--   gap (WrappedMonad u) (WrappedMonad v) = WrappedMonad (u <*> v)

-- instance Monad m => GMonad (WrappedMonad m) where
--   type Bindish (WrappedMonad m) () j = ()
--   k `gbind` (WrappedMonad m) = WrappedMonad (m >>= (\(WrappedMonad m') -> m') . k)

data WrappedIx m p a where
  WrappedIx :: m i j a -> WrappedIx m (i, j) a

unwrap :: WrappedIx m (i, j) a -> m i j a
unwrap (WrappedIx m) = m

unwrapL :: (a -> WrappedIx m (i, j) b) -> (a -> m i j b)
unwrapL k = (\a -> unwrap $ k a)

liftBind :: IxMonad m => WrappedIx m (i, j) a -> (a -> WrappedIx m (j, k) b) -> WrappedIx m (i, k) b
liftBind m k = WrappedIx $ ibind (unwrapL k) (unwrap m)

class GWrapped w f p where
  data Wrapped w f p
  -- type UnwrappedArg w f (p :: pk) = (r :: * -> *) | r -> w f p
  -- type WrappedArg w f (p :: pk) = (r :: * -> *) | r -> w f p
  -- unwrap :: (w f (p :: pk)) a -> (UnwrappedArg w f p) a
  -- wrap :: (UnwrappedArg w f p) a -> WrappedArg w f p a

-- instance GWrapped WrappedIx m '(i, j) where
--   data Wrapped WrappedIx m '(i, j) = Wrapped (m i j)
--     type UnwrappedArg WrappedIx m '(i, j) = m i j
--     type WrappedArg WrappedIx m '(i, j) = WrappedIx m '(i, j)
--     unwrap (WrappedIx m) = m
--     wrap m = WrappedIx m

instance IxFunctor f => GFunctor (WrappedIx f) where
    gmap :: forall a b p. (a -> b) -> WrappedIx f p a -> WrappedIx f p b
    gmap f (WrappedIx m) = WrappedIx (imap @f @a @b f m)

instance IxPointed f => GPointed (i, j) (WrappedIx f) where
    type EmptyishC (i, j) = (i ~ j)
    greturn a = WrappedIx $ ireturn a

instance IxApplicative f => GApplicative (i, j) (WrappedIx f) where
  type ApishC (i, j1) (j2, k) = (j1 ~ j2)
  type Apish (i, j1) (j2, k) = (i, k)
  gap (WrappedIx u) (WrappedIx v) = WrappedIx (iap u v)

instance IxMonad m => GMonad (j2, k) (WrappedIx m) where
  type BindishC (i, j1) (j2, k) = (j1 ~ j2)
  type Bindish (i, j1) (j2, k) = (i, k)
  k `gbind` (WrappedIx m) = WrappedIx $ (\a -> (case k a of WrappedIx k' -> k')) `ibind` m

-- class DeepAp i where
--   deepAp :: (a -> b) -> GraphEff u i a -> GraphEff u i b
  
-- instance DeepAp (ctor :>>= j) where
--   deepAp :: (a -> b) -> GraphEff u (ctor :>>= j) a -> GraphEff u (ctor :>>= j) b
--   deepAp f (E u q) = E u (q |> (V . f))
  
-- instance DeepAp (ctor :>>= j) => DeepAp (Aps (ctor :>>= j) (a1 :| '[])) where
--   -- deepAp :: (a -> b) -> GraphEff u (ctor :>>= j) a -> GraphEff u (ctor :>>= j) b
--   deepAp f (A a@(E u q) as@(_)) = A (E u (q |> (V . f))) as

instance GFunctor (GraphEff u) where
    gmap f (V x)    = V (f x)
    gmap f (E u q)  = E u (f . q)
    gmap f (A a as q) = A a as (f . q)

instance GPointed i (GraphEff u) where
    type EmptyishC i = i ~ 'Empty 
    greturn = V

instance GApplicative j (GraphEff u) where
    type Apish i j = GraphAp i j
    type ApishC i j = ()

    V f `gap` V x   = V $ f x
    V f `gap` E u q = E u (f . q)
    V f `gap` A a as q = A a as (f . q)
    V f `gap` B u q = B u (q |> (V . f))
-- --     -- -- V f@(_) `gap` A u@(_) q = A (V f :&: u) (coerce q)
    E u q `gap` m  = case m of
      V x     -> E u (\o -> (q o) x)
      E _ _   -> A (E u q) (m :<&> GNil) id
      A _ _ _ -> A (E u q) (m :<&> GNil) id
      B _ _   -> A (E u q) (m :<&> GNil) id
    -- A a@(_) as@(_) q `gap` V y = A (GraphEff u i (MakeF rs (a -> b)) (apqappend as (V y)) undefined
    -- E u q `gap` A a as r = A (E u q) (A a as r :<&> GNil) id
    -- E u q `gap` B v r  = A (E u q) (B v r :<&> GNil) id
    -- A a as q `gap` V x = A a as (\o -> (q o) x)
    -- A a as q `gap` V x = A a as (\o -> (q o) x)
--     E u q `gap` m      = E u (q |> undefined)
    -- A a as q `gap` m   = 
--     -- B u q `gap` m   = B u (q ||> (`gmap` m))

-- (<|*|>) :: forall u i0 is a b ik. GraphEff u (Aps i0 is) (a -> b) -> GraphEff u ik a -> GraphEff u (Aps i0 (is :++ '[ik])) b
-- (A f@(_) vec@(_) q@(_)) <|*|> g = case (f, vec, q) of
--   (_ :: GraphEff u i0 (MakeF rs (a -> r)), _ :: GVect u is rs, _ :: (_ -> (a -> b))) -> A undefined undefined undefined -- A (f) (apqappend vec g) undefined

-- instance GMonad (GraphEff u) where
--     type Bindish (GraphEff u) i j = GraphBind i j
--     gbind :: (a -> GraphEff u j b) -> GraphEff u i a -> GraphEff u (GraphBind i j) b
--     k `gbind` (V x) = k x
    -- k `gbind` m@(E u@(_) q@(_)) = (E u undefined)
-- If we define GraphEff like this, then the type roles of i, j are nominal, and `coerce` fails.
-- data ViewEff (u :: Graph Effect) (j :: Tree Effect) b
--   where
--     ViewV :: b -> ViewEff u Empty b
--     ViewE :: ctor -> Arrs u (Output ctor) b -> ViewEff u (Do ctor :>>= k) b

-- class View j where
--   view :: GraphEff u 'Empty j b -> ViewEff u j b

-- instance View 'Empty where
--   view (V x)   = ViewV x
--   view (E _ _) = error "Impossible."

-- instance View (Do ctor :>>= k)  where
--   view (E u q) = ViewE (unsafeCoerce u) (unsafeCoerce q)
--   view (V _)   = error "Impossible."

-- (||>) :: Arrs u i a x -> (x -> GraphEff u i b) -> Arrs u i a b
-- t ||> r = Node (coerce t) (Leaf (coerce r))


type family LookupEffect' (efx :: [*]) (e :: *) = (r :: Nat) where
  LookupEffect' (e ': efx) e = 0
  LookupEffect' (u ': efx) e = 1 + LookupEffect' efx e

-- type family LabelAps (efx :: [*]) (as :: [Tree *]) = (r :: [Tree Nat]) where
--   LabelAps efx '[]       = '[]
--   LabelAps efx (t ': ts) = LabelTree efx t ': LabelAps efx ts

-- type family LabelTree (efx :: [*]) (e :: Tree *) = (r :: Tree Nat) where
--   LabelTree efx     Empty       = Empty
--   LabelTree efx (    Do a)      = Do (LookupEffect' efx a)
--   LabelTree efx (a :>>= b)      = LabelTree efx a :>>= LabelTree efx b
--   LabelTree efx (  Aps as)      = Aps (LabelAps efx as)

-- type family DecompG m e where
--    DecompG (GraphEff ('Graph ps efx) i a) e = GraphEff ('Graph ps efx) (LabelTree efx e) a

data TraceProxy

newtype Trace = Trace String

data Ask r = Ask

data Get s = Get
data Put s = Put !s

-- send :: forall ctor u. ctor -> GraphEff u (Do ctor) Empty (Output ctor)
-- -- send t = E t (coerce $ tsingleton V)
-- send = undefined

-- seal :: GraphEff u j 'Empty a -> GraphEff u j 'Empty a
-- seal = id

-- ask :: forall r u j k. GraphEff u (Do (Ask r) :>>= j) k r
-- ask = send $ Ask @r

-- get :: forall s u j k. GraphEff u (Do (Get s) :>>= j) k s
-- get = send $ Get @s

-- type family FindIdx u j where
--   FindIdx u j = 0

-- type family AddFn u j where
--   FindIdx u j = u

-- put s = send $ Put s

type instance Output (Ask r) = r
type instance Output (Put s) = ()
type instance Output (Get r) = r

-- newtype Get r v = Get { get :: (v -> r) -> r }
-- newtype Put r v = Put { put :: (() -> r) -> r }
-- send' :: forall (ctor :: TYPE k) u. GraphEff u (Do (TreeRep ctor) :>>= Empty) (Output ctor)
-- send' = B' (const V)

-- gmap :: (a -> b) -> GraphEff u i a -> GraphEff u i b
-- -- gmap f (B' k)  = B' (gmap f . k)
-- gmap f (V x)   = V (f x)
-- gmap f (B u q) = B u (q |> (V . f))
-- gmap f (A m k) = A (gmap (f .) m) k

-- greturn :: a -> GraphEff u Zeroish a
-- greturn = V

-- decomp :: MonadEff k u i a ->

-- pjoin m = m |>= id

    -- (f <*> pure x1) >>= k
    -- (f <*> )


    -- bindish  (Aps f (a1 :| []))     j = Aps f ((bindish a1 j) :| [])
    -- bindish  (Aps f (a1 :| as))     j = Aps f (a1 :| go as)
    --   where
    --     go (b : []) = [bindish b j]
    --     go (b : bs) = b : go bs

-- m   |>= k = B m k

-- (|>=) :: GraphEff u i a -> (a -> GraphEff u j b) -> GraphEff u (Bindish i j) b
-- V x       |>= k = k x
-- m@(B u@(_) q@(_)) |>= k = B u (q |> k)

-- (<|*|>) :: GraphEff u i (a -> b) -> GraphEff u j a -> GraphEff u (Apish i j) b
-- V f       <|*|> k       = gmap f k
-- m         <|*|> V x     = gmap ($ x) m
-- -- Type familiy Apish requires we prove all patterns.
-- i@(B _ _) <|*|> j@(A _ _) = A i j
-- i@(B _ _) <|*|> j@(B _ _) = A i j
-- i@(A _ _) <|*|> j@(A _ _) = A i j
-- i@(A _ _) <|*|> j@(B _ _) = A i j

-- m@(A f as) <|*|>   j = case as of
--   a1@(E _ _) -> case a1 of
--     (a1' :: GraphEff _ a1i (a0)) -> case f of
--       f'@(E _ _) -> case f' of
--         (_ :: GraphEff _ fi (a0 -> a -> b)) -> case j of
--           j'@(E _ _) -> case j' of
--             (_ :: GraphEff _ ji a) -> A (A f as) j

-- m     <|*|> k   = A m k


data Val k (v :: k) = Var
-- t1, t1' :: Monad f => f a1 -> (a1 -> f (a -> b)) -> f a -> f b
-- t1 a b c = (a >>= b) <*> c

-- t1' a b c = a >>= (\x -> (b x) <*> c)

-- t2, t2' :: Monad f => f a2 -> (a2 -> f (a1 -> b)) -> f (a -> a1) -> f a -> f b
-- t2 a b c d = (a >>= b) <*> (c <*> d)

-- t2' a b c d = a >>= (\x -> (b x) <*> (c <*> d))

-- -- t3, t3' :: Monad f => f a2 -> (a2 -> f (a1 -> b)) -> f (a -> a1) -> f a -> f b
-- t3, t3' :: Monad f => f a3 -> (a3 -> f a2) -> (a2 -> f (a1 -> b)) -> f (a -> a1) -> f a -> f b
-- t3 a b c d e = (a >>= b >>= c) <*> (d <*> e)

-- t3' a b c d e = (a >>= b >>= (\x -> (c x) <*> (d <*> e)))

-- t4, t4'
--   :: Monad f =>
--      f a3
--      -> (a3 -> f a2) -> (a2 -> f (a1 -> a -> b)) -> f a1 -> f a -> f b
-- t4 a b c d e = (a >>= b >>= c) <*> d <*> e

-- t4' a b c d e = (a >>= b >>= (\x -> c x <*> d <*> e))

-- t5, t5' :: Monad m => m (a2 -> a1 -> a) -> m a2 -> m a1 -> (a -> m b) -> m b
-- t5 a b c d = (a <*> b <*> c) >>= d
-- -- t5' a b c d e f = (a <*> b <*> c) >>=

-- t5' a b c d = join $ pure (\f -> \a2 a1 -> d (f a2 a1)) <*> a <*> b <*> c
-- t7' a b c d e = join $ pure (\f -> \a2 -> \a1 -> d (f a2 a1) >>= e) <*> a <*> b <*> c



-- p1_1 a b = a >>= b
-- p1_1' a b = join $ pure (\f -> b f) <*> a

-- p1_2, p1_2' :: Monad m => m (a1 -> a) -> m a1 -> (a -> m b) -> m b
-- p1_2 a b c = (a <*> b) >>= c

-- p1_2' a b c = join $ pure (\f a1 -> c (f a1)) <*> a <*> b

-- -- p1_3, p1_3' :: Monad m => m (a2 -> a1 -> a) -> m a2 -> m a1 -> (a -> m b) -> m b
-- -- p1_3 a b c d = (a <*> b <*> c) >>= d
-- -- p1_3' a b c d = join $ pure (\f a1 -> d (f a1)) <*> a <*> b <*> c

-- p1_4 a b c d e  = (a <*> b <*> c <*> d) >>= e

-- -- t7, t7' :: Monad m => m (x2 -> x1 -> a) -> m x2 -> m x1 -> (a -> m b) -> (b -> m c) -> m c
-- t7 a b c d e = (a <*> b <*> c) >>= d >>= e

-- -- t6, t6' :: Monad m => m (a4 -> a3 -> a2) -> m a4 -> m a3 -> (a2 -> a1) -> (a1 -> a2 -> a) -> (a -> a2 -> m b) -> m bt5
-- t6, t6' :: Monad f => f (a4 -> a3 -> a2 -> b) -> f a4 -> f a3 -> f a1 -> (a1 -> f a) -> (a -> f a2) -> f b
-- t6 a b c d e f = (a <*> b <*> c) <*> (d >>= e >>= f)

-- t6' a b c d e f = a <*> b <*> c <*> (d >>= e >>= f)

-- decomp :: forall e ps efx i a. GraphEff ('Graph ps efx) (i :: Tree *) a -> GraphEff ('Graph ps efx) (LabelTree efx i) a
-- decomp = coerce


-- data Writer (e :: *) (v :: *) where
--   Writer :: o -> Writer o ()

-- data State (s :: *) (v :: *) where
--   Get :: State s s
--   Put :: s -> State s ()

-- newtype Exc (e :: *) (v :: *) = Exc e

-- data Trace v where
--   Trace :: String -> Trace ()



-- Non-empty tree. Deconstruction operations make it more and more
-- left-leaning

data GVect u i b where
  GNil   :: GraphEff u i (a -> b) -> GVect u (Aps i '[]) (a -> b)
  -- (:<&>) :: !(GVect u (Aps i0 is) (a->b)) -> !(GraphEff u i a) -> GVect u (Aps i0 (i :++ is)) (r ': rs) 
infixr 5 :<&>

-- apqappend :: GVect u is rs -> GraphEff u i r -> GVect u (is :++ '[i]) (rs :++ '[r])
-- apqappend      GNil  m = m :<&> GNil
-- apqappend (a :<&> b) m = a :<&> (apqappend b m)

-- gviewL :: GVect u ( '( 'Empty, a) ': '(i1, b) ': xs) -> (a -> w) -> (GVect u ( '(i1, b) ': xs ), w)
-- gviewL (V a :<&> b) f = (b, f a)

-- type family MakeF xs w where
--   MakeF '[] w = w
--   MakeF ( a ': xs ) w = a -> MakeF xs w

-- type family MakeFs (p :: * -> *) xs = (r :: * -> *) where
--   MakeFs p '[]       = p

  -- MakeFs (a ': as) p w g = (MakeFs as () w g)

-- --            GSingle (V b) :: GVect u p (p -> b -> w) w [(i, a)]
-- -- (V a) :<&> Gsingle (V b) :: GVect u a (a -> b -> w) w [(i, a)]

-- -- appendG :: GVect u (a -> b -> x) (a -> b) xs -> GraphEff u i a -> GVect u _ _ ( xs :++ '[ '(i, a) ] )
-- -- appendG v@(GSingle a) g = (a :<&> _ g)

-- data ApQueue u i w where
--   ApQueue :: GVect u (Aps 'Empty is) (a -> b) -> GraphEff u i a -> ApQueue i (Aps 'Empty (i :' is))

    -- E :: ctor ->  Arrs u j (Output ctor) b -> GraphEff u (ctor :>>= j) b

-- reduceApQueue :: ApQueue u 'Empty ( '( 'Empty, a) ': xs) w -> ApQueue u 'Empty ( xs ) w
-- reduceApQueue (ApQueue (V f) (V a :<&> b)) = ApQueue (V (f a)) b

-- extractApQueue :: ApQueue u 'Empty '[] w -> w
-- extractApQueue (ApQueue (V f) (GNil)) = f

-- instance FmapN xs => FmapN ( '(i1, a1) ': xs ) where
--   fmapN :: forall a b i1 a1 xs. (a -> b) -> MakeF ( '(i1, a1) ': xs ) a -> MakeF ( '(i1, a1) ': xs ) b
--   fmapN f = ($.$) @(MakeF xs a) @(MakeF xs b) @(MakeF ( '(i1, a1) ': xs ) a) @(MakeF ( '(i1, a1) ': xs ) b) (fmapN f)

-- instance FmapN ( '(i1, a1) ': xs ) where
  -- fmapN :: forall a b i1 a1 xs. (a -> b) -> MakeF ( '(i1, a1) ': xs ) a -> MakeF ( '(i1, a1) ': xs ) b
  -- fmapN f = (f $.$)

-- instance FmapN ( xs) => FmapN [ '(i1, a1) , '(i2, a2), '(i3, a3) ] where
--   -- fmapN :: forall a b i1 a1 xs. (a -> b) -> MakeF ( '(i1, a1) ': xs ) a -> MakeF ( '(i1, a1) ': xs ) b
--   fmapN f = (fmap . fmap . fmap) f

-- instance FmapN '[ '(i1, a1), '(i2, a2) ] where
--   fmapN f a = fmapN @'[] ((f .) .) a

-- instance FmapN xs => FmapN ( '(i1, a1) ': xs ) where
--   fmapN f a = where 
    
--   fmapN @xs (f .) a



-- fmapApQueue :: (a -> b) -> ApQueue m i0 xs a -> ApQueue m i0 xs b
-- fmapApQueue yz (ApQueue (V f) q) = ApQueue (V _) q

type role FTCQueue representational phantom representational nominal
data FTCQueue m (i :: Tree Effect) a b where
        Leaf :: (a -> m i' b) -> FTCQueue m i a b
        Node :: FTCQueue m i a x -> FTCQueue m j x b -> FTCQueue m k a b

-- -- Exported operations

-- -- There is no tempty: use (tsingleton return), which works just the same.
-- -- The names are chosen for compatibility with FastTCQueue

{-# INLINE tsingleton #-}
tsingleton :: (a -> m i b) -> FTCQueue m i a b
tsingleton r = Leaf (r)

-- snoc: clearly constant-time
{-# INLINE (|>) #-}

(|>) :: FTCQueue m i a x -> (x -> m j b) -> FTCQueue m k a b
t |> r = Node (t) (Leaf (r))

-- append: clearly constant-time
{-# INLINE (><) #-}

(><) :: FTCQueue m i a x -> FTCQueue m j x b -> FTCQueue m k a b
t1 >< t2 = Node t1 t2

-- -- Left-edge deconstruction
-- data ViewL m a b where
--         TOne :: (a -> m b) -> ViewL m a b
--         (:<) :: (a -> m x) -> (FTCQueue m x b) -> ViewL m a b

-- {-# INLINABLE tviewl #-}
-- tviewl
--     :: FTCQueue m a b -> ViewL m a b
-- tviewl (Leaf r) = TOne r
-- tviewl (Node t1 t2) = go t1 t2
--   where
--     go :: FTCQueue m a x -> FTCQueue m x b -> ViewL m a b
--     go (Leaf r) tr       = r :< tr
--     go (Node tl1 tl2) tr = go tl1 (Node tl2 tr)


$(promoteOnly [d|
  addPath [] p'       = ([p'], 0)
  addPath (p : ps) p' = if p == p'
                        then (p : ps, 0)
                        else case addPath ps p' of
                          (ps', n) -> (p : ps', n+1)

  addCallGraph (Graph ps es) p' = case addPath ps p' of
                                    (ps', _) -> Graph ps' es

  handleEffects (Graph ps es) hs = Graph ps (Prelude.filter (\e -> e `notElem` hs) es)

  -- callIdx (Graph ps _) p' = case addPath ps p' of
  --                              (_, n) -> n

  -- lookupIndex :: Nat -> Graph v -> Tree v
  -- lookupIndex k u = lookupIndex' k (ixpaths u)

  -- lookupIndex'                    :: (Eq a) => a -> [(a, b)] -> b
  -- lookupIndex'    key ((x,y):xys) = if key == x then y else lookupIndex' key xys

  -- lookupValue :: Eq v => Tree v -> Graph v -> Nat
  -- lookupValue k u = lookupValue' k (ixpaths u)

  -- lookupValue'                    :: (Eq b) => b -> [(a,b)] -> a
  -- lookupValue'  value ((x,y):xys) = if value == y then x else lookupValue' value xys

  |])

-- type family EqTree (a :: Tree Effect) (b :: Tree Effect) where
--   EqTree (Do ctor :>>= k) (Do ctor :>>= k) = True

-- type instance (a :: Tree Effect) == (b :: Tree Effect) = EqTree a b

-- type instance (==)
-- instance SDecide (Tree Effect) (a :: Tree Effect) (b :: Tree Effect) where
--   EqTree (Do ctor :>>= k) (Do ctor :>>= k) = True

-- instance SDecide (Tree Effect) where
--   (%~) :: forall a b. Sing a -> Sing b -> Decision (a :~: b)
--   a %~ b =

-- testEq :: forall ctor u j k a b. (SingI j, SingI (Do ctor :>>= k)) => GraphEff u 'Empty j a -> (forall k. GraphEff u 'Empty (Do ctor :>>= k) b) -> Maybe (j :~: Do ctor :>>= k)
-- testEq a b = testEquality (sing :: Sing j) (sing :: Sing (Do ctor :>>= k))

-- instance TestEquality (MonadEff )

-- type family HeadType j e = r where
--   HeadType (Do ctor :>>= i) e = ctor :~: e

-- data Call (n :: Nat) r = forall u j. Call !(GraphEff u 'Empty j r)
-- type instance Output (Call n r) = r

-- call :: u' ~ addCallGraph u j => GraphEff u 'Empty j a -> GraphEff u' i (Do (Call n r) :>>= i) a
-- call m = E (Call m) (tsingleton V)

-- runReader :: forall r u j a k. (SingI j) => GraphEff u 'Empty j a -> GraphEff u 'Empty j a
-- runReader (V x) = V x
-- runReader (E u q) = case STypeRep @j %~ STypeRep @(Do (Ask r) :>>= k) of
--   Proved x -> _ x

-- runInterpreters :: GraphEff u 'Empty j a -> a
-- runInterpreters = undefined
