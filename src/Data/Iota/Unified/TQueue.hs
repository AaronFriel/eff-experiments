{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE ScopedTypeVariables
 , TypeFamilies
 , GADTs
 , KindSignatures
 , TypeOperators
 , FlexibleContexts
 , RankNTypes
 , UndecidableInstances
 , FlexibleInstances
 , InstanceSigs
 , DefaultSignatures
 , DataKinds
 , TypeInType
 , PolyKinds
 , FunctionalDependencies
 , TypeFamilyDependencies
 , StandaloneDeriving
#-}

{-# LANGUAGE AllowAmbiguousTypes #-}

{-# LANGUAGE TypeApplications, MagicHash #-}

{-# LANGUAGE TemplateHaskell #-}

{-# LANGUAGE MultiParamTypeClasses #-}

{-# LANGUAGE PartialTypeSignatures #-}

module Data.Iota.Unified.TQueue where

import Prelude hiding (return, (>>=), (>>), fail, fmap, pure, (<*>))
import qualified Prelude as P (return, (>>=), (>>), fail, fmap, pure, (<*>))
import Control.Monad (ap)
import Data.Singletons.Prelude.List
-- import Data.Iota.Unified.Indexed
import Data.Kind (type (*), type Type, type Constraint)
import Control.Monad.Indexed

import Data.List.NonEmpty

import Data.Singletons
import Data.Singletons.Prelude.List
import Data.Singletons.Prelude.Either
import Data.Singletons.Prelude.Bool
import Data.Singletons.Prelude.Tuple
import Data.Singletons.TH

import Data.Type.Equality
import GHC.Prim (Proxy#, proxy#, type (#))
import GHC.Types (TYPE, RuntimeRep (VoidRep))
import Unsafe.Coerce (unsafeCoerce)

import Data.Coerce
import GHC.TypeLits hiding (type (*))

-- Combines "Union" and "Eff"


eqToRefl :: forall a b. (a == b) ~ 'True => a :~: b
eqToRefl = unsafeCoerce (Refl :: () :~: ())

newtype One a = One a
--   deriving Show

data IxPure r = IxPure r
data IxNode q1 q2 = IxNode q1 q2
data IxBind a q = IxBind a q
data IxEffect (t :: * -> *) v = forall v1. IxEffect (t v) v

-- type family IxNodeFamily q1 a q2 b where
--   IxNodeFamily  IxPure           a  q2               b = IxNode IxPure q2
--   IxNodeFamily  q1               a  IxPure           b = IxNode q1 IxPure
--   IxNodeFamily (IxBind     a q1) x (IxBind     x q2) b = IxNode (IxBind     a q1) (IxBind x q2)
  -- IxNodeFamily (IxBind     a q1) x (IxEffect m v) b = IxNode (IxBind     a q1) (IxBind x q2)
  -- IxNodeFamily (IxEffect m a q1) x (IxBind     x q2) b = IxNode (IxEffect m a q1) (IxBind x q2)

-- type family Input a :: * where
--   Input (IxPure _)      = Any
--   Input (IxEffect _ _)  = Any
--   Input (IxBind a _)    = a
--   Input (IxNode q1 _) = Input q1

type family Output a :: * where
  Output (IxPure r)      = r
  Output (IxEffect _ v)  = v
  Output (IxBind a q)    = Output q
  Output (IxNode q1 q2)  = Output q2

type family Compat a b :: Constraint where
  Compat a           (IxPure _)     = a ~ a
  Compat a           (IxEffect _ _) = a ~ a
  Compat a           (IxBind b q)   = Output a ~ b
  Compat a           (IxNode q1 q2) = Compat a q1
  -- Compat (IxEffect _ _)    b = b ~ b
  -- Compat (IxBind a _)      b = a ~ b
  -- Compat (IxNode q1 _ _ _) b = Input q1 ~ b

data IxQueue q where
  -- Computed values
  Pure    :: r                                          -> IxQueue (IxPure     r)
  Effect  :: t v                                        -> IxQueue (IxEffect t v)
  Bind    :: (a -> IxQueue q)                           -> IxQueue (IxBind a q)
  Node    :: (Compat q1 q2) => IxQueue q1 ->  IxQueue q2 -> IxQueue (IxNode q1 q2)

data Writer t x where
  Writer :: t -> Writer t ()
--
-- data State s v where
--         Get :: State s s
--         Put :: !s -> State s ()
--
t0 = Pure "foo"
t1 = Effect (Writer "foo")
t2 = Node t0 t1

--
-- eff :: t v -> IxQueue (t v) a v
-- eff ctor = Effect proxy# ctor

-- type family Ran eff q rebind where
--   Ran eff ()          rebind = ()
--   Ran eff (eff)       rebind = ()
--   Ran eff (q, x)      rebind = (Ran eff q rebind, rebind x)
--   Ran eff (q1, x, q2) rebind = (Ran eff q1 rebind, rebind x, Ran eff q2 rebind)
--
-- -- type family WriterRebind o r where
-- --   WriterRebind o r = (r, [o])
-- --
data IsPure
data MatchLeft
data MatchRight
data MatchBoth

type family EffectMatch eff q where
  EffectMatch eff (IxPure r)     = 'True
  -- EffectMatch eff (IxEffect t v) = Sing (eff == t)
  -- EffectMatch t1 v (IxEffect t v) = 'False

type family Effect k (eff :: k -> k) (params :: k) (q :: k) (test :: Bool) = (result :: k)

type instance Effect Type (Writer o) [o] (IxPure r)               t = IxPure (r, [o])
-- type instance Effect Type (Writer o) [o] (IxEffect (Writer o) ()) True  = IxPure ((), [o])
-- type instance Effect Type (Writer o) [o] (IxEffect         t   v) False = IxPure ()
-- type instance Effect (Writer o ()) [o] (IxEffect t ())          False = IxNode
--                         (IxEffect t ())
--                         (IxBind
--                            (Output (IxEffect t ())) (IxPure (Output (IxEffect t ()), [o])))

runWriter :: (t ~ EffectMatch (Writer o) q) => Proxy# t -> [o] -> IxQueue q -> IxQueue (Effect Type (Writer o) [o] q t)
runWriter (p :: Proxy# True) w (Pure r) = Pure (r, w)
-- runWriter w (_ :: Proxy# True) (Effect (Writer (t :: o))) = Pure ((), w)
-- runWriter w (_ :: Proxy# False) (Effect k) = Pure ()

-- instance Effect (Writer o ()) o (IxPure r) t where
--   type RunEff (Writer o ()) o (IxPure r) t = IxPure (r, [o])
--   run o (Pure r) = Pure (r, o)

-- type instance Effect (Writer o ()) [o]

-- class Effect eff params q test where
--   type RunEff eff params q test
--   run :: params -> IxQueue q -> IxQueue (RunEff eff params q test)

--
-- type family RunEff eff params q (test :: Bool)
--
-- type instance RunEff (Writer o ()) o (IxPure r) _ = IxPure (r, [o])
-- type instance RunEff (Writer o ()) o (IxEffect (Writer o) v) _ = IxPure (r, [o])
-- type instance RunEff True o (IxPure r) = IxPure (r, [o])
-- type instance RunEff _ o (IxPure r) = IxPure (r, [o])
-- type instance RunEff _ o (IxPure r) = IxPure (r, [o])
-- type instance RunEff (Writer o ()) o (IxPure r) = IxPure (r, [o])

-- type family RanWriter o q where
--   RanWriter o (IxPure r) = IxPure (r, [o])
--   RanWriter o (IxEffect (Writer o) v) = IxPure  ((), [o])
--   RanWriter o (IxEffect t v) = IxNode
--                         (IxEffect t v)
--                         (IxBind
--                            (Output (IxEffect t v)) (IxPure (Output (IxEffect t v), [o])))
--
-- --
-- class RunWriter o q where
--   runWriter :: [o] -> IxQueue q -> IxQueue (RanWriter o q)
--
--
-- instance RunWriter o (IxEffect (Writer o) v) where
--   type RanWriter o (IxEffect (Writer o) v) = IxPure  ((), [o])
--   runWriter w (Effect (Writer t)) = Pure ((), t:w)
--
-- instance RunWriter o (IxEffect t v) where
--   type RanWriter o (IxEffect t v) = IxNode
--                         (IxEffect t v)
--                         (IxBind
--                            (Output (IxEffect t v)) (IxPure (Output (IxEffect t v), [o])))
--   runWriter w (Effect k) = undefined

-- instance RunWriter o (IxPure r) where
--   type RanWriter o (IxPure r) = IxPure (r, [o])
--   runWriter o (Pure r) = Pure (r, o)

-- type family RanWriter o q where
--   RanWriter o (IxPure r)               = IxPure  (r, [o])
--   RanWriter o (IxEffect (Writer o) ()) = IxPure  ((), [o])
--   RanWriter o (IxEffect t v)           = IxNode
--                       (IxEffect t v)
--                       (IxBind
--                          (Output (IxEffect t v)) (IxPure (Output (IxEffect t v), [o])))

  -- RanWriter o (IxBind a r)              = IxQueue (IxBind a (RanWriter o q)) ( r, [o])
--
--
-- class RunWriter o q  where
--   runWriter :: [o] -> IxQueue q -> IxQueue (RanWriter o q)
--
-- instance RunWriter o (IxPure r) where
--   runWriter w (Pure r) = Pure (r, w)
--
-- instance (t ~ Writer o, v ~ ()) => RunWriter o (IxEffect t v) where
--   runWriter w (Effect (Writer t)) = Pure ((), t:w)
--
-- instance RunWriter o (IxEffect t v) where
--   runWriter w k = Node k (Bind $ \v -> Pure (v, w))
--
-- instance RunWriter o (IxQueue (IxBind a q) r) where
--   runWriter w (Bind k) = Bind (\a -> case k a of
--     Pure r -> Pure (r, w)
--     )
--
-- instance RunWriter o (IxQueue IxPure r) where
--   runWriter w (Pure r) = Pure (r, w)
--
-- instance RunWriter o () a r where
--   runWriter w (Pure r) = Pure (r, w)
--
-- -- instance RunWriter o t a r where
-- --   runWriter w (Effect p ctor) = (Effect p ctor)
--
-- instance RunWriter o (Writer o (), q, x) a r where
--    runWriter w (Bind (Writer t) f) = Bind (\a -> case f a of
--      Pure r -> Pure (r, t:w))
--

-- runWriter :: [o] -> IxQueue q a r -> IxQueue (RanWriter o q) a (r, [o])
-- runWriter w (Pure r)     = Pure (r, w)
-- runWriter w (Effect p k) =
--   case coerce k of
--     Writer str -> undefined

-- Pure (r, t:w)
-- runWriter (Pure r) = (Pure r) :: IxQueue (Proxy# ()) a r
--
-- t2 = Bind (\a -> eff (Writer a))
-- t3 = Node (Bind (\a -> Node (eff (Writer a)) (Pure "bar"))) (Bind (\y -> eff (Put y)))
-- --
-- -- class Run q a r where
-- --   run :: a -> IxQueue q a r -> r
-- --   run a (Pure r) = r
-- --
-- -- instance Run (Proxy# q) a v where
-- --   run a (Pure r) = r
--
-- foo = case (proxy# @(Proxy# 0)) %~ _ of
--   _ -> "true"

-- class RunWriter o q q2 a b r where
--   runWriter :: [o] -> IxQueue q a r -> IxQueue q2 b (r, [o])
--
-- instance RunWriter o () () a b r where
--   runWriter o (Pure r) = (Pure (r, o))
--
-- instance RunWriter o (Writer o ()) () a b r where
--   runWriter o (Effect (Writer t) p) = (Pure ((), t:o))
--
-- instance RunWriter o (q, x) () a x r where
--   runWriter o (Bind m)              = (Bind (\a -> runWriter o (m a)))

-- instance RunWriter ((), x, ()) () o a b where
--   -- runWriter' :: [o] -> IxQueue (q1, q2) a b -> _
--   runWriter o (Node (Bind m1) (Bind m2)) = Bind (\a ->
--     case runWriter o (m1 a) of
--       Pure (r', o') -> case runWriter o (m2 r') of
--         Pure (r'', o'') -> undefined)
  -- case runWriter o (m1 a) of
  --   (Pure (r, o')) -> case runWriter o' (m2 r) of
  --     (Pure (r', o'')) -> undefined)

-- instance RunWriter (Proxy# (q1, q2)) (Proxy# ()) o a r where
--   runWriter o (Node (Bind m1) (Bind m2)) = Bind (\a ->
--     case runWriter o (m1 a) of
--       (Pure (r, o')) -> case runWriter o' (m2 r) of
--         (Pure (r', o'')) -> undefined)

-- run a n@(Effect t pt) =
--   case pt :~: (proxy# :: Proxy# (Writer String)) of
--     _ -> undefined
-- --
-- -- isingleton :: (a -> m i j b) -> IxQueue m a b '[ '(a, b) ]
-- isingleton = Leaf
-- --
-- -- --
-- -- -- -- -- type Arr r a b = a -> (Eff r) b
-- -- -- type Arrs r a b = forall (q :: '[]). IxQueue (Eff r) a b q
-- -- --
-- -- -- data Eff (r :: [* -> *]) (i :: [(* -> *, Nat)]) (j ::
-- -- --                                                    [(* -> *, Nat)]) (a :: *)
-- -- --      where
-- -- --         Val :: a -> Eff r i j a
-- -- --         E :: t v -> Arrs r b a -> Eff r i j a
-- -- -- -- isingleton :: (a -> m i j b) -> IxQueue m i j a b ()
-- -- -- isingleton = Leaf
-- -- --
-- -- -- -- -- (|>) :: IxQueue b1 -> b -> IxQueue (b1, One b)
-- -- -- -- (|>) :: IxQueue m a x (i, j) -> (x -> m j k b) -> IxQueue m a b (i, k)
-- -- -- -- (|>) :: IxQueue m i j a x q1 -> (x -> m j k b) -> IxQueue m i k a b (q1, (j, x), ())
-- t |> r = Node t (Leaf r)
-- -- -- --
-- -- -- -- -- (><) :: IxQueue b -> IxQueue c -> IxQueue (b, c)
-- -- -- -- (><) :: IxQueue m a x (i, j) -> IxQueue m x b (j, k) -> IxQueue m a b (i, k)
-- -- -- -- (><) :: IxQueue m i j a x q1 -> IxQueue m j k x b q2 -> IxQueue m i k a b (q1, (j, x), q2)
-- t1 >< t2 = Node t1 t2
-- --
-- data TViewL m a b (q :: *) where
--   TOne  :: (a -> m i j b) -> TViewL m a b '[(a, b)]
--   (:+|) :: (a -> m i j x) -> IxQueue m x b q2 -> TViewL m a b ((a, x), q2)
--
-- -- class ViewL a where
-- --   viewl :: IxQueue m a b q -> TViewL m a b q
--
-- viewl :: IxQueue m a b q -> TViewL m a b q
-- viewl (Leaf a) = TOne a
-- viewl (Node (Leaf r) tr) = r :+| tr
-- viewl (Node (Node a b) tr) = viewl (Node a (Node b tr))
  -- where
  --   -- go :: IxQueue m a x q1 -> IxQueue m x b q2 -> TViewL m a b (q1 :++ q2)
  --   go (Leaf r) tr = r :+| tr
  --   go (Node tl1 tl2) tr = go tl1 (Node tl2 tr)

-- viewl (Node (Leaf a) b) = a :+| b
-- viewl (Node (Node a b) c) = viewl (Node a (Node b c))
--
-- class ViewL a where
--   type TTViewL a
--   viewl :: a -> TTViewL a
--
-- instance ViewL (IxQueue m a b ()) where
--   type TTViewL (IxQueue m a b ()) = TViewL m a b ()
--   viewl (Leaf a) = TOne a
--
--
-- instance ViewL (IxQueue m a b ((), x, q2)) where
--   type TTViewL (IxQueue m a b ((), x, q2)) = TViewL m a b ((), x, q2)
--   viewl (Node (Leaf a) b) = a :| b
--
-- -- instance ViewL (IxQueue m a b (q1, q2, (q3, q4, q5))) => ViewL (IxQueue m a b ((q1, q2, q3), q4, q5)) where
-- --   type TTViewL (IxQueue m a b ((q1, q2, q3), q4, q5)) = TTViewL (IxQueue m a b (q1, q2, (q3, q4, q5)))
-- --   viewl (Node (Node a b) c) = viewl (Node a (Node b c))
--
-- qApp :: Arrs r i j b w -> b -> Eff r i j w
-- qApp q x =
--   case viewl q of
--     TOne k -> k x
--       Val y -> undefined
--     k :| t ->
--         case k x of
--             Val y -> qApp t y
--             E u q -> E u (q >< t)
--
-- -- tviewl :: IxQueue m i k a b q -> TViewL m i k a b q
-- -- tviewl (Leaf a) = TOne a
-- -- tviewl (Node t1 t2) = go t1 t2
-- --   where
-- --     go :: IxQueue m i j a x q1 -> IxQueue m j k x b q2 -> TViewL m1 i1 k1 a1 b1 ((), (j1, x1), q5)
-- --     go (Leaf r) tr = r :| tr
-- --     go (Node tl1 tl2) tr = go tl1 (Node tl2 tr)
-- --
-- -- qApp
-- --     :: Arrs r i j b w -> b -> Eff r i j w
-- -- qApp q x =
-- --     case tviewl q of
-- --         TOne k -> k x
-- --         k :| t ->
-- --             case k x of
-- --                 Val y -> qApp t y
-- --                 E u q -> E u (q >< t)
--
--
-- -- instance ViewL (IxQueue m a b (i, j)) where
-- --   -- type TTViewL (IxQueue m a b (i, j)) = TViewL (One a)
-- --   viewl (Leaf a) = TOne a
-- --   viewl (Node (Leaf a) b) = a :| b
--
-- -- instance ViewL (IxQueue (One a, b)) where
-- --   type TTViewL (IxQueue (One a, b)) = TViewL (a, b)
-- --   viewl (Node (Leaf a) b) = a :| b
-- --
-- -- instance ViewL (IxQueue (a, (b, c))) => ViewL (IxQueue ((a, b), c)) where
-- --   type TTViewL (IxQueue ((a, b), c)) = TTViewL (IxQueue (a, (b, c)))
-- --   viewl (Node (Node a b) c) = viewl (Node a (Node b c))
--
-- --
-- -- data IxQueue a where
-- --   Leaf :: b -> IxQueue (One b)
-- --   Node :: IxQueue b -> IxQueue c -> IxQueue (b, c)
-- --
-- -- -- isingleton :: b -> IxQueue (One b)
-- -- isingleton = Leaf
-- --
-- -- (|>) :: IxQueue b1 -> b -> IxQueue (b1, One b)
-- -- t |> r = Node t (Leaf r)
-- --
-- -- (><) :: IxQueue b -> IxQueue c -> IxQueue (b, c)
-- -- t1 >< t2 = Node t1 t2
-- --
-- -- data TViewL a where
-- --   TOne  :: b -> TViewL (One b)
-- --   (:|) :: b -> IxQueue c -> TViewL (b, c)
-- --
-- -- class ViewL a where
-- --   type TTViewL a
-- --   viewl :: a -> TTViewL a
-- --
-- -- instance ViewL (IxQueue (One a)) where
-- --   type TTViewL (IxQueue (One a)) = TViewL (One a)
-- --   viewl (Leaf a) = TOne a
-- --
-- -- instance ViewL (IxQueue (One a, b)) where
-- --   type TTViewL (IxQueue (One a, b)) = TViewL (a, b)
-- --   viewl (Node (Leaf a) b) = a :| b
-- --
-- -- instance ViewL (IxQueue (a, (b, c))) => ViewL (IxQueue ((a, b), c)) where
-- --   type TTViewL (IxQueue ((a, b), c)) = TTViewL (IxQueue (a, (b, c)))
-- --   viewl (Node (Node a b) c) = viewl (Node a (Node b c))
-- --
-- -- instance (Show b) => Show (IxQueue (One b)) where
-- --   showsPrec d (Leaf a) = showParen (d > app_prec) $ showString "Leaf " . showsPrec (app_prec+1) a
-- --     where app_prec = 10
-- --
-- -- instance (Show (IxQueue b), Show (IxQueue c)) => Show (IxQueue (b, c)) where
-- --   showsPrec d (Node a b) = showParen (d > app_prec) $ showString "Node " . showsPrec (app_prec+1) a . showsPrec (app_prec+1) b
-- --     where app_prec = 10
-- --
-- -- instance Show b => Show (TViewL (One b)) where
-- --   showsPrec d (TOne b) = showParen (d > app_prec) $ showString "TOne " . showsPrec (app_prec+1) b
-- --     where app_prec = 10
-- --
-- -- instance (Show b, Show (IxQueue c)) => Show (TViewL (b, c)) where
-- --   showsPrec d (r :| tr) =
-- --       showParen (d > app_prec) $ showsPrec (app_prec+1) r . showString " :| " . showsPrec (app_prec+1) tr
-- --     where app_prec = 10
-- --
-- -- -- type Arr r a b = a -> (Eff r) b
-- -- type Arrs r a b = forall i j. IxQueue (a -> Eff r i j b)
-- --
-- -- -- Combines "U hnion" and "Eff"
-- -- data Eff (r :: [* -> *]) (i :: [(* -> *, Nat)]) (j ::
-- --                                                  [(* -> *, Nat)]) (a :: *)
-- --    where
-- --       Val :: a -> Eff r i j a
-- --       E :: t v -> Arrs r b a -> Eff r i j a
-- --
-- --
-- -- qApp :: (forall i j. IxQueue (One (b -> Eff r i j w))) -> b -> Eff r i j w
-- -- qApp q x =
-- --    case (viewl q) of
-- --      TOne k  -> k x
--     --  k :| t -> case k x of
--     --    Val y -> qApp t y
--     --    E u q -> E u (q >< t)
-- --
