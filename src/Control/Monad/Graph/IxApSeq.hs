{-# LANGUAGE GADTs,TypeSynonymInstances,FlexibleInstances,Rank2Types #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

module Control.Monad.Graph.IxApSeq where

import Control.Monad.Indexed
import Data.Functor.Indexed

import Data.Coerce

import Debug.Trace 

import Data.HVect (HVect (..))
import qualified Data.HVect as HVect

tpure :: ApSequence s c => a -> s c y y a
tpure = tsingleton . ireturn

class (IxApplicative c, IxPointed c) => ApSequence s c where
--   tempty     :: a -> s c x x a
  tsingleton :: c x y a -> s c x y a
  -- | Append two type aligned sequences
  (><)       :: s c x y (a -> b) -> s c y z a -> s c x z b
  -- | View a type aligned sequence from the left
  tviewl     :: s c x y a -> TAViewL s c x y a
  -- | View a type aligned sequence from the right
  --       
  -- Default definition:
  -- 
  -- > tviewr q = case tviewl q of 
  -- >   TAEmptyL -> TAEmptyR
  -- >   h :< t -> case tviewr t of
  -- >        TAEmptyR -> tempty   :> h
  -- >        p :> l   -> (h <| p) :> l
  tviewr     :: s c x y a -> TAViewR s c x y a
  -- | Append a single element to the right
  --
  -- Default definition:
  -- 
  -- > l |> r = l >< tsingleton r

  (|>)       :: s c x y (a -> b) -> c y z a -> s c x z b
  -- | Append a single element to the left
  -- 
  -- Default definition:
  --
  -- > l <| r = tsingleton l >< r

  (<|)       :: c x y (a -> b) -> s c y z a -> s c x z b
  -- | Apply a function to all elements in a type aligned sequence
  -- 
  -- Default definition:
  -- 
  -- > tmap f q = case tviewl q of
  -- >    TAEmptyL -> tempty
  -- >    h :< t -> f h <| tmap f t
  tmap       :: (a -> b) -> s c x y a -> s c x y b
  
  l |> r = l >< tsingleton r
  l <| r = tsingleton l >< r
  l >< r = case (tviewr l, tviewl r) of
    (TAEmptyR a, TAEmptyL b) -> tsingleton (iap a b)
    (TAEmptyR a, b1 :< bs)   -> ((imap (.) a) `iap` b1) <| bs
    (as :> a1, TAEmptyL b) -> tmap uncurry as |> ((imap (,) a1) `iap` b)
    (as :> a1, b1 :< bs) -> tmap uncurry as >< ( ((imap ( (.) . (,) ) a1) `iap` b1) <| bs)

  tviewl q = case tviewr q of 
    TAEmptyR a -> TAEmptyL a
    p :> l -> case tviewl p of
        TAEmptyL f -> TAEmptyL $ f `iap` l
        h :< t     -> imap uncurry h :< ((tpure (,) >< t) |> l)  
  
  tviewr q = case tviewl q of 
    TAEmptyL a -> TAEmptyR a
    f :< t -> case tviewr t of
        TAEmptyR b -> TAEmptyR $ f `iap` b
        p :> l -> ((imap (.) f) <| p) :> l

  tmap f q = case tviewr q of
    TAEmptyR a -> tsingleton $ imap f a
    p :> l -> tmap (f .) p |> l

data TAViewL s c x y a where
   TAEmptyL  :: c x y a -> TAViewL s c x y a
   (:<)     :: c x y (a -> b) -> s c y z a -> TAViewL s c x z b

data TAViewR s c x y a where
   TAEmptyR  :: c x y a -> TAViewR s c x y a
   (:>)     :: s c x y (a -> b) -> c y z a -> TAViewR s c x z b



data SnocList c x y a where
  SNil :: c x y a -> SnocList c x y a
  Snoc :: SnocList c x y (a -> b) -> c y z a -> SnocList c x z b

instance (IxPointed f, IxApplicative f) => ApSequence SnocList f where
  tsingleton c = SNil c
  (|>) = Snoc
  tviewr (SNil a) = TAEmptyR a
  tviewr (Snoc p l) = p :> l
  tmap phi (SNil a) = SNil (imap phi a)
  tmap phi (Snoc s c) = Snoc (tmap (phi .) s) c

data ConsList c x y a where
  CNil :: c x y a -> ConsList c x y a
  Cons :: c x y (a -> b) -> ConsList c y z a -> ConsList c x z b

instance (IxPointed f, IxApplicative f) => ApSequence ConsList f where
  tsingleton c = CNil c
  a <| b = Cons a b
  tviewl (CNil a) = TAEmptyL a
  tviewl (Cons h t) = h :< t

-- data FingerTree f i j a where
--   Single  :: f i j a -> FingerTree f i j a
--   Double  :: f i j (a -> b) -> f j k a -> FingerTree f i k b
--   Deep   :: !(Digit f i j (a -> b -> c)) -> FingerTree (Node f) j k b -> !(Digit f k l c) -> FingerTree f i l c

-- data Node f i j a where
--   Empty     :: Node f i k ()
--   BiasLeft  :: f i j a -> f j k b -> Node f i k a
--   BiasRight :: f i j a -> f j k b -> Node f i k b 
--   Node1 :: f i j a -> Node f i j a
--   Node2 :: f i j (a -> b) -> f j k a -> Node f i k b
--   Node3 :: f i j (a -> b -> c) -> f j k a -> f k d b -> Node f i d c

-- data Digit f i j a where
--   One   :: f i j a                  -> Digit f i j a
--   Two   :: f i j (a -> b)           -> f j k a -> Digit f i k b
--   Three :: f i j (a -> b -> c)      -> f j k a -> f k l b -> Digit f i l c
--   Four  :: f i j (a -> b -> c -> d) -> f j k a -> f k l b -> f l m c -> Digit f i m d
--   Five  :: f i j (a -> b -> c -> d -> e) -> f j k a -> f k l b -> f l m c -> f m n d -> Digit f i m e

-- instance TASequence FingerTree where
--   tempty = Empty
--   tsingleton = Single

--   Empty                     |> a = Single a
--   Single b                  |> a = Deep (One b) Empty (One a)
--   Deep pr m (Four e d c b)  |> a = Deep pr (m |> Node3 e d c) (Two b a)
--   Deep pr m sf              |> a = Deep pr m (appendd sf (One a))

--   a <| Empty                     = Single a
--   a <| Single b                  = Deep (One a) Empty (One b) 
--   a <| Deep (Four b c d e) m sf  = Deep (Two a b) (Node3 c d e <| m) sf
--   a <| Deep pr m sf              = Deep (appendd (One a) pr) m sf

--   tviewl Empty = TAEmptyL
--   tviewl (Single a) = a :< Empty
--   tviewl (Deep pr m sf) = case toList pr of
--               h ::: t -> h :< deepl t m sf

--   tviewr Empty = TAEmptyR
--   tviewr (Single a) = Empty :> a 
--   tviewr (Deep pr m sf) = case toListR sf of
--             h :::< t -> deepr pr m t :> h

--   xs >< ys = app3 xs ZNil ys

--   tmap f Empty = Empty
--   tmap f (Single a) = Single (f a)
--   tmap f (Deep l m r) = Deep (mapd f l) (tmap (mapn f) m) (mapd f r)



-- toTree :: Digit f i j a -> FingerTree f i j a
-- toTree (One a)          = Single a
-- toTree (Two a b)        = Double a b
-- toTree (Three a b c)    = Deep (Two a b) (Single (NodeEmpty)) (One c)
-- toTree (Four a b c d)   = Deep (Two a b) (Single (Node1 c)) (One d)
-- toTree (Five a b c d e) = Deep (Two a b) (Single (Node1 c)) (Two d e)


-- appendd :: Digit f a b -> Digit f b c -> Digit f a c
-- appendd (One a)        (One b)        = Two a b
-- appendd (One a)        (Two b c)      = Three a b c
-- appendd (Two a b)      (One c)        = Three a b c
-- appendd (One a)        (Three b c d)  = Four a b c d
-- appendd (Two a b)      (Two c d)      = Four a b c d
-- appendd (Three a b c)  (One d)        = Four a b c d






-- infixr 5 ::: 


-- data ZList r a b where
--   ZNil :: ZList r a a
--   (:::) :: r a b -> ZList r b c -> ZList r a c

-- toList (One a) = a ::: ZNil 
-- toList (Two a b) = a ::: b ::: ZNil
-- toList (Three a b c) = a ::: b ::: c ::: ZNil
-- toList (Four a b c d) = a ::: b ::: c ::: d ::: ZNil




-- fromList :: ZList r a b -> Digit f a b
-- fromList (a ::: ZNil) = One a
-- fromList (a ::: b ::: ZNil) = Two a b
-- fromList (a ::: b ::: c ::: ZNil) = Three a b c
-- fromList (a ::: b ::: c ::: d ::: ZNil) = Four a b c d

-- append :: ZList r a b -> ZList r b c -> ZList r a c
-- append ZNil t = t
-- append (h ::: t) r = h ::: append t r


-- deepl :: ZList r a b -> FingerTree (Node r) b c -> Digit f c d -> FingerTree f a d
-- deepl ZNil m sf = case tviewl m of
--            TAEmptyL -> toTree sf
--            a :< m' -> Deep (nodeToDigit a) m' sf 
-- deepl pr m sf = Deep (fromList pr) m sf

-- infixr 5 :::< 

-- data ZListR r a b where
--   ZNilR :: ZListR r a a
--   (:::<) :: r b c -> ZListR r a b -> ZListR r a c

-- toListR :: Digit f a b -> ZListR r a b
-- toListR (One a) = a :::< ZNilR
-- toListR (Two a b) = b :::< a :::< ZNilR
-- toListR (Three a b c) = c :::< b :::< a :::< ZNilR
-- toListR (Four a b c d) = d:::< c :::< b :::< a :::< ZNilR



-- fromListR :: ZListR r a b -> Digit f a b
-- fromListR (a :::< ZNilR) = One a
-- fromListR (b :::< a :::< ZNilR) = Two a b
-- fromListR (c :::< b :::< a :::< ZNilR) = Three a b c
-- fromListR (d :::< c :::< b :::< a :::< ZNilR) = Four a b c d


-- rev = toList . fromListR 



-- deepr :: Digit f a b -> FingerTree (Node r) b c -> ZListR r c d -> FingerTree f a d
-- deepr pr m ZNilR = case tviewr m of
--            TAEmptyR -> toTree pr
--            m' :> a -> Deep pr m' (nodeToDigit a)
-- deepr pr m sf = Deep pr m (fromListR sf)


-- nodeToDigit :: Node r a b -> Digit f a b
-- nodeToDigit (Node2 a b) = Two a b
-- nodeToDigit (Node3 a b c) = Three a b c



-- addAlll :: ZList r a b -> FingerTree f b c -> FingerTree f a c
-- addAlll ZNil m = m
-- addAlll (h ::: t) m = h <| addAlll t m

-- addAllr :: FingerTree f a b -> ZList r b c  -> FingerTree f a c
-- addAllr m ZNil  = m
-- addAllr m (h ::: t) = addAllr (m |> h) t

  

-- app3 :: FingerTree f a b -> ZList r b c -> FingerTree f c d -> FingerTree f a d
-- app3 Empty ts xs = addAlll ts xs
-- app3 xs ts Empty = addAllr xs ts
-- app3 (Single x) ts xs = x <| (addAlll ts xs)
-- app3 xs ts (Single x) = (addAllr xs ts) |> x
-- app3 (Deep pr1 m1 sf1) ts (Deep pr2 m2 sf2) =
--     Deep pr1 
--         (app3 m1 (nodes (append (toList sf1) (append ts (toList pr2)))) m2) sf2


-- nodes :: ZList r a b -> ZList (Node r) a b
-- nodes (a ::: b ::: ZNil) = Node2 a b ::: ZNil
-- nodes (a ::: b ::: c ::: ZNil) = Node3 a b c ::: ZNil
-- nodes (a ::: b ::: c ::: d ::: ZNil) = Node2 a b ::: Node2 c d ::: ZNil
-- nodes (a ::: b ::: c ::: xs) = Node3 a b c ::: nodes xs

-- mapn :: (forall x y. c x y -> d x y) -> Node c x y -> Node d x y
-- mapn phi (Node2 r s) = Node2 (phi r) (phi s)
-- mapn phi (Node3 r s t) = Node3 (phi r) (phi s) (phi t)
  
-- mapd :: (forall x y. c x y -> d x y) -> Digit c x y -> Digit d x y
-- mapd phi (One r) = One (phi r) 
-- mapd phi (Two r s) = Two (phi r) (phi s)
-- mapd phi (Three r s t) = Three (phi r) (phi s) (phi t)
-- mapd phi (Four r s t u) = Four (phi r) (phi s) (phi t) (phi u)


-- ------------------------------------------------
data ApTree t = Compute [t]
              | ApTree t `Then` ApTree t
              | ApTree t `But` ApTree t

data FreeApVec t f i j a where
    Single :: !(SnocList f i j a)              -> FreeApVec ('Compute t) f i j a 
    Then :: !(SnocList f i j a)              -> FreeApVec ('Compute t) f i j a 
--     Then   :: !(FreeApVec r) -> !(HVect t    ) -> FreeApVec (r ':*> 'Compute t)
--     But    :: !(HVect b    ) -> !(FreeApVec r) -> FreeApVec ('Compute b ':<* r)

-- data FreeApQ f i j a where
--     Pure :: f a -> FreeApQ f i j 

-- data ApTree = Then (Tree a) (Tree b)

-- data FreeApQ f i j a where
--     Pure :: f a -> FreeApQ f i i a

-- data FreeApQ f i j where
--     Pure :: f a -> FreeApQ f a a
--     Ap :: f a -> FreeApQ f (a -> b) b

-- fsingleton x = Single x

-- t1 :: FingerTree (FreeApQ Maybe) (Char -> Char -> (Char, Char)) (Char, Char)
-- t1 = (fsingleton (Pure $ pure (,)) |> Ap (pure 'a')) |> Ap (pure 'b')

-- runFreeStep :: FingerTree (FreeApQ Maybe) (a -> b -> c) x 
--    -> Maybe (FingerTree (FreeApQ Maybe) (b -> c) x)
-- runFreeStep t1 = case tviewl t1 of
--     (Pure (Just f') :< r) -> case tviewl r of
--         (Ap (Just a) :< r') -> Just $ Pure (pure $ f' a) <| r'  
--         _ -> Nothing
--     _ -> Nothing

-- runFreeStep' :: Applicative f => FingerTree (FreeApQ f) (a -> b -> c) x 
--    -> f (FingerTree (FreeApQ f) (b -> c) x)
-- runFreeStep' t1 = case tviewl t1 of
--     (Pure f' :< r) -> case tviewl r of
--         (Ap a :< r') -> pure $ Pure (f' <*> a) <| r'
--         -- (Pure a :< r') -> a *> (runFreeStep' $ Pure a <| r')
--     _ -> undefined


-- runFreeStep'' :: Applicative f => FingerTree (FreeApQ f) (a -> b -> c) y
--    -> f (FingerTree (FreeApQ f) (b -> c) y)
-- runFreeStep'' t1 = case tviewl t1 of
--     (Pure f' :< r) -> case tviewl r of
--         (Ap a :< r') -> pure $ Pure (f' <*> a) <| r'  
--         -- (Pure a :< r') -> a *> (runFreeStep'' $ Pure a <| r')
--     _ -> undefined

-- runFreeLast :: Applicative f
--             => FingerTree (FreeApQ f) (b -> c) c
--             -> f c
-- runFreeLast t1 = case tviewl t1 of
--     (Pure f' :< r) -> case tviewl r of
--         (Ap a :< r') -> f' <*> a
--         -- *> or <*, discarded application
--         (Pure a :< r') -> a *> (runFreeLast $ Pure a <| r')
--     (Ap a :< r') -> error "Impossible, nothing to apply Ap to"

-- -- returns `Just ('a', 'b')`
-- t1r = case runFreeStep t1 of
--     Just t1' -> case runFreeLast t1' of
--         Just x -> Just x
--         _ -> Nothing
--     _ -> Nothing

-- -- runFreeAp :: Applicative f => FingerTree (FreeApQ f) (a -> y) x -> f x
-- -- runFreeAp r = case tviewl r of
-- --     TAEmptyL -> undefined

-- t2 :: Applicative f => f a -> f b -> f c -> FingerTree (FreeApQ f) (a -> b -> c -> (a, b, c)) (a, b, c)
-- t2 a b c= (tsingleton (Pure $ pure (,,)) |> Ap a) |> Ap b |> Ap c 

-- t2r a b c = runFreeAp (t2 a b c)

-- t3 a b c = (tsingleton (Pure $ pure (,,))) |> Ap a |> Ap b |> Ap c


-- class Applicative f => RunFreeApQ f i j where
--     runFreeAp :: FingerTree (FreeApQ f) i j -> f j

-- instance Applicative f => RunFreeApQ f c c where
--     runFreeAp m = case tviewl m of
--         (Pure a :< r) -> a *> runFreeAp r
--         (Ap f :< r) -> error "Impossible"
--         TAEmptyL -> error "Impossible"

-- instance Applicative f => RunFreeApQ f (b -> c) c where
--     runFreeAp m = case tviewl m of
--         (Pure f' :< r) -> case tviewl r of
--             (Ap a :< r') -> runFreeAp (Ap (f' <*> a) <| r')
--             -- *> discarded application
--             (Pure a :< r') -> f' *> (runFreeAp $ Pure a <| r')
--             -- TAEmptyL -> error "Impossible" 
--         (Ap a :< r') -> a *> runFreeAp r'
--         -- TAEmptyL -> error "Impossible"

-- instance RunFreeApQ f (b -> c) y => RunFreeApQ f (a -> b -> c) y where
--     runFreeAp m = case tviewl m of
--         (Pure f' :< r) -> case tviewl r of
--             (Ap a :< r') -> runFreeAp (Ap (f' <*> a) <| r')
--             (Pure a :< r') -> f' *> (runFreeAp $ Pure a <| r')
--             TAEmptyL -> f'
--         (Ap a :< r') -> a *> runFreeAp r'
--         TAEmptyL -> error "Impossible"

-- data FreeF f i b = forall a. FreeF !(f i a) !(a -> b)

-- instance Functor (FreeF f i) where
--     fmap f (FreeF t q) = FreeF t (f . q) 

-- newtype FreeAp f a = FreeAp { unFreeAp :: forall i. FreeF (FingerTree (FreeApQ f)) i a } 

-- -- class Applicative f => ApFreeApQ f i j where
-- --     apFree :: FingerTree (FreeApQ f) i j -> FreeApQ f (j -> k) k -> FingerTree (FreeApQ f) (j -> k) k

-- -- instance ApFreeApQ f i j where
-- --     apFree q s = q |> s


-- apFree :: FingerTree (FreeApQ f) (a -> b -> c) (b -> c) -> FreeApQ f (b -> c) c -> FingerTree (FreeApQ f) (a -> b -> c) c
-- apFree q s = q |> s

-- -- apFree' :: FingerTree (FreeApQ f) i j -> FingerTree (FreeApQ f) j k -> FingerTree (FreeApQ f) i k
-- -- apFree' q s = q >< s

-- instance Functor (FreeAp f) where
--     fmap f (FreeAp t) = FreeAp (fmap f t)

-- instance IxApplicative (FingerTree (FreeApQ f)) where
--     iap m k = _ m k

-- -- instance Applicative f => Applicative (FreeAp f) where
-- --     (FreeAp (FreeF a@(_) q)) <*> (FreeAp (FreeF k@(_) q')) = case tviewl k of
-- --         (Pure k' :< r) -> (FreeAp $ FreeF (a |> Pure k')) undefined) <*> undefined
            
--             --  FreeAp $ FreeF (a >< coerce k) (undefined)