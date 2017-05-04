{-# LANGUAGE GADTs,TypeSynonymInstances,FlexibleInstances,Rank2Types #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeInType #-}

module Control.Monad.Graph.ApSeq where

import Control.Monad.Indexed

import Data.Coerce

import Debug.Trace 

class TASequence s where

  tempty     :: s c x x
  tsingleton :: c x y -> s c x y
  -- | Append two type aligned sequences
  (><)       :: s c x y -> s c y z  -> s c x z
  -- | View a type aligned sequence from the left
  tviewl     :: s c x y -> TAViewL s c x y
  -- | View a type aligned sequence from the right
  --       
  -- Default definition:
  -- 
  -- > tviewr q = case tviewl q of 
  -- >   TAEmptyL -> TAEmptyR
  -- >   h :< t -> case tviewr t of
  -- >        TAEmptyR -> tempty   :> h
  -- >        p :> l   -> (h <| p) :> l
  tviewr     :: s c x y -> TAViewR s c x y
  -- | Append a single element to the right
  --
  -- Default definition:
  -- 
  -- > l |> r = l >< tsingleton r

  (|>)       :: s c x y -> c y z -> s c x z
  -- | Append a single element to the left
  -- 
  -- Default definition:
  --
  -- > l <| r = tsingleton l >< r

  (<|)       :: c x y -> s c y z -> s c x z
  -- | Apply a function to all elements in a type aligned sequence
  -- 
  -- Default definition:
  -- 
  -- > tmap f q = case tviewl q of
  -- >    TAEmptyL -> tempty
  -- >    h :< t -> f h <| tmap f t
  tmap       :: (forall x y. c x y -> d x y) -> s c x y -> s d x y
  
  l |> r = l >< tsingleton r
  l <| r = tsingleton l >< r
  l >< r = case tviewl l of
    TAEmptyL -> r
    h :< t  -> h <| (t >< r)

  tviewl q = case tviewr q of 
    TAEmptyR -> TAEmptyL
    p :> l -> case tviewl p of
        TAEmptyL -> l :< tempty
        h :< t   -> h :< (t |> l)

  tviewr q = case tviewl q of 
    TAEmptyL -> TAEmptyR
    h :< t -> case tviewr t of
        TAEmptyR -> tempty   :> h
        p :> l   -> (h <| p) :> l

  tmap f q = case tviewl q of
    TAEmptyL -> tempty
    h :< t -> f h <| tmap f t


data TAViewL s c x y where
   TAEmptyL  :: TAViewL s c x x
   (:<)     :: c x y -> s c y z -> TAViewL s c x z

data TAViewR s c x y where
   TAEmptyR  :: TAViewR s c x x
   (:>)     :: s c x y -> c y z -> TAViewR s c x z



data SnocList c x y where
  SNil :: SnocList c x x
  Snoc :: SnocList c x y -> c y z -> SnocList c x z

instance TASequence SnocList where
  tempty = SNil
  tsingleton c = Snoc SNil c 
  (|>) = Snoc
  tviewr SNil = TAEmptyR
  tviewr (Snoc p l) = p :> l
  tmap phi SNil = SNil
  tmap phi (Snoc s c) = Snoc (tmap phi s) (phi c)

data ConsList c x y where
  CNil :: ConsList c x x
  Cons :: c x y -> ConsList c y z -> ConsList c x z

instance TASequence ConsList where
  tempty = CNil
  tsingleton c = Cons c CNil
  (<|) = Cons
  tviewl CNil = TAEmptyL
  tviewl (Cons h t) = h :< t


revAppend l r = rotate l r CNil
-- precondtion : |a| = |f| - (|r| - 1)
-- postcondition: |a| = |f| - |r|
rotate :: ConsList tc a b -> SnocList tc b c -> ConsList tc c d -> ConsList tc a d
rotate CNil  (SNil `Snoc` y) r = y `Cons` r
rotate (x `Cons` f) (r `Snoc` y) a = x `Cons` rotate f r (y `Cons` a)
rotate f        a     r  = error "Invariant |a| = |f| - (|r| - 1) broken"

data FastQueue tc a b where
  RQ :: !(ConsList tc a b) -> !(SnocList tc b c) -> !(ConsList tc x b) -> FastQueue tc a c

queue :: ConsList tc a b -> SnocList tc b c -> ConsList tc x b -> FastQueue tc a c
queue f r CNil = let f' = revAppend f r 
                 in RQ f' SNil f'
queue f r (h `Cons` t) = RQ f r t


instance TASequence FastQueue where
 tempty = RQ CNil SNil CNil
 tsingleton x = let c = tsingleton x in queue c SNil c
 (RQ f r a) |> x = queue f (r `Snoc` x) a

 tviewl (RQ CNil SNil CNil) = TAEmptyL
 tviewl (RQ (h `Cons` t) f a) = h :< queue t f a

 tmap phi (RQ a b c) = RQ (tmap phi a) (tmap phi b) (tmap phi c)

data FingerTree r a b where
  Empty  :: FingerTree r a a
  Single :: r a b -> FingerTree r a b
  Deep   :: !(Digit r a b) -> FingerTree (Node r) b c -> !(Digit r c d) -> FingerTree r a d

data Node r a b where
  Node2 :: r a b -> r b c -> Node r a c
  Node3 :: r a b -> r b c -> r c d -> Node r a d

data Digit r a b where
  One   :: r a b -> Digit r a b
  Two   :: r a b -> r b c -> Digit r a c
  Three :: r a b -> r b c -> r c d -> Digit r a d
  Four  :: r a b -> r b c -> r c d -> r d e -> Digit r a e

instance TASequence FingerTree where
  tempty = Empty
  tsingleton = Single

  Empty                     |> a = Single a
  Single b                  |> a = Deep (One b) Empty (One a)
  Deep pr m (Four e d c b)  |> a = Deep pr (m |> Node3 e d c) (Two b a)
  Deep pr m sf              |> a = Deep pr m (appendd sf (One a))

  a <| Empty                     = Single a
  a <| Single b                  = Deep (One a) Empty (One b) 
  a <| Deep (Four b c d e) m sf  = Deep (Two a b) (Node3 c d e <| m) sf
  a <| Deep pr m sf              = Deep (appendd (One a) pr) m sf

  tviewl Empty = TAEmptyL
  tviewl (Single a) = a :< Empty
  tviewl (Deep pr m sf) = case toList pr of
              h ::: t -> h :< deepl t m sf

  tviewr Empty = TAEmptyR
  tviewr (Single a) = Empty :> a 
  tviewr (Deep pr m sf) = case toListR sf of
            h :::< t -> deepr pr m t :> h

  xs >< ys = app3 xs ZNil ys

  tmap f Empty = Empty
  tmap f (Single a) = Single (f a)
  tmap f (Deep l m r) = Deep (mapd f l) (tmap (mapn f) m) (mapd f r)



toTree :: Digit r a b -> FingerTree r a b
toTree (One a)         = Single a
toTree (Two a b)       = Deep (One a) Empty (One b)
toTree (Three a b c)   = Deep (Two a b) Empty (One c)
toTree (Four a b c d)  = Deep (Two a b) Empty (Two c d)


appendd :: Digit r a b -> Digit r b c -> Digit r a c
appendd (One a)        (One b)        = Two a b
appendd (One a)        (Two b c)      = Three a b c
appendd (Two a b)      (One c)        = Three a b c
appendd (One a)        (Three b c d)  = Four a b c d
appendd (Two a b)      (Two c d)      = Four a b c d
appendd (Three a b c)  (One d)        = Four a b c d






infixr 5 ::: 


data ZList r a b where
  ZNil :: ZList r a a
  (:::) :: r a b -> ZList r b c -> ZList r a c

toList (One a) = a ::: ZNil 
toList (Two a b) = a ::: b ::: ZNil
toList (Three a b c) = a ::: b ::: c ::: ZNil
toList (Four a b c d) = a ::: b ::: c ::: d ::: ZNil




fromList :: ZList r a b -> Digit r a b
fromList (a ::: ZNil) = One a
fromList (a ::: b ::: ZNil) = Two a b
fromList (a ::: b ::: c ::: ZNil) = Three a b c
fromList (a ::: b ::: c ::: d ::: ZNil) = Four a b c d

append :: ZList r a b -> ZList r b c -> ZList r a c
append ZNil t = t
append (h ::: t) r = h ::: append t r


deepl :: ZList r a b -> FingerTree (Node r) b c -> Digit r c d -> FingerTree r a d
deepl ZNil m sf = case tviewl m of
           TAEmptyL -> toTree sf
           a :< m' -> Deep (nodeToDigit a) m' sf 
deepl pr m sf = Deep (fromList pr) m sf

infixr 5 :::< 

data ZListR r a b where
  ZNilR :: ZListR r a a
  (:::<) :: r b c -> ZListR r a b -> ZListR r a c

toListR :: Digit r a b -> ZListR r a b
toListR (One a) = a :::< ZNilR
toListR (Two a b) = b :::< a :::< ZNilR
toListR (Three a b c) = c :::< b :::< a :::< ZNilR
toListR (Four a b c d) = d:::< c :::< b :::< a :::< ZNilR



fromListR :: ZListR r a b -> Digit r a b
fromListR (a :::< ZNilR) = One a
fromListR (b :::< a :::< ZNilR) = Two a b
fromListR (c :::< b :::< a :::< ZNilR) = Three a b c
fromListR (d :::< c :::< b :::< a :::< ZNilR) = Four a b c d


rev = toList . fromListR 



deepr :: Digit r a b -> FingerTree (Node r) b c -> ZListR r c d -> FingerTree r a d
deepr pr m ZNilR = case tviewr m of
           TAEmptyR -> toTree pr
           m' :> a -> Deep pr m' (nodeToDigit a)
deepr pr m sf = Deep pr m (fromListR sf)


nodeToDigit :: Node r a b -> Digit r a b
nodeToDigit (Node2 a b) = Two a b
nodeToDigit (Node3 a b c) = Three a b c



addAlll :: ZList r a b -> FingerTree r b c -> FingerTree r a c
addAlll ZNil m = m
addAlll (h ::: t) m = h <| addAlll t m

addAllr :: FingerTree r a b -> ZList r b c  -> FingerTree r a c
addAllr m ZNil  = m
addAllr m (h ::: t) = addAllr (m |> h) t

  

app3 :: FingerTree r a b -> ZList r b c -> FingerTree r c d -> FingerTree r a d
app3 Empty ts xs = addAlll ts xs
app3 xs ts Empty = addAllr xs ts
app3 (Single x) ts xs = x <| (addAlll ts xs)
app3 xs ts (Single x) = (addAllr xs ts) |> x
app3 (Deep pr1 m1 sf1) ts (Deep pr2 m2 sf2) =
    Deep pr1 
        (app3 m1 (nodes (append (toList sf1) (append ts (toList pr2)))) m2) sf2


nodes :: ZList r a b -> ZList (Node r) a b
nodes (a ::: b ::: ZNil) = Node2 a b ::: ZNil
nodes (a ::: b ::: c ::: ZNil) = Node3 a b c ::: ZNil
nodes (a ::: b ::: c ::: d ::: ZNil) = Node2 a b ::: Node2 c d ::: ZNil
nodes (a ::: b ::: c ::: xs) = Node3 a b c ::: nodes xs

mapn :: (forall x y. c x y -> d x y) -> Node c x y -> Node d x y
mapn phi (Node2 r s) = Node2 (phi r) (phi s)
mapn phi (Node3 r s t) = Node3 (phi r) (phi s) (phi t)
  
mapd :: (forall x y. c x y -> d x y) -> Digit c x y -> Digit d x y
mapd phi (One r) = One (phi r) 
mapd phi (Two r s) = Two (phi r) (phi s)
mapd phi (Three r s t) = Three (phi r) (phi s) (phi t)
mapd phi (Four r s t u) = Four (phi r) (phi s) (phi t) (phi u)


------------------------------------------------



data FreeApQ f i j where
    Pure :: f a -> FreeApQ f a a
    Ap :: f a -> FreeApQ f (a -> b) b

fsingleton x = Single x

t1 :: FingerTree (FreeApQ Maybe) (Char -> Char -> (Char, Char)) (Char, Char)
t1 = (fsingleton (Pure $ pure (,)) |> Ap (pure 'a')) |> Ap (pure 'b')

runFreeStep :: FingerTree (FreeApQ Maybe) (a -> b -> c) x 
   -> Maybe (FingerTree (FreeApQ Maybe) (b -> c) x)
runFreeStep t1 = case tviewl t1 of
    (Pure (Just f') :< r) -> case tviewl r of
        (Ap (Just a) :< r') -> Just $ Pure (pure $ f' a) <| r'  
        _ -> Nothing
    _ -> Nothing

runFreeStep' :: Applicative f => FingerTree (FreeApQ f) (a -> b -> c) x 
   -> f (FingerTree (FreeApQ f) (b -> c) x)
runFreeStep' t1 = case tviewl t1 of
    (Pure f' :< r) -> case tviewl r of
        (Ap a :< r') -> pure $ Pure (f' <*> a) <| r'
        -- (Pure a :< r') -> a *> (runFreeStep' $ Pure a <| r')
    _ -> undefined


runFreeStep'' :: Applicative f => FingerTree (FreeApQ f) (a -> b -> c) y
   -> f (FingerTree (FreeApQ f) (b -> c) y)
runFreeStep'' t1 = case tviewl t1 of
    (Pure f' :< r) -> case tviewl r of
        (Ap a :< r') -> pure $ Pure (f' <*> a) <| r'  
        -- (Pure a :< r') -> a *> (runFreeStep'' $ Pure a <| r')
    _ -> undefined

runFreeLast :: Applicative f
            => FingerTree (FreeApQ f) (b -> c) c
            -> f c
runFreeLast t1 = case tviewl t1 of
    (Pure f' :< r) -> case tviewl r of
        (Ap a :< r') -> f' <*> a
        -- *> or <*, discarded application
        (Pure a :< r') -> a *> (runFreeLast $ Pure a <| r')
    (Ap a :< r') -> error "Impossible, nothing to apply Ap to"

-- returns `Just ('a', 'b')`
t1r = case runFreeStep t1 of
    Just t1' -> case runFreeLast t1' of
        Just x -> Just x
        _ -> Nothing
    _ -> Nothing

-- runFreeAp :: Applicative f => FingerTree (FreeApQ f) (a -> y) x -> f x
-- runFreeAp r = case tviewl r of
--     TAEmptyL -> undefined

t2 :: Applicative f => f a -> f b -> f c -> FingerTree (FreeApQ f) (a -> b -> c -> (a, b, c)) (a, b, c)
t2 a b c= (tsingleton (Pure $ pure (,,)) |> Ap a) |> Ap b |> Ap c 

t2r a b c = runFreeAp (t2 a b c)

t3 a b c = (tsingleton (Pure $ pure (,,))) |> Ap a |> Ap b |> Ap c


class Applicative f => RunFreeApQ f i j where
    runFreeAp :: FingerTree (FreeApQ f) i j -> f j

instance Applicative f => RunFreeApQ f c c where
    runFreeAp m = case tviewl m of
        (Pure a :< r) -> a *> runFreeAp r
        (Ap f :< r) -> error "Impossible"
        TAEmptyL -> error "Impossible"

instance Applicative f => RunFreeApQ f (b -> c) c where
    runFreeAp m = case tviewl m of
        (Pure f' :< r) -> case tviewl r of
            (Ap a :< r') -> runFreeAp (Ap (f' <*> a) <| r')
            -- *> discarded application
            (Pure a :< r') -> f' *> (runFreeAp $ Pure a <| r')
            -- TAEmptyL -> error "Impossible" 
        (Ap a :< r') -> a *> runFreeAp r'
        -- TAEmptyL -> error "Impossible"

instance RunFreeApQ f (b -> c) y => RunFreeApQ f (a -> b -> c) y where
    runFreeAp m = case tviewl m of
        (Pure f' :< r) -> case tviewl r of
            (Ap a :< r') -> runFreeAp (Ap (f' <*> a) <| r')
            (Pure a :< r') -> f' *> (runFreeAp $ Pure a <| r')
            TAEmptyL -> f'
        (Ap a :< r') -> a *> runFreeAp r'
        TAEmptyL -> error "Impossible"

data FreeF f i b = forall a. FreeF !(f i a) !(a -> b)

instance Functor (FreeF f i) where
    fmap f (FreeF t q) = FreeF t (f . q) 

newtype FreeAp f a = FreeAp { unFreeAp :: forall i. FreeF (FingerTree (FreeApQ f)) i a } 

-- class Applicative f => ApFreeApQ f i j where
--     apFree :: FingerTree (FreeApQ f) i j -> FreeApQ f (j -> k) k -> FingerTree (FreeApQ f) (j -> k) k

-- instance ApFreeApQ f i j where
--     apFree q s = q |> s


apFree :: FingerTree (FreeApQ f) (a -> b -> c) (b -> c) -> FreeApQ f (b -> c) c -> FingerTree (FreeApQ f) (a -> b -> c) c
apFree q s = q |> s

-- apFree' :: FingerTree (FreeApQ f) i j -> FingerTree (FreeApQ f) j k -> FingerTree (FreeApQ f) i k
-- apFree' q s = q >< s

instance Functor (FreeAp f) where
    fmap f (FreeAp t) = FreeAp (fmap f t)

instance IxApplicative (FingerTree (FreeApQ f)) where
    iap m k = _ m k

-- instance Applicative f => Applicative (FreeAp f) where
--     (FreeAp (FreeF a@(_) q)) <*> (FreeAp (FreeF k@(_) q')) = case tviewl k of
--         (Pure k' :< r) -> (FreeAp $ FreeF (a |> Pure k')) undefined) <*> undefined
            
            --  FreeAp $ FreeF (a >< coerce k) (undefined)