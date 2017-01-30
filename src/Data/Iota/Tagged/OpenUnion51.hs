{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds, PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
-- {-# LANGUAGE OverlappingInstances #-}

-- Only for MemberU below, when emulating Monad Transformers
{-# LANGUAGE FunctionalDependencies, UndecidableInstances #-}

{-# LANGUAGE Strict #-}

-- Open unions (type-indexed co-products) for extensible effects
-- All operations are constant-time, and there is no Typeable constraint

-- This is a variation of OpenUion5.hs, which relies on overlapping
-- instances instead of closed type families. Closed type families
-- have their problems: overlapping instances can resolve even
-- for unground types, but closed type families are subject to a
-- strict apartness condition.

-- This implementation is very similar to OpenUnion1.hs, but without
-- the annoying Typeable constraint. We sort of emulate it:

-- Our list r of open union components is a small Universe.
-- Therefore, we can use the Typeable-like evidence in that
-- universe. We hence can define
--
-- data Union r v where
--  Union :: t v -> TRep t r -> Union r v -- t is existential
-- where
-- data TRep t r where
--  T0 :: TRep t (t ': r)
--  TS :: TRep t r -> TRep (any ': r)
-- Then Member is a type class that produces TRep
-- Taken literally it doesn't seem much better than
-- OpenUinion41.hs. However, we can cheat and use the index of the
-- type t in the list r as the TRep. (We will need UnsafeCoerce then).

-- The interface is the same as of other OpenUnion*.hs
module Data.Iota.Tagged.OpenUnion51 (Union, inj, prj, decomp,
                   Member, MemberU2, weaken
                  ) where

import Unsafe.Coerce(unsafeCoerce)
import Data.Word (Word8)
type Index = Word8
-- The data constructors of Union are not exported

-- Strong Sum (Existential with the evidence) is an open union
-- t is can be a GADT and hence not necessarily a Functor.

-- Index is the index of t in the list r; that is, the index of t in the
-- universe r
data Union (r :: [ * -> * ]) (v :: k) where
  Union0 :: t v -> Union r v
  Union1 :: t v -> Union r v
  Union2 :: t v -> Union r v
  Union3 :: t v -> Union r v
  Union4 :: t v -> Union r v
  Union5 :: t v -> Union r v
  Union :: {-# UNPACK #-} !Index -> t v -> Union r v

{-# INLINE prj' #-}
{-# INLINE inj' #-}
inj' :: Index -> t v -> Union r v
inj' 0 = Union0
inj' 1 = Union1
inj' 2 = Union2
inj' 3 = Union3
inj' 4 = Union4
inj' 5 = Union5
inj' n = Union n

prj' :: Index -> Union r v -> Maybe (t v)
prj' 0 (Union0 x)   = Just (unsafeCoerce x)
prj' 1 (Union1 x)   = Just (unsafeCoerce x)
prj' 2 (Union2 x)   = Just (unsafeCoerce x)
prj' 3 (Union3 x)   = Just (unsafeCoerce x)
prj' 4 (Union4 x)   = Just (unsafeCoerce x)
prj' 5 (Union5 x)   = Just (unsafeCoerce x)
prj' n (Union n' x) | n == n'   = Just (unsafeCoerce x)
                    | otherwise = Nothing
prj' _ _            = Nothing

newtype P t r = P{unP :: Index}

class (FindElem t r) => Member (t :: * -> *) r where
  inj :: t v -> Union r v
  prj :: Union r v -> Maybe (t v)

-- Optimized specialized instance
instance {-# INCOHERENT #-} Member t '[t] where
  {-# INLINE inj #-}
  {-# INLINE prj #-}
  inj x           = Union 0 x
  prj (Union0 x) = Just (unsafeCoerce x)
  prj (Union1 x) = Just (unsafeCoerce x)
  prj (Union2 x) = Just (unsafeCoerce x)
  prj (Union3 x) = Just (unsafeCoerce x)
  prj (Union4 x) = Just (unsafeCoerce x)
  prj (Union5 x) = Just (unsafeCoerce x)
  prj (Union _ x) = Just (unsafeCoerce x)

instance {-# INCOHERENT #-} (FindElem t r) => Member t r where
  {-# INLINE inj #-}
  {-# INLINE prj #-}
  inj = inj' (unP $ (elemNo :: P t r))
  prj = prj' (unP $ (elemNo :: P t r))

{-# INLINE [2] decomp #-}
decomp :: Union (t ': r) v -> Either (Union r v) (t v)
decomp (Union0 v) = Right $ unsafeCoerce v
decomp (Union1 v) = Left $ Union0 v
decomp (Union2 v) = Left $ Union1 v
decomp (Union3 v) = Left $ Union2 v
decomp (Union4 v) = Left $ Union3 v
decomp (Union5 v) = Left $ Union4 v
decomp (Union n v) = Left $ if n == 6 then Union5 v else Union (n-1) v

-- Specialized version
{-# RULES "decomp/singleton"  decomp = decomp0 #-}
{-# INLINE decomp0 #-}
decomp0 :: Union '[t] v -> Either (Union '[] v) (t v)
decomp0 (Union0 v) = Right $ unsafeCoerce v
decomp0 _          = error "Not possible"
-- decomp0 (Union1 v) = Right $ unsafeCoerce v
-- decomp0 (Union2 v) = Right $ unsafeCoerce v
-- decomp0 (Union3 v) = Right $ unsafeCoerce v
-- decomp0 (Union4 v) = Right $ unsafeCoerce v
-- decomp0 (Union5 v) = Right $ unsafeCoerce v
-- decomp0 (Union _ v) = Right $ unsafeCoerce v
-- No other case is possible

weaken :: Union r w -> Union (any ': r) w
weaken (Union0 v) = Union1 v
weaken (Union1 v) = Union2 v
weaken (Union2 v) = Union3 v
weaken (Union3 v) = Union4 v
weaken (Union4 v) = Union5 v
weaken (Union5 v) = Union 6 v
weaken (Union n v) = Union (n+1) v

-- Find an index of an element in a `list'
-- The element must exist
-- This is essentially a compile-time computation.
class FindElem (t :: * -> *) r where
  elemNo :: P t r

instance {-# OVERLAPPING #-} FindElem t (t ': r) where
  elemNo = P 0

instance {-# OVERLAPS #-} FindElem t r => FindElem t (t' ': r) where
  elemNo = P $ 1 + (unP $ (elemNo :: P t r))

type family EQU (a :: k) (b :: k) :: Bool where
  EQU a a = 'True
  EQU a b = 'False

-- This class is used for emulating monad transformers
class Member t r => MemberU2 (tag :: k -> * -> *) (t :: * -> *) r | tag r -> t
instance (MemberU' (EQU t1 t2) tag t1 (t2 ': r)) => MemberU2 tag t1 (t2 ': r)

class Member t r =>
      MemberU' (f::Bool) (tag :: k -> * -> *) (t :: * -> *) r | tag r -> t
instance MemberU' 'True tag (tag e) (tag e ': r)
instance (Member t (t' ': r), MemberU2 tag t r) =>
           MemberU' 'False tag t (t' ': r)
