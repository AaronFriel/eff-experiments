{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds, PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
-- {-# LANGUAGE ConstraintKinds #-}

-- {-# LANGUAGE Strict #-}

-- Open unions (type-indexed co-products) for extensible effects
-- All operations are constant-time, and there is no Typeable constraint

module Data.Iota.OpenUnion51 (
  Union (..),
  Member (..),
  KnownNat,
  FindElem,
  decomp,
  weaken,
  elemNo',
  succ',
  pred',
) where

import Unsafe.Coerce(unsafeCoerce)
import GHC.TypeLits hiding (type (*))
import Data.Proxy
import Data.Type.Equality
import GHC.Exts (inline)
-- import Debug.Trace

import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.Decide
-- import Data.Singletons.Prelude.Num
-- import Data.Singletons.Prelude.Enum
import Data.Singletons.TypeLits

-- The data constructors of Union are not exported

-- Strong Sum (Existential with the evidence) is an open union
-- t is can be a GADT and hence not necessarily a Functor.
-- Int is the index of t in the list r; that is, the index of t in the
-- universe r
data Union (n :: Nat) (r :: [ * -> * ]) v where
  Union :: t v -> Union n r v

-- Find an index of an element in a `list'
-- The element must exist
-- This is essentially a compile-time computation.
elemNo' :: forall t r. KnownNat (FindElem t r) => Sing (FindElem t r)
elemNo' = SNat @(FindElem t r)

{-# INLINE [2] withKnownNat' #-}
withKnownNat' :: forall n r. Sing n -> (KnownNat n => r) -> r
withKnownNat' SNat f = f
{-# RULES
  "withKnownNat'"     forall n f. withKnownNat' n f = f
#-}

{-# INLINE [2] succ' #-}
succ' :: forall n r. (KnownNat n) => Sing n -> (KnownNat (n + 1) => r) -> r
succ' SNat f = withKnownNat' (SNat @n %:+ SNat @1) f
{-# RULES
  "succ'"     forall n f. succ' n f = f
#-}

{-# INLINE [2] pred' #-}
pred' :: forall n r. (KnownNat n) => Sing n -> (KnownNat (n - 1) => r) -> r
pred' SNat f = withKnownNat' (SNat @n %:- SNat @1) f
{-# RULES
  "pred'"     forall n f. pred' n f = f
#-}

-- instance {-# OVERLAPS #-} FindElem' t r => FindElem' t (t' ': r) where
--   elemNo = P $ 1 + (elemNo @t @r)

-- findElem :: forall t n r v. Union n r v -> SNat (FindElem' t r)
-- findElem (Union x) =
--   case (unsafeCoerce x :: t v2) of
--     _ -> case Proxy @t :~: FindElem
  -- case Proxy

-- type family MemberFamily (t :: * -> *) r :: Constraint where
--     MemberFamily t (t ': r) = (FindElem t (t ': r) ~ 0)
--     MemberFamily t (_ ': r) = MemberFamily t r

type family FindElem (t :: * -> *) r :: Nat where
    FindElem t (t ': r) = 0
    FindElem t (u ': r) = 1 + FindElem t r
    FindElem t _  = TypeError ('Text "The type " ':<>: 'ShowType t ':<>: 'Text " is not an element in the universe provided.")

-- elemNo' :: forall t r. (MemberFamily t r, KnownNat (FindElem t r)) => Integer
-- elemNo' = natVal (Proxy @(FindElem t r))

-- class (MemberFamily t r, KnownNat (FindElem t r)) => Member (t :: * -> *) r where
class (KnownNat (FindElem t r)) => Member t r where
  inj :: t v -> Union (FindElem t r) r v
  -- prj :: forall n t r v i. (MemberFamily t r, i ~ FindElem t r) => Union n r v -> Maybe (t v)
  -- prj :: forall n t r v. (KnownNat n) => Union n r v -> Maybe (t v)
  prj :: forall n v. KnownNat n => Union n r v -> Maybe (t v)

instance (KnownNat (FindElem t r)) => Member (t :: * -> *) r where
  inj = Union @_ @(FindElem t r)

  prj :: forall n v. KnownNat n => Union n r v -> Maybe (t v)
  prj (Union x) =
    case SNat @n %~ SNat @(FindElem t r) of
      Proved _  -> Just (unsafeCoerce x)
      _         -> Nothing

{-# INLINE [2] decomp #-}
decomp :: forall n t r v. KnownNat n => Union n (t ': r) v -> Either (Union (n - 1) r v) (t v)
-- decomp (Union v) = (withNatOp (%-) (Proxy @n) (Proxy @1)) $
decomp (Union v) =
   case SNat @n %~ SNat @0 of
     Proved _  -> Right $ unsafeCoerce v
     _         -> pred' (SNat @n) $ Left $ Union v

weaken :: forall n r w any. KnownNat n => Union n r w -> Union (n + 1) (any ': r) w
weaken (Union v) = succ' (SNat @n) $ Union v
