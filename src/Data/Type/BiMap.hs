{- This module provides type-level finite maps.
The implementation is similar to that shown in the paper.
 "Embedding effect systems in Haskell" Orchard, Petricek 2014  -}

{-# LANGUAGE TypeOperators, PolyKinds, DataKinds, KindSignatures,
             TypeFamilies, UndecidableInstances, MultiParamTypeClasses,
             FlexibleInstances, GADTs, FlexibleContexts, ScopedTypeVariables,
             ConstraintKinds #-}
{-# LANGUAGE TypeInType #-}

{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

    -- (BiMapping(..), Union, Unionable, union, Var(..), BiMap(..),
    --  Combine, Combinable(..), Cmp,
    --  Nubable, nub,
    --  Lookup, Member, (:\), Split, split,
    --  IsMap, AsMap, asMap,
    --  Submap, submap)
module Data.Type.BiMap
where

import GHC.TypeLits hiding (type (*))
import Data.Type.Bool
import Data.Type.Equality
import Data.Type.Set (Cmp, Proxy(..), Flag(..), Sort, Filter, (:++))
import Data.Kind (type (*))

{- Throughout, type variables
   'k' ranges over "keys"
   'v'  ranges over "values"
   'kvp' ranges over "key-value-pairs"
   'm', 'n' range over "maps" -}

-- BiMappings
infixr 4 :<->
{-| A key-value pair -}
data BiMapping k v = k :<-> v

{-| Union of two finite maps -}
type Union m n = Nub (Sort (m :++ n))

{-| Apply 'Combine' to values with matching key (removes duplicate keys) -}
type family Nub t where
   Nub '[]                             = '[]
   Nub '[kvp]                          = '[kvp]
   Nub ((k :<-> v1) ': (k :<-> v2) ': m) = Nub ((k :<-> Combine v1 v2) ': m)
   Nub (kvp1 ': kvp2 ': s)             = kvp1 ': Nub (kvp2 ': s)

{-| Open type family for combining values in a map (that have the same key) -}
type family Combine (a :: v) (b :: v) :: v

{-| Delete elements from a map by key -}
type family (m :: [BiMapping k v]) :\ (c :: k) :: [BiMapping k v] where
     '[]               :\ k = '[]
     ((k :<-> v) ': m)  :\ k = m :\ k
     (kvp ': m)        :\ k = kvp ': (m :\ k)

{-| Lookup elements from a map -}
type family Lookup (m :: [BiMapping k v]) (c :: k) :: Maybe v where
            Lookup '[]               k = Nothing
            Lookup ((k :<-> v) ': m) k = Just v
            Lookup (kvp ': m)        k = Lookup m k

{-| Lookup elements from a map -}
type family CoLookup (m :: [BiMapping k v]) (c :: v) :: Maybe v where
            CoLookup '[]               v  = Nothing
            CoLookup ((k :<-> v) ': m) v  = Just v
            CoLookup (kvp ': m)        v  = CoLookup m v

{-| Membership test -}
type family Member (c :: k) (m :: [BiMapping k v]) :: Bool where
            Member k '[]               = False
            Member k ((k :<-> v) ': m) = True
            Member k (kvp ': m)        = Member k m

{-| Membership test -}
type family CoMember (c :: v) (m :: [BiMapping k v]) :: Bool where
            CoMember v '[]               = False
            CoMember v ((k :<-> v) ': m) = True
            CoMember v (kvp ': m)        = CoMember v m

-----------------------------------------------------------------
-- Value-level map with a type-level representation

{-| Pair a symbol (representing a variable) with a type -}
data Var k (v :: k) = Var

instance KnownSymbol k => Show (Var Symbol k) where
    show = symbolVal

instance KnownNat k => Show (Var Nat k) where
    show = show . natVal

{-| A value-level heterogenously-typed BiMap (with type-level representation in terms of lists) -}
data BiMap (n :: [BiMapping kindk *]) where
    Empty :: BiMap '[]
    Ext :: Var kindk k -> v -> BiMap m -> BiMap ((k :<-> v) ': m)

{-| Predicate to check if in normalised map form -}
type IsMap s = (s ~ Nub (Sort s))

{-| At the type level, normalise the list form to the map form -}
type AsMap s = Nub (Sort s)

{-| At the value level, noramlise the list form to the map form -}
asMap :: (Sortable s, Nubable (Sort s)) => BiMap s -> BiMap (AsMap s)
asMap x = nub (quicksort x)

instance Show (BiMap '[]) where
    show Empty = "{}"

instance (KnownSymbol k, Show v, Show' (BiMap s)) => Show (BiMap ((k :<-> v) ': s)) where
    show (Ext k v s) = "{" ++ show k ++ " :<-> " ++ show v ++ (show' s) ++ "}"

class Show' t where
    show' :: t -> String
instance Show' (BiMap '[]) where
    show' Empty = ""

instance (KnownSymbol k, Show v, Show' (BiMap s)) => Show' (BiMap ((k :<-> v) ': s)) where
    show' (Ext k v s) = ", " ++ show k ++ " :<-> " ++ show v ++ (show' s)

instance Eq (BiMap '[]) where
    Empty == Empty = True

instance (KnownSymbol k, Eq (Var Symbol k), Eq v, Eq (BiMap s)) => Eq (BiMap ((k :<-> v) ': s)) where
    (Ext k v m) == (Ext k' v' m') = k == k' && v == v' && m == m'

{-| Union of two finite maps -}
union :: (Unionable s t) => BiMap s -> BiMap t -> BiMap (Union s t)
union s t = nub (quicksort (append s t))

type Unionable s t = (Nubable (Sort (s :++ t)), Sortable (s :++ t))

append :: BiMap s -> BiMap t -> BiMap (s :++ t)
append Empty x = x
append (Ext k v xs) ys = Ext k v (append xs ys)

type instance Cmp (k :: Symbol) (k' :: Symbol) = CmpSymbol k k'
type instance Cmp (k :<-> v) (k' :<-> v') = CmpSymbol k k'

{-| Value-level quick sort that respects the type-level ordering -}
class Sortable xs where
    quicksort :: BiMap xs -> BiMap (Sort xs)

instance Sortable '[] where
    quicksort Empty = Empty

-- Since we are using a bijection, we only need to compare on the key, which we guarantee to be sortable.
instance (Sortable (Filter FMin (k :<-> v) xs),
          Sortable (Filter FMax (k :<-> v) xs)) => Sortable ((k :<-> v) ': xs) where
    quicksort (Ext k v xs) = ((quicksort (less k v xs)) `append` (Ext k v Empty)) `append` (quicksort (more k v xs))
                              where less = filterV (Proxy::(Proxy FMin))
                                    more = filterV (Proxy::(Proxy FMax))

{- Filter out the elements less-than or greater-than-or-equal to the pivot -}
-- class FilterV (f::Flag) k v xs where
--     filterV :: Proxy f -> Var Symbol k -> v -> BiMap xs -> BiMap (Filter f (k :<-> v) xs)

-- instance FilterV f k v '[] where
--     filterV _ k v Empty      = Empty

-- instance (Conder ((Cmp x (k :<-> v)) == LT), FilterV FMin k v xs) => FilterV FMin k v (x ': xs) where
--     filterV f@Proxy k v (Ext k' v' xs) = cond (Proxy::(Proxy ((Cmp x (k :<-> v)) == LT)))
--                                         (Ext k' v' (filterV f k v xs)) (filterV f k v xs)

-- instance (Conder (((Cmp x (k :<-> v)) == GT) || ((Cmp x (k :<-> v)) == EQ)), FilterV FMax k v xs) => FilterV FMax k v (x ': xs) where
--     filterV f@Proxy k v (Ext k' v' xs) = cond (Proxy::(Proxy (((Cmp x (k :<-> v)) == GT) || ((Cmp x (k :<-> v)) == EQ))))
--                                         (Ext k' v' (filterV f k v xs)) (filterV f k v xs)

class Combinable t t' where
    combine :: t -> t' -> Combine t t'

class Nubable t where
    nub :: BiMap t -> BiMap (Nub t)

instance Nubable '[] where
    nub Empty = Empty

instance Nubable '[e] where
    nub (Ext k v Empty) = Ext k v Empty

instance {-# OVERLAPPABLE #-}
     (Nub (e ': f ': s) ~ (e ': Nub (f ': s)),
              Nubable (f ': s)) => Nubable (e ': f ': s) where
    nub (Ext k v (Ext k' v' s)) = Ext k v (nub (Ext k' v' s))

instance {-# OVERLAPS #-}
    (Combinable v v', Nubable ((k :<-> Combine v v') ': s)) => Nubable ((k :<-> v) ': (k :<-> v') ': s) where
    nub (Ext k v (Ext k' v' s)) = nub (Ext k (combine v v') s)

class Conder g where
    cond :: Proxy g -> BiMap s -> BiMap t -> BiMap (If g s t)

instance Conder True where
    cond _ s t = s

instance Conder False where
    cond _ s t = t

{-| Splitting a union of maps, given the maps we want to split it into -}
class Split s t st where
   -- where st ~ Union s t
   split :: BiMap st -> (BiMap s, BiMap t)

instance Split '[] '[] '[] where
   split Empty = (Empty, Empty)

instance {-# OVERLAPPABLE #-} Split s t st => Split (x ': s) (x ': t) (x ': st) where
   split (Ext k v st) = let (s, t) = split st
                        in (Ext k v s, Ext k v t)

instance {-# OVERLAPS #-} Split s t st => Split (x ': s) t (x ': st) where
   split (Ext k v st) = let (s, t) = split st
                        in  (Ext k v s, t)

instance {-# OVERLAPS #-} (Split s t st) => Split s (x ': t) (x ': st) where
   split (Ext k v st) = let (s, t) = split st
                        in  (s, Ext k v t)

{-| Construct a submap 's' from a supermap 't' -}
class Submap s t where
   submap :: BiMap t -> BiMap s

instance Submap '[] '[] where
   submap xs = Empty

instance {-# OVERLAPPABLE #-} Submap s t => Submap s (x ': t) where
   submap (Ext _ _ xs) = submap xs

instance {-# OVERLAPS #-} Submap s t => Submap  (x ': s) (x ': t) where
   submap (Ext k v xs) = Ext k v (submap xs)