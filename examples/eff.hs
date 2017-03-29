-- In extensible effects, the operators are dumb data types. 
-- We need to enable a few language extensions...
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

-- ... and import some machinery here.
import Unsafe.Coerce(unsafeCoerce)
-- Included at end of file:
-- import Eff.Internal.OpenUnion51
-- import Eff.Internal.FTCQueue1

f :: Eff '[State Int] ()
f = do
    x :: Int <- get
    put (x * x)
    return ()

-- We run it with:
runF = run (runState f 100)

-- and runF == 10000
ranF = (runF == ((), 10000)) -- returns True

-- Here's our State data type: just defines two operations, Get and Put.
data State s v where
  Get :: State s s
  Put :: !s -> State s ()

-- Now get and put are really simple:
get = send Get
put s = send (Put s)

-- But unlike with regular monads, instead of "runState" being really simple
-- here it's quite a bit more involved!
-- But note that it now contains all of the logic here:
runState :: Eff (State s ': r) w -> s -> Eff r (w,s)
runState (Val x) s = return (x,s)
runState (E u q) s = case decomp u of
  -- If it's a "get", apply (qApp) the state parameter, and recurse:
  Right Get        -> runState (qApp q s) s
  -- If it's a "put", apply (qApp) the unit value (), and recurse with the new state:
  Right (Put new) -> runState (qApp q ()) new
  -- And this is how it handles layering multiple effects, but we can ignore it.
  Left  u -> E u (tsingleton (\x -> runState (qApp q x) s))

-- But we need to define our central data type, this wacky thing:
data Eff r a where
  Val :: a -> Eff r a
  E   :: Union r b -> FTCQueue (Eff r) b a -> Eff r a

-- And this method of adding effects:
send :: Member t r => t v -> Eff r v
send t = E (inj t) (tsingleton Val)

-- Get the value out at the end:
run :: Eff '[] w -> w
run (Val x) = x

-- A helper function:
qApp :: FTCQueue (Eff r) b w -> b -> Eff r w
qApp q x =
   case tviewl q of
     TOne k  -> k x
     k :| t -> case k x of
       Val y -> qApp t y
       E u q -> E u (q >< t)

-- Finally, the type class definitions just seem to move values around without doing anything:
instance Monad (Eff r) where
  {-# INLINE return #-}
  {-# INLINE [2] (>>=) #-}
  return x = Val x
  Val x >>= k = k x
  E u q >>= k = E u (q |> k)          -- just accumulates continuations

instance Applicative (Eff r) where
  {-# INLINE pure #-}
  pure = Val
  {-# INLINE (<*>) #-}
  Val f <*> Val x = Val $ f x
  Val f <*> E u q = E u (q |> (Val . f))
  E u q <*> Val x = E u (q |> (Val . ($ x)))
  E u q <*> m     = E u (q |> (`fmap` m))

instance Functor (Eff r) where
  {-# INLINE fmap #-}
  fmap f (Val x) = Val (f x)
  fmap f (E u q) = E u (q |> (Val . f)) -- does no mapping yet!

-- Eff/Internal/OpenUnion51.hs:

-- The data constructors of Union are not exported

-- Strong Sum (Existential with the evidence) is an open union
-- t is can be a GADT and hence not necessarily a Functor.
-- Int is the index of t in the list r; that is, the index of t in the
-- universe r
data Union (r :: [ * -> * ]) (v :: k) where
  Union :: {-# UNPACK #-} !Int -> t v -> Union r v

{-# INLINE prj' #-}
{-# INLINE inj' #-}
inj' :: Int -> t v -> Union r v
inj' = Union

prj' :: Int -> Union r v -> Maybe (t v)
prj' n (Union n' x) | n == n'   = Just (unsafeCoerce x)
                    | otherwise = Nothing

newtype P t r = P{unP :: Int}

class (FindElem t r) => Member (t :: * -> *) r where
  inj :: t v -> Union r v
  prj :: Union r v -> Maybe (t v)

-- Optimized specialized instance
instance {-# INCOHERENT #-} Member t '[t] where
  {-# INLINE inj #-}
  {-# INLINE prj #-}
  inj x           = Union 0 x
  prj (Union _ x) = Just (unsafeCoerce x)

instance {-# INCOHERENT #-} (FindElem t r) => Member t r where
  {-# INLINE inj #-}
  {-# INLINE prj #-}
  inj = inj' (unP $ (elemNo :: P t r))
  prj = prj' (unP $ (elemNo :: P t r))

{-# INLINE [2] decomp #-}
decomp :: Union (t ': r) v -> Either (Union r v) (t v)
decomp (Union 0 v) = Right $ unsafeCoerce v
decomp (Union n v) = Left  $ Union (n-1) v


-- Specialized version
{-# RULES "decomp/singleton"  decomp = decomp0 #-}
{-# INLINE decomp0 #-}
decomp0 :: Union '[t] v -> Either (Union '[] v) (t v)
decomp0 (Union _ v) = Right $ unsafeCoerce v
-- No other case is possible

weaken :: Union r w -> Union (any ': r) w
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

-- Eff/Internal/FTCQueue1.hs

-- Non-empty tree. Deconstruction operations make it more and more
-- left-leaning

data FTCQueue m a b where
  Leaf :: (a -> m b) -> FTCQueue m a b
  Node :: FTCQueue m a x -> FTCQueue m x b -> FTCQueue m a b

-- Exported operations

-- There is no tempty: use (tsingleton return), which works just the same.
-- The names are chosen for compatibility with FastTCQueue

{-# INLINE tsingleton #-}
tsingleton :: (a -> m b) -> FTCQueue m a b
tsingleton r = Leaf r

-- snoc: clearly constant-time
{-# INLINE (|>) #-}
(|>) :: FTCQueue m a x -> (x -> m b) -> FTCQueue m a b
t |> r = Node t (Leaf r)

-- append: clearly constant-time
{-# INLINE (><) #-}
(><) :: FTCQueue m a x -> FTCQueue m x b -> FTCQueue m a b
t1 >< t2 = Node t1 t2

-- Left-edge deconstruction
data ViewL m a b where
  TOne  :: (a -> m b) -> ViewL m a b
  (:|)  :: (a -> m x) -> (FTCQueue m x b) -> ViewL m a b

{-# INLINABLE tviewl #-}
tviewl :: FTCQueue m a b -> ViewL m a b
tviewl (Leaf r) = TOne r
tviewl (Node t1 t2) = go t1 t2
 where
   go :: FTCQueue m a x -> FTCQueue m x b -> ViewL m a b
   go (Leaf r) tr = r :| tr
   go (Node tl1 tl2) tr = go tl1 (Node tl2 tr)
