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
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MagicHash #-}

{-# LANGUAGE StrictData #-}

module Data.Iota.Unified.Eff2
 where

import Unsafe.Coerce(unsafeCoerce)
import GHC.TypeLits hiding (type (*))
import Data.Proxy
import Data.Type.Equality
import GHC.Exts (inline)
import GHC.Prim (Proxy#, proxy#)
import qualified Debug.Trace as Debug

import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Num
import Data.Singletons.Decide
-- import Data.Singletons.Prelude.Num
-- import Data.Singletons.Prelude.Enum
import Data.Singletons.TypeLits

import Control.Monad
import Control.Applicative
import Data.Kind

--  ███████ ████████  ██████  ██████  ██    ██ ███████ ██    ██ ███████
--  ██         ██    ██      ██    ██ ██    ██ ██      ██    ██ ██
--  █████      ██    ██      ██    ██ ██    ██ █████   ██    ██ █████
--  ██         ██    ██      ██ ▄▄ ██ ██    ██ ██      ██    ██ ██
--  ██         ██     ██████  ██████   ██████  ███████  ██████  ███████
--                               ▀▀

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
tsingleton = Leaf

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
  (:|)  :: (a -> m x) -> FTCQueue m x b -> ViewL m a b

{-# INLINABLE tviewl #-}
tviewl :: FTCQueue m a b -> ViewL m a b
tviewl (Leaf r) = TOne r
tviewl (Node t1 t2) = go t1 t2
 where
   go :: FTCQueue m a x -> FTCQueue m x b -> ViewL m a b
   go (Leaf r) tr = r :| tr
   go (Node tl1 tl2) tr = go tl1 (Node tl2 tr)

--  ███████  █████  ███    ███ ██ ██      ██ ███████ ███████
--  ██      ██   ██ ████  ████ ██ ██      ██ ██      ██
--  █████   ███████ ██ ████ ██ ██ ██      ██ █████   ███████
--  ██      ██   ██ ██  ██  ██ ██ ██      ██ ██           ██
--  ██      ██   ██ ██      ██ ██ ███████ ██ ███████ ███████

type family FindElem (t :: * -> *) r :: Nat where
    FindElem t (t ': r) = 0
    FindElem t (u ': r) = 1 :+ FindElem t r
    FindElem t _  = TypeError ('Text "The type " ':<>: 'ShowType t ':<>: 'Text " is not an element in the universe provided.")

type family Length r :: Nat where
    Length '[] = 0
    Length (u ': r) = 1 :+ Length r

-- type family Last r where
--     Last (u ': '[]) = u
--     Last (u ': r)   = Last r

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

-- ███████ ███████ ███████
-- ██      ██      ██
-- █████   █████   █████
-- ██      ██      ██
-- ███████ ██      ██

type Arr r h a b = a -> Eff r h b

type Arrs r h a b = FTCQueue (Eff r h) a b

-- Combines "Union" and "Eff"

data Eff r h a where
  Val :: a -> Eff r h a
  E   :: KnownNat (FindElem t r) => t v -> Arrs r h b a -> Eff r h a

instance Functor (Eff r h) where
  {-# INLINE fmap #-}
  fmap f (Val x) = Val (f x)
  fmap f (E u q) = E u (q |> (Val . f)) -- does no mapping yet!

instance Applicative (Eff r h) where
  {-# INLINE pure #-}
  pure = Val
  {-# INLINE (<*>) #-}
  Val f <*> Val x = Val $ f x
  Val f <*> E u q = E u (q |> (Val . f))
  E u q <*> Val x = E u (q |> (Val . ($ x)))
  E u q <*> E u' q' = E u (q |> (\f -> E u' (q' |> (Val . f))))
  -- -- E u q <*> E u' q' = E u (q |> (`fmap` (E u' q')))
  -- E u q <*> m     = E u (q |> (`fmap` m))

instance Monad (Eff r h) where
  {-# INLINE return #-}
  {-# INLINE [2] (>>=) #-}
  return = Val
  Val x >>= k = k x
  E u q >>= k = E u (q |> k)          -- just accumulates continuations

-- {-# INLINE run #-}
run :: Eff '[] h w -> w
run (Val x) = x
-- run (E _ _) = error "unreachable"

{-# INLINEABLE qApp #-}
qApp :: Arrs r h b w -> b -> Eff r h w
qApp q x =
   case inline tviewl q of
     TOne k  -> k x
     k :| t -> case k x of
       Val y -> qApp t y
       E u q -> E u (q >< t)

{-# INLINE qComp #-}
qComp :: Arrs r h a b -> (Eff r h b -> Eff r' h' c) -> Arr r' h' a c
qComp g h = \a -> h $ qApp g a

-- qComp = \a -> h $
--    case inline tviewl g of
--      TOne k  -> k a
--      k :| t -> case k a of
--        Val y -> qApp t y
--        E u g -> E u (g >< t)

{-# INLINE [2] send #-}
-- send :: forall t r a. Member t r => t a -> Eff r a
send t = E t (tsingleton Val)
{-# RULES
"send/bind" [~3] forall t k. send t >>= k = E t (tsingleton k)
#-}

-- ██████  ███████  █████  ██████  ███████ ██████
-- ██   ██ ██      ██   ██ ██   ██ ██      ██   ██
-- ██████  █████   ███████ ██   ██ █████   ██████
-- ██   ██ ██      ██   ██ ██   ██ ██      ██   ██
-- ██   ██ ███████ ██   ██ ██████  ███████ ██   ██

type UMember t r h = (KnownNat (Length r), KnownNat (Length h), KnownNat (FindElem t (r :++ '[t] :++ h)))

-- {-# INLINE handleRelay #-}
-- handleRelay :: forall t r h w a. UMember t r h
--             => (a -> Eff r (t ': h) w)
--             -> (forall v. t v -> Arr r (t ': h) v w -> Eff r (t ': h) w)
--             -> Eff (t ': r) h a -> Eff r (t ': h) w
-- handleRelay ret handler m = loop m
--  where
--   loop (Val x) = ret x
--   loop e = loopE (natVal $ SNat @(Length r)) (natVal $ SNat @(Length h)) e
--   -- -- loopE _ _ (Val x) =
--   -- --      Debug.trace ("@(Length r) = " ++ show (natVal (Proxy @(Length r)))
--   -- --              ++ "\n@(Length h) = " ++ show (natVal (Proxy @(Length h)))
--   -- --              ++ "\n returning Val x"
--   -- --                  ) ret x
--   loopE _ _ (Val x) = ret x
--   loopE r 0 (E u q) =
--     let k = qComp q loop
--      in Debug.trace ("float @(Length r) = " ++ show (natVal (Proxy @(Length r)))
--                             ++ "\t@(Length h) = " ++ show (natVal (Proxy @(Length h)))
--                             ++ "\t@(Length h) = " ++ show (natVal (Proxy @(Length h)))
--                             ++ "\t returning singleton x"
--                             ) $ E u (tsingleton (qComp q (loopE (r-1) 0)))
--   loopE r h (E u q) =
--     let k = qComp q loop
--      in Debug.trace ("float @(Length r) = " ++ show (natVal (Proxy @(Length r)))
--                             ++ "\t@(Length h) = " ++ show (natVal (Proxy @(Length h)))
--                             ++ "\t returning coersion x"
--               ) $ handler (unsafeCoerce u) (qComp q (loopE (r-1) h))

{-# INLINE handleRelay' #-}
handleRelay' :: forall t r h w a. UMember t r h
            => String -> (a -> Eff r (t ': h) w)
            -> (forall v. t v -> Arr r (t ': h) v w -> Eff r (t ': h) w)
            -> Eff (t ': r) h a -> Eff r (t ': h) w
handleRelay' str ret handler m = loop m
 where
  loop (Val x) = ret x
  loop e@(E (u :: t1 v) q) = loopE (natVal' @(FindElem t1 (t ': r)) proxy#) e
    where loopE _ (Val x) = ret x
          loopE 0 e = handler (unsafeCoerce u) (qComp q (loopE 0))
          loopE n e = undefined -- unsafeCoerce $ E u (tsingleton (qComp q (loopE (n-1))))

-- handleRelay str ret handler n u q = loop n
--   where loop 0 = handler (unsafeCoerce u) (qComp q (loopE 0))
--         loop n = E u (tsingleton (qComp q (loopE (n-1))))
    -- let k = qComp q loop
    --  in case u of
          -- (v :: t1 v) -> loopE n (E u q)
          --   case SNat @(FindElem t1 (t ': r)) %~ SNat @0 of
          --     Proved _ ->  Debug.trace (str ++ " @(Length r) = " ++ show (natVal (Proxy @(Length r)))
          --                          ++ "\tFindElem = " ++ show (natVal (Proxy @(FindElem t1 (t ': r))))
          --                          ++ "\treturning coersion x"
          --              ) $ handler (unsafeCoerce v) k
          --     _        -> Debug.trace (str ++ " @(Length r) = " ++ show (natVal (Proxy @(Length r)))
          --                          ++ "\tFindElem = " ++ show (natVal (Proxy @(FindElem t1 (t ': r))))
          --                          ++ "\t returning singleton x"
          --              ) $ undefined -- $ E v (tsingleton k)



    -- TOne k -> handler (unsafeCoerce u) (qComp q loop)
    -- k :| t -> E u (_ k t)
  -- loop e = loopE (natVal $ SNat @(Length r)) (natVal $ SNat @(Length h)) e
  -- -- -- loopE _ _ (Val x) =
  -- -- --      Debug.trace ("@(Length r) = " ++ show (natVal (Proxy @(Length r)))
  -- -- --              ++ "\n@(Length h) = " ++ show (natVal (Proxy @(Length h)))
  -- -- --              ++ "\n returning Val x"
  -- -- --                  ) ret x
  -- loopE _ _ (Val x) = ret x
  -- loopE r 0 (E u q) =
    -- let k = qComp q loop
    --  in Debug.trace (str ++ " @(Length r) = " ++ show (natVal (Proxy @(Length r)))
    --                         ++ "\t@(Length h) = " ++ show (natVal (Proxy @(Length h)))
    --                         ++ "\t@(FindElem t (r :++ '[t] :++ h)) = " ++ show (natVal (Proxy @(FindElem t (r :++ '[t] :++ h))))
    --                         ++ "\t returning singleton x"
    --                         ) $ E u (tsingleton (qComp q (loopE r 0)))
  -- loopE r h (E u q) =
  --   let k = qComp q loop
  --    in Debug.trace (str ++ " @(Length r) = " ++ show (natVal (Proxy @(Length r)))
  --                           ++ "\t@(Length h) = " ++ show (natVal (Proxy @(Length h)))
  --                           ++ "\t@(FindElem t (r :++ '[t] :++ h)) = " ++ show (natVal (Proxy @(FindElem t (r :++ '[t] :++ h))))
  --                           ++ "\t returning coersion x"
  --             ) $ handler (unsafeCoerce u) (qComp q (loopE r h))

  -- -- loopE r 0 (E u q) = Debug.trace ("@(Length r) = " ++ show (natVal (Proxy @(Length r)))
  -- --                      ++ "\n@(Length h) = " ++ show (natVal (Proxy @(Length h)))
  -- --                      ++ "\n returning E u loop x"
  -- --        ) $ E u (tsingleton (qComp q (loopE (r - 1) h)))

  -- -- GOOD:
  -- loop (E u q) =
  --   let k = qComp q loop
  --    in case
  --         Debug.trace ("@(Length r) = " ++ show (natVal (Proxy @(Length r)))
  --                 ++ "\n@(Length h) = " ++ show (natVal (Proxy @(Length h)))
  --                     )
  --         $ SNat @(FindElem t (t ': r)) %~ SNat @(Length r) of
  --             Proved _ -> Debug.trace "Coercing" $ h (unsafeCoerce u) k
  --             _        -> Debug.trace "Returning E" $ E u (tsingleton k)

data Reader e v where
  Reader :: Reader e e

{-# INLINE [2] ask #-}
ask :: forall e r h. (KnownNat (FindElem (Reader e) r)) => Eff r h e
ask = send (Reader :: Reader e e) -- E (Reader :: Reader e e) (tsingleton Val)
-- {-# RULES
-- "get/bind" forall k. ask >>= k = send Reader >>= k
-- #-}

capEff :: Eff r '[] ()
capEff = Val ()

initEff = (capEff >>)

-- runReader :: UMember (Reader e) r h => Eff (Reader e ': r) h w -> e -> Eff r (Reader e ': h) w
-- runReader m e = handleRelay return (\Reader k -> k e) m

runReader' :: UMember (Reader e) r h => String -> Eff (Reader e ': r) h w -> e -> Eff r (Reader e ': h) w
runReader' str m e = Debug.trace ("runReader " ++ str) $ handleRelay' str return (\Reader k -> Debug.trace ("handle " ++ str) $ k e) m

add :: Monad m => m Int -> m Int -> m Int
add = liftM2 (+)

t1 :: KnownNat (FindElem (Reader Int) r) => Eff r h Int
-- t1 :: UMember (Reader Int) r '[] => Eff r '[] Int
t1 = ask `add` return (1::Int)

-- t1r = run $ runReader (initEff t1) (10::Int)

t2 :: (KnownNat (FindElem (Reader Float) r), KnownNat (FindElem (Reader Int) r), KnownNat (FindElem (Reader Integer) r), UMember (Reader Int) r h, UMember (Reader Float) r h, UMember (Reader Integer) r h) => Eff r h Float
t2 = do
  v2 <- Debug.trace "ask Float" $ ask -- Union 0 (Reader Int), r = 1, h 0
  v1 <- Debug.trace "ask Int"   $ ask --E Reader (tsingleton Val >< tsingleton (E Reader)) -- Union 1 (Reader Int), r = 0, h = 1
  v3 <- Debug.trace "ask Integer"   $ ask --E Reader (tsingleton Val >< tsingleton Val >< tsingleton (E Reader)) -- Union 1 (Reader Int), r = 0, h = 1
  v4 <- Debug.trace "ask Float" $ ask --E Reader (tsingleton Val) -- Union 0 (Reader Int), r = 1, h = 0
  return $ fromIntegral (Debug.trace ("v1: " ++ show v1) $ v1 + (1::Int))
                      + (Debug.trace ("v2: " ++ show v2) $ v2 + (2::Float))
                      + (Debug.trace ("v4: " ++ show v4) $ v4 + (2::Float))
                      + fromIntegral (Debug.trace ("v3: " ++ show v3) $ v3 + (1::Integer))
  -- return $ (Debug.trace ("v2: " ++ show v2) $ v2 + (2::Float))
--
-- -- t2r :: Member (Reader Float) r => Eff r Float
-- -- t2r = runReader t2 (10::Int)
--
-- -- t2rr :: Eff r Float
t2rr = run $ flip (runReader' "Float") (20::Float) . flip (runReader' "Int") (10::Int) . flip (runReader' "Integer") (10::Integer) $ initEff t2

t2rr' = run $ runReader' "Integer" (runReader' "Int" (runReader' "Float" (initEff t2) (20::Float)) (10::Int)) (10::Integer)


--
-- t2rr' = flip runReader (1e15::Float) . flip runReader (1000::Int) $ t2
---
-- t2rrr = 33.0 == run t2rr

-- -- local :: forall e a r. Member (Reader e) r =>
-- --          (e -> e) -> Eff r a -> Eff r a
-- local f m = do
--   e0 <- ask
--   let e = f e0
--   -- Local signature is needed, as always with GADTs
--   let h :: Reader e v -> Arr r v a -> Eff r a
--       h Reader g = g e
--   interpose return h m

-- {-# INLINE [2] runReader' #-}
-- runReader' :: forall r v e. KnownNat (Length r) => Eff (Reader e ': r) v -> e -> Eff r v
-- runReader' m e = loop m where
--  {-# INLINE loop #-}
--  loop (Val x) = return x
--  loop (E u q) =
--    case SNat @(Length r) %~ SNat @0 of
--      Proved _ -> loop $ qApp q e
--     --   case (unsafeCoerce u) of
--     --     Reader -> loop $ qApp q e
--      _ -> undefined -- E u (tsingleton (qComp q loop))
