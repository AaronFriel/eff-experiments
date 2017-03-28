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

{-# OPTIONS_GHC -Wno-unticked-promoted-constructors -Wno-missing-signatures -Wno-redundant-constraints #-}

module Data.Iota.Unified.Indexed5
 -- ( Eff )
 where



-- import Data.Promotion.Prelude
-- import Data.Promotion.TH

import Data.Singletons
import Data.Singletons.Decide
import Data.Singletons.Prelude
import Data.Singletons.TH
-- import Data.Singletons.TypeLits
import Data.Type.Equality

import Data.Kind (type (*))
import Data.Proxy (Proxy)
import GHC.Prim (Proxy#, proxy#)

import Data.Type.Set

import qualified Debug.Trace as Debug

import qualified GHC.Exts as E
import qualified Foreign as F

unsafeSizeof :: a -> Int
unsafeSizeof a =
  case E.unpackClosure# a of
    (# x, ptrs, nptrs #) ->
      F.sizeOf (undefined::Int) + -- one word for the header
        E.I# (E.sizeofByteArray# (E.unsafeCoerce# ptrs)
             E.+# E.sizeofByteArray# nptrs)

intX :: Int
intX = 5

foobar :: String
foobar = "foobar"

data Tree a = ApNode (Tree a) (Tree a) | BindNode (Tree a) (Tree a) | Ctor a (Tree a) | Pure

$(singletons [d|
  |])

data Reader (e :: *) (v :: *) where
  Reader :: Reader e e

data Writer (e :: *) (v :: *) where
  Writer :: o -> Writer o ()

newtype Exc (e :: *) (v :: *) = Exc e

data Halt = Halt

seal :: MonadEff '[] 'Pure a -> MonadEff '[] 'Pure a
seal = id

run :: MonadEff '[] 'Pure a -> a
run (Val x) = x

send :: forall v ctor. ctor v -> MonadEff '[ctor] ('Ctor ctor 'Pure) v
send t = Eff t Val

ask :: forall r. MonadEff '[Reader r] ('Ctor (Reader r) 'Pure) r
ask = send Reader

-- tell :: forall o. MonadEff ('Ctor (Writer o) 'Pure) o
tell = send . Writer

-- test :: MonadEff ('Ctor (Reader String) 'Pure) String
test = ask @Int

-- test2 :: MonadEff ('Ctor (Reader String) ('Ctor (Writer String) 'Pure)) ()
test2 = Eff (Reader) (\a -> Eff (Writer a) Val)

type family RunSimple x ctor where
  RunSimple ('Pure)           _ = 'Pure
  RunSimple ('Ctor ctor k) ctor = k

class RunReader j e where
  runReader :: MonadEff (Reader e ': r) j w -> e -> MonadEff r (RunSimple j (Reader e)) w

instance RunReader ('Ctor (Reader e) k) e where
  runReader (Eff u q) e = case u of
    Reader -> (q e)

class RunWriter j o where
  runWriter :: MonadEff (Writer o ': r) j w -> MonadEff r (RunSimple j (Writer o)) (w, [o])

instance RunWriter ('Ctor (Writer String) k) o where
  runWriter (Eff u q) = case u of
    Writer o -> Debug.trace ("Found o: " ++ o) $ case q () of
      Val a -> Val (a, [o])

data MonadEff r j (a :: *)
  where
    Val     :: {-# UNPACK #-} !a -> MonadEff '[] 'Pure a
    Eff     :: {-# UNPACK #-} !(ctor a) -> {-# UNPACK #-} !(a -> MonadEff r k b) -> MonadEff (ctor ': r) (Ctor ctor k) b
    -- (:<*>)  :: MonadEff j (a -> b) -> MonadEff k a -> MonadEff ('ApNode j k) b
    -- (:>>=)  :: MonadEff j a -> (a -> MonadEff k b) -> MonadEff ('BindNode j k) b

-- data WrappedMonadEff w = forall j. SingI j => WrappedMonadEff (MonadEff j w)

-- class TreeView j eff where
--   focus :: MonadEff j w -> MonadEff 

-- runReader :: forall j w e. (SingI (Reader e e)) => MonadEff j w -> e -> WrappedMonadEff w
-- runReader (Val x) e = WrappedMonadEff (Val x)
-- runReader m@(Eff u q) e = case m of
--   (Eff u q :: SingI (ctor a) => MonadEff (Ctor (ctor a)) w) -> case toSing (sing :: Sing (ctor a)) of
--     _ -> undefined
-- runReader m@(Eff u q) e = case m of
--   (Eff u q :: MonadEff (Ctor (ctor a)) w) -> case (sing :: Sing j) %~ (SCtor (fromSing (SReader @e))) of
--     _ -> undefined
  
  
  -- %~ (sing :: Sing (Ctor (Reader e e))) of
  --   Proved _ -> WrappedMonadEff (Eff u q)
-- 
-- $(promote [d|
--   -- data Reader (e :: *) (v :: *) where
--   --     R :: (e ~ v) => Reader e v

--   |])  


-- $(singletons [d|

--   -- data Reader (e :: *) (v :: *) where

--   |])

-- -- type STree (x :: (Tree *)) = Sing x


-- -- type SomeMonadEff w = forall j. SomeSing (MonadEff j w)

-- type EffTree = Tree (* -> *)

  

-- -- runReader m@(Eff u q) e = case WrappedMonadEff (Eff u q)

-- -- getTree :: SingI j => MonadEff j w -> STree j
-- -- getTree m = sing

-- -- runReader :: e -> MonadEff j w -> MonadEff 

-- $(promote [d|

--   -- reader'Opaque e = id
--   -- reader'Pure e = id
--   -- reader'Ctor :: e -> Reader e v -> v 
--   -- reader'Ctor e ctor = case ctor of
--   --   R -> e
  
--   -- runReader e m = case (getTree m, m) of
--   --   (sing, Val x) -> reader'Pure e
--   |])

-- -- runReader :: e -> MonadEff j w -> 
-- -- runReader e m = case (getTree m, m) of
-- --   (s, Val a) -> Val


-- -- test :: MonadEff 'Pure w -> (k :: RunSimpleSym5 Int Int Int Int 'Pure (Reader Int))
-- -- test (Val x) = Pu 5

-- $(promote [d|

--   toTree _ Pure m = P m
--   -- toTree e (Ctor (t, v)) 
--   -- toTree e (Ctor t) a = (Pure, a)

--   -- -- runError :: ETree (Exc Halt -> a) b ->
--   -- runError Opaque = Opaque
--   -- runError (Pu a) = Pu (Right a)
--   -- runError (Ct _) = Pu (Left Halt)
--   -- runError (Ap (Ct _)      r) = Pu (Left Halt) 
--   -- runError (Ap      l (Ct _)) = Pu (Left Halt)
--   -- runError (Ap      l      r) = Ap (runError l) (runError r)
--   -- runError (Bi (Ct _)      r) = Pu (Left Halt) 
--   -- runError (Bi      l (Ct _)) = Pu (Left Halt)
--   -- runError (Bi      l      r) = Ap (runError l) (runError r)

--   -- runReader' :: t -> ETree (t -> b) b -> ETree a b
--   -- runReader' e (Opaque t) = t id
--   -- runReader' e (Pu a)     = a id
--   -- runReader' e (Ct f)     = Pu (f e)
--   -- runReader' e (Ap l r) = Ap (runReader' e l) (runReader' e r)
--   -- runReader' e (Bi l f) = Bi (runReader' e l) (f e)

--   -- addWrite o a = (a, [o])
--   -- mergeWrite (a, [o]) (a', [o']) = mergeWrite 

--   -- runWriter' :: ETree k a -> ETree a (a, [t])
--   -- runWriter' o (Opaque t) = t (addWrite o)
--   -- runWriter' o (Pu a) = a (addWrite o)
--   -- runWriter' o (Ct (k, f)) = Pu (f (), k:o)
--   -- runWriter' o (Ap l r) = l
--   -- runWriter' o (Bi l f) = f (runWriter' o l)

--   -- runWriter' o (Ap l r) = Ap (runWriter' o l) (runWriter' o r)
--   -- runWriter' o (Bi l r) = Ap (runWriter' e l) (runWriter' e r)

--   |])