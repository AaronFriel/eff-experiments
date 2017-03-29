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

{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE Strict #-}

{-# OPTIONS_GHC -funbox-strict-fields #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors -Wno-missing-signatures -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Ddump-splices #-}


module Data.Iota.Unified.Indexed5
 -- ( Eff )
 where



import Data.Promotion.Prelude
-- import Data.Promotion.TH

import Data.Singletons
import Data.Singletons.Decide
import Data.Singletons.Prelude
import Data.Singletons.TH
import Data.Singletons.TypeLits
import Data.Type.Equality

import Data.Kind (Constraint, type (*))
import Data.Proxy (Proxy)
import GHC.TypeLits hiding (type (*))
import GHC.Prim (Proxy#, proxy#)
import           Unsafe.Coerce               (unsafeCoerce)

import Control.Monad.Fix (fix)
-- import Data.Type.Set (Set (..), Union)
-- import Data.Type.BiMap (BiMapping (..), BiMap (..))
-- import qualified Data.Type.BiMap as BiMap

import Data.Typeable

import qualified Debug.Trace as Debug

-- import qualified GHC.Exts as E
-- import qualified Foreign as F

-- unsafeSizeof :: a -> Int
-- unsafeSizeof a =
--   case E.unpackClosure# a of
--     (# x, ptrs, nptrs #) ->
--       F.sizeOf (undefined::Int) + -- one word for the header
--         E.I# (E.sizeofByteArray# (E.unsafeCoerce# ptrs)
--              E.+# E.sizeofByteArray# nptrs)

intX :: Int
intX = 5

foobar :: String
foobar = "foobar"

data Reader (e :: *) (v :: *) where
  Reader :: Reader e e
  deriving (Typeable)

data Writer (e :: *) (v :: *) where
  Writer :: o -> Writer o ()

newtype Exc (e :: *) (v :: *) = Exc e

data Trace v where
  Trace :: String -> Trace ()

data Halt = Halt

-- seal :: MonadEff '[] 'Pure a -> MonadEff '[] 'Pure a
-- seal = id

-- instance Member t (t ': r) 
-- instance (Member t r) => Member t (u ': r)

-- type family Member' t r :: Constraint where
--   Member' x (x ': r) = ()
--   Member' x (y ': r) = Member' x r

-- type family AllMemberOf ts r :: Constraint where
--   AllMemberOf       '[] _ = ()
--   AllMemberOf (x ': ts) r = (Member' x r, AllMemberOf ts r)



type Effect = (* -> *)

$(promote [d|
  data Tree a = Pure | Ctor a | Tree a :>>= Nat
    deriving (Eq)
  data Universe v = Universe {
      treeMap :: [(Nat, Tree v)],
      effects :: [v]
    }
  
  emptyU = Universe [] []
  |])

$(promoteOnly [d|

  lookupIndex :: Nat -> Universe v -> Tree v  
  lookupIndex k u = lookupIndex' k (treeMap u)

  lookupIndex'                    :: (Eq a) => a -> [(a, b)] -> b
  lookupIndex'    key ((x,y):xys) = if key == x then y else lookupIndex' key xys

  lookupValue :: Eq v => Tree v -> Universe v -> Nat  
  lookupValue k u = lookupValue' k (treeMap u)

  lookupValue'                    :: (Eq b) => b -> [(a,b)] -> a
  lookupValue'  value ((x,y):xys) = if value == y then x else lookupValue' value xys

  removeEffect :: (* -> *) -> Universe (* -> *) -> Universe (* -> *)
  removeEffect e (Universe a efxs) = Universe a (removeEffect' e efxs)

  removeEffect' e (eft':efxs)      = case e == eft' of True -> efxs 

  |])

data MonadEff (u :: Universe Effect) j (a :: *)
  where
    Val     :: a -> MonadEff u 'Pure a

    Eff     :: (ctor a)
            -> (a -> b)
            -> MonadEff u (Ctor ctor) b

    Bind    :: MonadEff u j a
            -> (a -> MonadEff u k b)
            -> MonadEff u (j :>>= n) b
            
class Run u j where 
  run :: MonadEff u j a -> a

instance Run u 'Pure where
  run (Val x) = x

instance (Run u (LookupIndex k u)) => Run u ('Pure ':>>= k) where
  run :: MonadEff u j a -> a
  run (Val x `Bind` k) = case x of
    (x :: a') -> run $ (unsafeCoerce k :: a' -> MonadEff u (LookupIndex k u) a) x

runTrace :: MonadEff ('Universe m r) (Ctor Trace) a -> a
runTrace (Eff u q) = case u of
  Trace t -> Debug.trace t $ q ()

type TestMap = '[ '(1, Ctor Trace :>>= 1), '(2, Pure :>>= 1) ]

{-# INLINE stepTrace #-}
stepTrace :: MonadEff ('Universe TestMap r)
                      (Ctor Trace :>>= 1)
                      a 
          -> MonadEff ('Universe TestMap r) 
                      (LookupIndex' 2 TestMap)
                      a
stepTrace ((Eff u q) `Bind` k) = case u of
  Trace t -> Debug.trace t $ unsafeCoerce $ Val (q ()) `Bind` k

{-# INLINE runTest' #-}
runTest' :: MonadEff ('Universe TestMap r) (Pure :>>= k) a -> MonadEff ('Universe TestMap r) (LookupIndex' k TestMap) a
runTest' m = case m of
  (Val x `Bind` k) -> unsafeCoerce $ k x

infiniteTraceTest :: MonadEff ('Universe TestMap r) (LookupIndex' 1 TestMap) Int
infiniteTraceTest = 
  let t (n :: Int) = Eff (Trace $ show n) (const $ n + 1) `Bind` t in t 0

loop :: MonadEff ('Universe TestMap r) ('Ctor Trace ':>>= 1) a -> IO Void
loop m = do
  case stepTrace m of
    m'@(Val x' `Bind` _) -> do
      loop (runTest' m')

testLoop = loop infiniteTraceTest

-- finiteTest = do
--   let stepOnce m = do
--         case stepTrace m of
--           (Val x `Bind` k) -> do
--             print $ (unsafeCoerce x' :: Int)
--             return $ runTest' (k x)
--   return foobar
-- runTest'' = let x = runTrace' . runTest' . x in x infiniteTraceTest

-- send :: Member ctor r => ctor v -> MonadEff r ('Ctor ctor 'Pure) v
-- send t = Eff t Val

-- ask :: forall e r. Member (Reader e) r => MonadEff r ('Ctor (Reader e) 'Pure) e
-- ask = send (Reader)

-- tell :: forall o r. Member (Writer o) r => o -> MonadEff r ('Ctor (Writer o) 'Pure) ()
-- tell o = send (Writer o)

-- trace = send . Trace

-- test :: MonadEff ('Ctor (Reader String) 'Pure) String
-- test = ask @Int

-- test2 :: MonadEff ('Ctor (Reader String) ('Ctor (Writer String) 'Pure)) ()
-- test2 = ask @String `Bind` tell

-- t2rr = (((), [foobar]) ==) $ run $ runWriter (runReader test2 foobar)

-- class RunReader (j :: Tree (* -> *)) e where
--   runReader :: MonadEff (Reader e ': r) j w -> e -> MonadEff r (RunSimple j (Reader e)) w

-- instance RunReader ('Ctor (Reader e) k) e where
--   runReader (Eff u q) e = case u of
--     Reader -> (q e)

-- class RunWriter j o where
--   runWriter :: MonadEff (Writer o ': r) j w -> MonadEff r (RunSimple j (Writer o)) (w, [o])

-- instance RunWriter ('Ctor (Writer String) k) o where
--   runWriter (Eff u q) = case u of
--     Writer o -> case q () of
--       Val a -> Val (a, [o])

    -- (:<*>)  :: MonadEff j (a -> b) -> MonadEff k a -> MonadEff ('ApNode j k) b
    -- Bind :: {-# UNPACK #-} !(MonadEff r j a)
    --      -> {-# UNPACK #-} !(a -> MonadEff r k b)
    --      -> MonadEff r (j :>>= k) b

-- imap :: (a -> b) -> MonadEff r j a -> MonadEff r j b
-- imap f (Val a) = Val (f a)
-- imap f (Eff u q) = Eff u (imap f . q)
-- imap f (m `Bind` k) = m `Bind` (imap f . k)

-- data WrappedMonadEff w = forall j. SingI j => WrappedMonadEff (MonadEff j w)
