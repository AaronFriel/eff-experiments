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
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}  

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


intX :: Int
intX = 5

foobar :: String
foobar = "foobar"

data Reader (e :: *) (v :: *) where
  Reader :: Reader e e
  deriving (Typeable)

data Writer (e :: *) (v :: *) where
  Writer :: o -> Writer o ()

data State (s :: *) (v :: *) where
  Get :: State s s
  Put :: s -> State s ()

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



type Effect  = (* -> *)

$(promote [d|
  data Tree a = Pure | Ctor a | Tree a :>>= Nat | Focused (Tree a) | Unfocused (Tree a)
    deriving (Eq)

  data Universe v = Universe {
      treeMap      :: [(Nat, Tree v)],
      effects      :: [v],
      currentFocus :: Maybe v
    }
  
  emptyU = Universe [] []

  class Treelike a where
    makeCtor :: a -> Tree a
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

  |])


data MonadEff (u :: Universe Effect) j (a :: *)
  where
    Val     :: a -> MonadEff u 'Pure a

    Eff     :: (ctor a)
            -> (a -> b)
            -> MonadEff u (Ctor ctor) b

    Unf     :: (ctor a)
            -> (a -> b)
            -> MonadEff u (Unfocused (Ctor ctor)) b

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

-- This is the control flow graph, with nodes indexed by type-level natural numbers.
-- This graph forms a cycle with one node.
type TraceMap = '[ '(1, Ctor Trace :>>= 1) ]
type TraceUniverse r = 'Universe TraceMap r Nothing 
-- TraceMap is a type of kind [(GHC.Types.Nat, Tree (* -> *))]

-- Increment over a "Trace" effect, emitting it, and iterating.
{-# INLINE stepTrace #-}
stepTrace :: MonadEff (TraceUniverse r) (Ctor Trace :>>= 1)      a 
          -> MonadEff (TraceUniverse r) (LookupIndex' 1 TraceMap) a
stepTrace ((Eff u q) `Bind` k) = case u of
  Trace t -> Debug.trace t $ unsafeCoerce $ k (q ())

-- Uses a Trace effect and a recursive let binding for an infinite loop.
infiniteTraceLoop :: MonadEff (TraceUniverse r) (LookupIndex' 1 TraceMap) Int
infiniteTraceLoop = 
  let t (n :: Int) = Eff (Trace $ show n) (const $ n + 1) `Bind` t in t 0

{-# INLINE loopTrace #-}
loopTrace :: MonadEff (TraceUniverse r) ('Ctor Trace ':>>= 1) a -> IO Void
loopTrace m = do
  case stepTrace m of
    m' -> loopTrace (stepTrace m')

type StateUniverse r = 'Universe StateMap r Nothing 
type StateMap = '[ '(1, Ctor (State Int) :>>= 2), '(2, Ctor (State Int) :>>= 1) ]

-- Uses a Trace effect and a recursive let binding for an infinite loop.
infiniteStateLoop :: MonadEff (StateUniverse r) (LookupIndex' 1 StateMap) a
infiniteStateLoop = 
  let t () = (Debug.trace "Get" (Eff Get id)
           `Bind` (\s ->  (Eff (Put $ s + 1) id)
             `Bind` t)) in t ()


$(promote [d|
  mapOverEffect f (n, e)         = (n, f e)
  mapOverGraph  f (Universe g r c) = Universe (map f g) r c
  applyEffect f u = mapOverGraph (mapOverEffect f) u

  -- simpleEffect' e Pure       = Pure
  -- simpleEffect' e (Ctor e')  = if e == e' then Pure else Ctor e' 
  -- simpleEffect' e (m :>>= n) = simpleEffect' e m :>>= n

  -- simpleEffect e = simpleEffect' e

  -- decomp' e (Ctor e')    = if e == e' then Ctor e else Ctor e'
  -- decomp' e j            = j
  |])



type family SimpleResult u j e where
  --Not correct, but works for infiniteStateLoop
  SimpleResult u (Ctor e :>>= n) e = LookupIndex n u
  SimpleResult u (Ctor e)        e = Pure
  SimpleResult u       j         _ = j

type family FocusT (n :: Tree (* -> *)) (e :: * -> *) = r | r -> n where
  -- FocusT (Pure    ) e = Focused (Pure)
  FocusT (Ctor e  ) e = Ctor e
  -- FocusT (Ctor e' ) e = Unfocused (Ctor e')
  -- FocusT (m :>>= n) e = FocusT m e :>>= n

type family FocusG (g :: [(Nat, Tree (* -> *))]) (e :: * -> *) = r | r -> g e where
  FocusG ( '(n, tree) ': r) e = '(n, FocusT tree e) ': FocusG r e

type family FocusU u e = r | r -> u e where
  FocusU ('Universe g r Nothing) e = 'Universe (FocusG g e) r (Just e)

type family Focus m e = r | r -> m e where
  Focus (MonadEff u j w) e = MonadEff (FocusU u e) (FocusT j e) w

focus :: forall e u j w. 
         MonadEff u j w
      -> (Focus (MonadEff u j w) e, Focus (MonadEff u j w) e -> MonadEff u j w)
focus m = (unsafeCoerce m, unsafeCoerce)

class Decomp (e :: * -> *) u j j' w | j' -> j where
  decomp :: MonadEff u j w -> Either (MonadEff u j w) (MonadEff u j' w)

instance {-# INCOHERENT #-} (Focus (MonadEff u (Ctor e) w) e ~ t) => Decomp e u (Ctor e) (Ctor e) w where
  decomp = Right . unsafeCoerce

instance Decomp e u j j' w where
  decomp = Left


-- decomp :: forall e u j w. MonadEff u j w -> Either (MonadEff u j w) (MonadEff u (Ctor e) w)
-- decomp m = case focus @e m of
--     (m', _) -> case m' of
--       (Eff u q) -> Right (unsafeCoerce $ m)
--       (_)       -> Left m

testDecomp :: MonadEff u j w -> IO String
testDecomp m = do
  return $ 
    case decomp @(Writer [Char]) m of
      Left (Val _)   -> "Left Pure"
      Left (Eff u q)  -> "Left Eff"
      Left (Bind _ _) -> "Left Bind"
      Left (Unf _ _)  -> "Left Unf"
      Left (_)        -> "Left Other"
      -- Right (Val x)    -> "Right Pure"
      Right (Eff u q)  -> "Right Eff"
      -- Right (Bind _ _) -> "Right Bind"
      -- Right (Unf _ _)  -> "Right Unf"
      Right (_)        -> "Right Other"
      -- (Val _ )   -> Right (Val x)
-- decomp :: (Focusable e (MonadEff u j w)) 
--        => MonadEff u j w
--        -> Either (MonadEff u j w) (MonadEff u (Ctor e) w)
-- decomp m = case focus 

-- class Decomp e u j w where
--   decomp :: m -> Either (MonadEff u j w) (MonadEff u (Ctor e) w)


class Decomp' u j j' (e :: * -> *) where
  decomp1 :: MonadEff u j a -> Either (MonadEff u j a) (MonadEff u j' a)
  decompProofLeft  :: Decision (SimpleResult u j e :~: j)
  decompProofLeft = Disproved undefined
  decompProofRight :: Decision (SimpleResult u j e :~: Pure)
  decompProofRight = Disproved undefined
-- unfocus :: forall e u j w. MonadEff u j w
--         -> Focus (MonadEff u j w) e
-- unfocus = unsafeCoerce

--   Focus (MonadEff u (Ctor e) w) e = MonadEff u (Focused e) w
--   Focus (MonadEff u j w) e        = MonadEff u j w

instance Decomp' u j j' e where
  decomp1 = Debug.trace "Decomp Left" . Left
  decompProofLeft = Proved (unsafeCoerce Refl)

instance Decomp' u (Ctor e) (Ctor e') e where
  decomp1 = Debug.trace "Decomp Right" . Right . unsafeCoerce
  decompProofRight = Proved (unsafeCoerce Refl)

-- appBind :: MonadEff u (Ctor t :>>= n) w 
--         -> v
--         -> (v -> MonadEff u k w)
--         -> MonadEff u (LookupIndex n u) w
-- appBind (Eff u q `Bind` _) extract = unsafeCoerce $ k (q (extract u))

appBind' :: (forall a1. (a1 -> MonadEff u k a, ctor1 a3, a3 -> a1))
         -> MonadEff u (LookupIndex n u) w
appBind' (k, u, q) = undefined

-- instance {-# OVERLAPPABLE #-} Decomp e j k where
--   decomp = Left

-- instance {-# OVERLAPS #-} (Decomp' e j ~ True) => Decomp e j True where
--   decomp m = unsafeCoerce (Right m)

-- instance {-# OVERLAPPABLE #-} (Decomp' e j ~ True) => Decomp e j where
--   decomp m = unsafeCoerce $ Right m

-- applyBind :: MonadEff u (Ctor (State Int) :>>= n) w
--           -> (forall a. State Int a -> a)
--           -> forall v. (v, v -> MonadEff u (LookupIndex n u) w)
-- applyBind (Eff u q `Bind` k) extract = (_ q (extract u), undefined)

-- applyBind :: MonadEff u ('Ctor (State Int) ':>>= n) a
--           -> (forall v1. State Int v1 -> v1)
--           -> MonadEff u (LookupIndex n u) a
-- applyBind (Eff u q `Bind` k) extract = unsafeCoerce $ k (q (extract u))

tr n = Debug.trace (show n)

runState :: forall u j a i r. (u ~ (StateUniverse r))
         => MonadEff u j a
         -> Int
         -> MonadEff u (SimpleResult u j (State Int)) (a, Int)
runState m s = tr 0 $ case decomp1 @u @j @(Ctor (State Int)) @(State Int) m of
  Right m   -> tr 1 $ case decompProofRight @u @j @(Ctor (State Int)) @(State Int) of
    Proved Refl -> tr 2 $ case m of
      (Eff  Get     q) -> tr 3 $ Val (q  s, s )
      (Eff (Put s') q) -> tr 4 $ Val (q (), s')
  Left (Val a)      -> tr 5 $ Val (a, s)
  Left (Eff u q)    -> tr 6 $ case decompProofLeft @u @j @(Ctor (State Int)) @(State Int) of
    Proved Refl -> tr 7 $ Eff u (undefined q)
  Left m@(e@(Eff u q :: MonadEff u j' _) `Bind` k) -> tr 8 $ 
    case decomp1 @u @j' @(Ctor (State Int)) @(State Int) e of
      Left  _   -> tr 12 $ undefined
      Right e   -> tr 9 $ case decompProofRight @u @j' @(Ctor (State Int)) @(State Int) of
        Proved Refl -> tr 10 $ case e of
          (Eff Get q) -> tr 11 $ undefined -- $ unsafeCoerce k (q s) :: MonadEff u (LookupIndex n u) a
    -- case decompProofLeft @u @(Ctor t :>>= n) @(Ctor (State Int)) @(State Int) of
    --   Proved Refl -> case decomp1 @u @j' @(Ctor (State Int)) @(State Int) m' of
    --     Right (Eff Get q) -> case decompProofRight @u @j' @(Ctor (State Int)) @(State Int) of
          -- Proved Refl -> undefined $ appBind m extract
  where
    extract :: State Int v -> v
    extract Get    = s
    extract (Put _)= ()
  -- Left (Eff u q)    -> case proofDecomp @j @(Ctor (State Int)) @(State Int) of
  --   Proved refl -> Eff _ _
--   Left (m `Bind` k) -> case decomp @(State Int) m of
--     _ -> undefined
  -- Right m@(Eff u q) -> case m of 
  --   (Eff Get q :: MonadEff u (Ctor (State Int)) a) -> Val (q s, s)
  -- Right m@(Eff u q) -> undefined
-- runState m@(Val a) s            = Val (a, s)
-- runState m@(Eff u _ `Bind` k) s =
--   case u of
--     Get    -> runState (applyBind m extract) s
--     Put _  -> undefined
--     -- Put s' -> runState (applyBind m extract) s'
--     (Get, (q, k) -> runState (unsafeCoerce $ k $ q s) s
--     -- (Put s', q, k) -> runState (unsafeCoerce $ k $ q ()) s'

--   loop m@(Eff u q `Bind` k) s = qApp m 
-- case u of
--   Get    -> Debug.trace showGet $ unsafeCoerce $ stepState (qApp )
--     where showGet = "Get " ++ show s 
--   Put s' -> Debug.trace showPut $ unsafeCoerce $ stepState (k (q ())) s
--     where showPut = "Put " ++ show s' ++ " over " ++ show s

-- {-# INLINE loopState #-}
-- loopState :: MonadEff ('Universe StateMap r) (LookupIndex' 1 StateMap) a -> IO ()
-- loopState m = do
--   case stepState m 0 of
--     m' -> case stepState m' 0 of
--       m'' -> loopState m''

-- -- Increment over a "Trace" effect, emitting it, and iterating.
-- {-# INLINE stepState #-}
-- stepState :: MonadEff ('Universe StateMap r) (Ctor (State Int) :>>= n) a
--           -> Int 
--           -> MonadEff ('Universe StateMap r) (LookupIndex' n StateMap) a
-- stepState ((Eff u q) `Bind` k) s = case u of
--   Get    -> Debug.trace showGet $ unsafeCoerce $ k (q s)
--     where showGet = "Get " ++ show s 
--   Put s' -> Debug.trace showPut $ unsafeCoerce $ k (q ())
--     where showPut = "Put " ++ show s' ++ " over " ++ show s

-- {-# INLINE loopState #-}
-- loopState :: MonadEff ('Universe StateMap r) (LookupIndex' 1 StateMap) a -> IO ()
-- loopState m = do
--   case stepState m 0 of
--     m' -> case stepState m' 0 of
--       m'' -> loopState m''

-- branch (b :: Bool) = case toSing b of
--   SomeSing (sb :: Sing Bool) -> _ sb

-- stepIf :: MonadEff ('Universe u r) ('Ctor (Branch n1 n2)) a
--        -> MonadEff ('Universe u r) (LookupIndex k u) a
-- stepIf (Eff u q) = case u of
--   (Branch True) -> 

-- Runs forever, loops over "Int" domain [0, 1, ..., maxBound, minBound, ... -1]

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
