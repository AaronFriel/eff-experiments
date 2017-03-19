{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE ExplicitNamespaces    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MagicHash             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StrictData            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -fprint-explicit-kinds #-}
-- {-# LANGUAGE QuasiQuotes #-}

module Data.Iota.Unified.Indexed3
 -- ( Eff )
 where

import           Control.Monad.Indexed
import           Data.Proxy
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude
import           Data.Singletons.Prelude.Num
import           Data.Singletons.Prelude.Enum
import           Data.Singletons.Prelude.Ord
import           Data.Type.Equality
import           Data.Type.Map               hiding (Map)
import           Data.Type.Set               hiding ((:++))
import qualified Debug.Trace                 as Debug
import           GHC.Exts                    (inline)
import           GHC.Prim                    (Any, Proxy#, proxy#)
import           GHC.TypeLits                hiding (type (*))
import           Unsafe.Coerce               (unsafeCoerce)
-- import Data.Singletons.Prelude.Num
-- import Data.Singletons.Prelude.Enum
import           Control.Applicative
import           Control.Monad
import           Data.Kind
import           Data.Singletons.TypeLits

-- --
-- --  ███████  █████  ███    ███ ██ ██      ██ ███████ ███████
-- --  ██      ██   ██ ████  ████ ██ ██      ██ ██      ██
-- --  █████   ███████ ██ ████ ██ ██ ██      ██ █████   ███████
-- --  ██      ██   ██ ██  ██  ██ ██ ██      ██ ██           ██
-- --  ██      ██   ██ ██      ██ ██ ███████ ██ ███████ ███████
--
type family FindElem (t :: * -> *) (r :: [* -> *]) :: Nat where
        FindElem t (t ': r) = 0
        FindElem t (u ': r) = 1 :+ FindElem t r
        FindElem t _ =
                     TypeError
                       ('Text "The type " :<>:
                          'ShowType t :<>:
                            'Text " is not an element in the universe provided.")

-- type family GetIstrs k (p :: Program [k] m) :: [k] where
--   GetIstrs k (p :: Program '[] m) = '[k]

type family AddIndex' t r ixs :: [(* -> *, Nat)] where
        AddIndex' t r ixs = ixs :++ '[ '(t, FindElem t r)]

type family AddIndex t r ixs :: [(* -> *, Nat)] where
        AddIndex t r ixs = AddIndex' t (Fst r) ixs

type family Reduce (ixs :: [(* -> *, Nat)]) :: [(* -> *, Nat)]
     where
        Reduce '[] = '[]
        Reduce ('(t, 0) ': r) = Reduce r
        Reduce ('(t, n) ': r) = '(t, n - 1) ': Reduce r

type family Decomp t (ixs :: [(* -> *, Nat)]) :: [Bool] where
        Decomp t ('(t, 0) ': r) = True ': Decomp t r
        Decomp t ('(u, 0) ': r) = False ': Decomp t r
        Decomp t ('(u, n) ': r) = Decomp t ('(u, n - 1) ': r)
        Decomp t '[] = '[]

--
-- type family Length r :: Nat where
--     Length '[] = 0
--     Length (u ': r) = 1 :+ Length r
--
-- -- type family Last r where
-- --     Last (u ': '[]) = u
-- --     Last (u ': r)   = Last r
--
-- {-# INLINE [2] withKnownNat' #-}
-- withKnownNat' :: forall n r. Sing n -> (KnownNat n => r) -> r
-- withKnownNat' SNat f = f
-- {-# RULES
--   "withKnownNat'"     forall n f. withKnownNat' n f = f
-- #-}
--
-- {-# INLINE [2] succ' #-}
-- succ' :: forall n r. (KnownNat n) => Sing n -> (KnownNat (n + 1) => r) -> r
-- succ' SNat f = withKnownNat' (SNat @n %:+ SNat @1) f
-- {-# RULES
--   "succ'"     forall n f. succ' n f = f
-- #-}
--
-- {-# INLINE [2] pred' #-}
-- pred' :: forall n r. (KnownNat n) => Sing n -> (KnownNat (n - 1) => r) -> r
-- pred' SNat f = withKnownNat' (SNat @n %:- SNat @1) f
-- {-# RULES
--   "pred'"     forall n f. pred' n f = f
-- #-}
--  ███████ ████████  ██████  ██████  ██    ██ ███████ ██    ██ ███████
--  ██         ██    ██      ██    ██ ██    ██ ██      ██    ██ ██
--  █████      ██    ██      ██    ██ ██    ██ █████   ██    ██ █████
--  ██         ██    ██      ██ ▄▄ ██ ██    ██ ██      ██    ██ ██
--  ██         ██     ██████  ██████   ██████  ███████  ██████  ███████
--                               ▀▀
-- Non-empty tree. Deconstruction operations make it more and more
-- left-leaning
data FTCQueue m a b where
        Leaf :: (a -> m i j b) -> FTCQueue m a b
        Node :: FTCQueue m a x -> FTCQueue m x b -> FTCQueue m a b

-- Exported operations
-- There is no tempty: use (tsingleton return), which works just the same.
-- The names are chosen for compatibility with FastTCQueue
{-# INLINE tsingleton #-}

tsingleton :: (a -> m i j b) -> FTCQueue m a b
tsingleton r = Leaf r

-- snoc: clearly constant-time
{-# INLINE (|>) #-}

(|>) :: FTCQueue m a x -> (x -> m i j b) -> FTCQueue m a b
t |> r = Node t (Leaf r)

-- append: clearly constant-time
{-# INLINE (><) #-}

(><) :: FTCQueue m a x -> FTCQueue m x b -> FTCQueue m a b
t1 >< t2 = Node t1 t2

-- Left-edge deconstruction
data ViewL m a b where
        TOne :: (a -> m i j b) -> ViewL m a b
        (:|) :: (a -> m i j x) -> (FTCQueue m x b) -> ViewL m a b

{-# INLINABLE tviewl #-}
tviewl
    :: FTCQueue m a b -> ViewL m a b
tviewl (Leaf r) = TOne r
tviewl (Node t1 t2) = go t1 t2
  where
    go :: FTCQueue m a x -> FTCQueue m x b -> ViewL m a b
    go (Leaf r) tr       = r :| tr
    go (Node tl1 tl2) tr = go tl1 (Node tl2 tr)

--
data IxQ m i k a b where
        IxLeaf :: (a -> m i k b) -> IxQ m i k a b
        IxNode :: IxQ m i j a x -> IxQ m j k x b -> IxQ m i k a b

-- ███████ ███████ ███████
-- ██      ██      ██
-- █████   █████   █████
-- ██      ██      ██
-- ███████ ██      ██
-- type Arr r a b = a -> (Eff r) b
type Arrs a b = FTCQueue Eff a b

-- data Instructions (istr :: [[(* -> *, Nat)]]) = Instructions
-- data Instruction (n :: [(* -> *, Nat)]) where
--     Instruction :: Instruction n

type family AddEffect (i :: [(* -> *, Maybe Nat)]) (e :: * -> *) :: [(* -> *, Maybe Nat)] where
  AddEffect i e = i :++ '[ '(e, Nothing) ]

-- type family FindDepth (i :: [(* -> *, Maybe Nat)]) (e :: * -> *) :: Maybe Nat where
--   FindDepth            '[] e = Nothing
--   FindDepth ('(t, n) ': r) e = n
--   FindDepth (      _ ': r) e = FindDepth r e

type family SetDepth (i :: [(* -> *, Maybe Nat)]) (e :: * -> *) (n :: Nat) :: [(* -> *, Maybe Nat)] where
  SetDepth                  '[] e n = '[]
  SetDepth ('(e, Nothing) ': r) e n = '(e, Just n) ': SetDepth r e n
  SetDepth ('(e,  Just n) ': _) _ _ = TypeError
                                        ('Text "The effect " :<>: 'ShowType e
                                         :<>: 'Text " has already been interpreted.")
  SetDepth (            i ': r) e n = i ': SetDepth r e n 

type family RunEffect (i :: [(* -> *, Maybe Nat)]) (e :: * -> *) :: [(* -> *, Maybe Nat)] where
  RunEffect i e = SetDepth i e (Succ (MaxDepth i))

type family MaxDepth (i :: [(* -> *, Maybe Nat)]) :: Nat where
    MaxDepth                  '[] = 0
    MaxDepth ('(_, Nothing) ': r) = MaxDepth r
    MaxDepth ('(_,  Just n) ': r) = Max (MaxDepth r) n 

type family FullyInterpreted (i :: [(* -> *, Maybe Nat)]) :: Bool where
    FullyInterpreted                  '[] = True
    FullyInterpreted ('(_,  Just n) ': r) = FullyInterpreted r
    FullyInterpreted ('(e, Nothing) ': r) = TypeError
                                              ('Text "The effect " :<>: 'ShowType e
                                               :<>: 'Text " has not been interpreted.")

type family EffectDepths (i :: [(* -> *, Maybe Nat)]) (e :: * -> *) :: [Bool] where
    EffectDepths i e = EffectDepths' (RunEffect i e) e

type family EffectDepths' (i :: [(* -> *, Maybe Nat)]) (e :: * -> *) :: [Bool] where
    EffectDepths'            '[] _ = '[]
    EffectDepths' ('(e, Just 1) ': r) e = True  ': EffectDepths' r e
    EffectDepths' ('(_, Just 1) ': r) e = False ': EffectDepths' r e
    EffectDepths' ('(u, Just n) ': r) e = EffectDepths' ('(u, Just (Pred n)) ': r) e

data Eff (i :: [(* -> *, Maybe Nat)]) (j :: [(* -> *, Maybe Nat)]) (a :: *)
  where
    Val :: a -> Eff i j a
    E :: ctor v -> Arrs b a -> Eff i j a

data HelloWorld (v :: *) where
        HelloWorld :: HelloWorld v

-- greet :: forall i. Eff '[] (AddEffect '[] HelloWorld) String
greet = send (HelloWorld :: HelloWorld String)

t_1 :: Eff '[] '[] String
t_1 = Val "Foo"

t_2 = greet >>>= ireturn

-- t_3 = greet >>>= const greet >>>= ireturn

-- runHelloWorld = 

run :: (FullyInterpreted j ~ True) => Eff '[] j a -> a
run (Val x) = x

send :: forall ctor v i. ctor v -> Eff i (AddEffect i ctor) v
send t = E t (tsingleton Val)

--     ibind :: (a -> Eff r j k b) -> Eff r i j a -> Eff r i k b
--     k `ibind` Val x =
--         case k x of
--             E u q -> E u q
--             Val y -> Val y
--     k `ibind` E u q = E u (q |> k)


--     k `ibind` E u q = E u (q |> k)

qApp
    :: forall i j b w.
       Arrs b w -> b -> Eff i j w
qApp q x =
    case inline tviewl q of
        TOne k ->
            case k x of
                Val y -> Val y
                E u q -> E u q
        k :| t ->
            case k x of
                Val y -> qApp t y
                E u q -> E u (q >< t)

qComp :: Arrs b w -> (Eff i j w -> c) -> b -> c
qComp g h = h . qApp g

-- send :: t v -> Eff r i (AddIndex t r i) a

runHelloWorld
    :: forall r i j w b.
       SingI (EffectDepths j HelloWorld)
    => Eff i j w -> Eff i (RunEffect j HelloWorld) w
runHelloWorld m = loop m
  where
    {-# INLINE loop #-}
    loop (Val x) = Val x
    loop m@(E u q) = loopE (fromSing (sing :: Sing (EffectDepths j HelloWorld))) m
      where
        -- loopE :: Proxy# (Sing (p ': ps)) -> Eff t t1 j a -> Eff r i (Reduce j) a
        {-# INLINE loopE #-}
        loopE _ (Val x)         = Val x
        loopE [] (E u q)        = error "IMPOSSIBLE!"
        loopE (True:p) (E u q)  = loopE p $ qApp (unsafeCoerce q) "Hello, World!"
        loopE (False:p) (E u q) = E u (tsingleton (qComp q (loopE p)))

-- data Call fn x
--   where
--     Call :: Call fn ()

-- data Eff (u :: [EffectCtor]) (i :: Program x m) (j :: Program y n) (a :: *)
--   where
--     Val :: a -> Eff r i j a
--     E :: t v -> Arrs r b a -> Eff r i j a

-- -- type family ProgramIstrs p :: [Instruction i] where
-- --   ProgramIstrs (Program ixs _) = ixs

-- type family ProgramFns p where
--   ProgramFns (Program _ fns) = fns

-- type family WriteEffect e p where
--   WriteEffect e p = Program (ProgramIstrs p :++ e) (ProgramFns p)

-- send :: t v -> Eff r i (AddIndex t r i) a
-- send t = E t (tsingleton Val)

-- Combines "Union" and "Eff"
-- data Eff (r :: [* -> *]) (p :: [Mapping Symbol (Instructions m)]) (EffectDepth ctor d) (j :: [(* -> *, Nat)]) (a :: *)
--      where
--         Val :: a -> Eff r p i j a
--         E :: t v -> Arrs r p b a -> Eff r p i j a

-- type family Reduce (ixs :: [(* -> *, Nat)]) :: [(* -> *, Nat)]
--      where
--         Reduce '[] = '[]
--         Reduce ('(t, 0) ': r) = Reduce r
--         Reduce ('(t, n) ': r) = '(t, n - 1) ': Reduce r

-- type family Jump (s :: Symbol) (k) :: * where
--     Jump s (Eff r p i j a) = Eff r p i j a

-- {-| Lookup elements from a map -}
-- type family Lookup' (m :: [Mapping k v]) (c :: k) :: v where
--             Lookup' ((k :-> v) ': m) k = v
--             Lookup' (kvp ': m)       k = Lookup' m k
--             Lookup' '[]              k = TypeError
--                        ('Text "The symbol " :<>:
--                           'ShowType k :<>:
--                             'Text " is not an element in the map provided.")
-- seal :: Eff r '[] j a -> Eff r '[] j a
-- seal = id

instance IxFunctor (Eff) where
    imap f (Val x) = Val (f x)

instance IxPointed (Eff) where
    ireturn = Val

instance IxApplicative (Eff) where
    Val f `iap` Val x = Val $ f x
    Val f `iap` E u q = E u (q |> (Val . f))
    -- E u q `iap` Val x = E u (q |> (Val . ($ x)))
    -- E u q `iap` E u' q' = E u (q |> (\f -> E u' (q' |> (Val . f))))
    E u q `iap` m = E u (q |> (`imap` m))

instance IxMonad (Eff) where
    ibind :: (a -> Eff j k b) -> Eff i j a -> Eff i k b
    k `ibind` Val x =
        case k x of
            E u q -> E u q
            Val y -> Val y
    k `ibind` E u q = E u (q |> k)

-- type Send k = forall r i a. Eff r i (AddIndex k r i) a

-- -- ██████  ███████  █████  ██████  ███████ ██████
-- -- ██   ██ ██      ██   ██ ██   ██ ██      ██   ██
-- -- ██████  █████   ███████ ██   ██ █████   ██████
-- -- ██   ██ ██      ██   ██ ██   ██ ██      ██   ██
-- -- ██   ██ ███████ ██   ██ ██████  ███████ ██   ██
-- -- | Reader
-- data Reader (e :: *) (v :: *) where
--         Reader :: Reader e e

-- ask
--     :: forall r i e a.
--        Eff r i (AddIndex (Reader e) r i) e
-- ask = send (Reader :: Reader e e)

-- {-# INLINE runReader #-}

-- runReader
--     :: forall r i j w b.
--        SingI (Decomp (Reader b) j)
--     => Eff (Reader b ': r) i j w -> b -> Eff r i (Reduce j) w
-- runReader m e = loop m
--   where
--     {-# INLINE loop #-}
--     loop (Val x) = Val x
--     loop m@(E u q) = loopE (fromSing (sing :: Sing (Decomp (Reader b) j))) m
--       where
--         -- loopE :: Proxy# (Sing (p ': ps)) -> Eff t t1 j a -> Eff r i (Reduce j) a
--         {-# INLINE loopE #-}
--         loopE _ (Val x)         = Val x
--         loopE [] (E u q)        = error "IMPOSSIBLE!"
--         loopE (True:p) (E u q)  = loopE p $ qApp (unsafeCoerce q) e
--         loopE (False:p) (E u q) = E u (tsingleton (qComp q (loopE p)))

-- data Writer t x where
--         Writer :: t -> Writer t ()

-- -- tell :: Member (Writer o) r => o -> Eff r ()
-- -- tell :: i -> Eff t r (AddIndex (Writer i) t r) a
-- tell t = send $ Writer t

-- {-# INLINE runWriter #-}

-- runWriter
--     :: forall r i j w t.
--        SingI (Decomp (Writer t) j)
--     => Eff (Writer t ': r) i j w -> [t] -> Eff r i (Reduce j) (w, [t])
-- runWriter m w = loop w m
--   where
--     {-# INLINE loop #-}
--     loop w (Val x) = Val (x, w)
--     loop w m@(E u q) =
--         loopE w (fromSing (sing :: Sing (Decomp (Writer t) j))) m
--       where
--         {-# INLINE loopE #-}
--         loopE w _ (Val x) = Val (x, w)
--         loopE w [] (E u q) = error "IMPOSSIBLE!"
--         loopE w (True:p) (E u q) =
--             case unsafeCoerce u of
--                 (Writer o :: Writer t ()) ->
--                     loopE (o : w) p $ qApp (unsafeCoerce q) ()
--         loopE w (False:p) (E u q) = E u (tsingleton (qComp q (loopE w p)))

-- -- t3 =
-- --     [ido|do
-- --   tell ("Begin\n" :: String)
-- --   foo :: String <- ask
-- --   _ <- t2'
-- --   bar :: Int    <- ask
-- --   tell (foo ++ show bar ++ "\n")
-- --   tell "End"
-- --   ireturn bar
-- -- |]
-- -- t3rr =
-- --     run .
-- --     flip runReader ("foo" :: String) .
-- --     flip runReader (5 :: Int) .
-- --     flip runReader (5 :: Float) . flip runWriter ([] :: [String]) $
-- --     t3
-- data State s v where
--         Get :: State s s
--         Put :: !s -> State s ()

-- --
-- get
--     :: forall r i e a.
--        Eff r i (AddIndex (State e) r i) e
-- get = send (Get :: State e e)

-- put
--     :: forall r i s a.
--        s -> Eff r i (AddIndex (State s) r i) ()
-- put s = send (Put s)

-- {-# INLINE runState #-}

-- runState
--     :: forall r i j w s.
--        SingI (Decomp (State s) j)
--     => Eff (State s ': r) i j w -> s -> Eff r i (Reduce j) (w, s)
-- runState m s = loop s m
--   where
--     {-# INLINE loop #-}
--     loop s (Val x) = Val (x, s)
--     loop s m@(E u q) = loopE s (fromSing (sing :: Sing (Decomp (State s) j))) m
--       where
--         {-# INLINE loopE #-}
--         loopE s _ (Val x) = Val (x, s)
--         loopE s [] (E u q) = error "IMPOSSIBLE!"
--         loopE s (True:p) (E u q) =
--             case (unsafeCoerce u :: State s v) of
--                 (Put s') -> loopE s' p $ qApp (unsafeCoerce q) ()
--                 (Get)    -> loopE s p $ qApp (unsafeCoerce q) s
--         loopE s (False:p) (E u q) = E u (tsingleton (qComp q (loopE s p)))

-- -- ts2 =
-- --     [ido| do
-- --   put (10::Int)
-- --   x :: Int <- get
-- --   put (20::Int)
-- --   y :: Int <- get
-- --   ireturn (x+y)
-- -- |]
-- data Fix eff v where
--         Fix :: (a -> eff) -> Fix eff v

-- ixfix = send . Fix

-- {-# INLINE runFix #-}

-- runFix
--     :: forall r i j w s a r' i' j' w'.
--        SingI (Decomp (Fix s) j)
--     => Eff (Fix s ': r) i j w
--     -> _ -- ((a -> Eff r' i' j' w') -> Eff (Fix s : r) i j w)
--     -> Eff '[] '[] '[] w
-- -- => Eff (Fix s ': r) i j w
-- -- -> (Eff r i (Reduce j) w -> Eff '[] '[] '[] w)
-- -- -> Eff r i (Reduce j) w
-- runFix m i10s = loop i10s m
--   where
--     {-# INLINE loop #-}
--     loop s (Val x) = Val x
--     loop s m@(E u q) = loopE s (fromSing (sing :: Sing (Decomp (Fix s) j))) m
--       where
--         {-# INLINE loopE #-}
--         loopE s _ (Val x) = Val x
--         loopE s [] (E u q) = error "IMPOSSIBLE!"
--         loopE s (True:p) (E u q) =
--             case (unsafeCoerce u :: Fix eff v) of
--                 Fix k ->
--                     case run . flip runFix i10s . i10s $
--                          qApp (unsafeCoerce q s) of
--                         y -> Val y
--         loopE s (False:p) (E u q) = E u (tsingleton (qComp q (loopE s p)))

-- -- ts2r = ((30, 20) ==) $ run (runState ts2 (0 :: Int))
-- -- testFib =
-- --     ixfix $
-- --     \m ->
-- --          [ido| do
-- --   a :: Int <- ask
-- --   ireturn $ a : (1 :: Int) : zipWith (+) m (tail m)
-- -- |]
-- -- benchCnt_Iota :: Int -> ((),Int)
-- -- benchCnt_Iota n = run $ runState m n
-- --
-- -- m = Fix do
-- --   x :: Int <- get
-- --   _ <- Fix (\m2 -> m)
-- --   ireturn ()
-- -- |]
-- -- data Fix i10s m v where
-- --   Fix i10s m v ::
-- -- runState :: Eff (State s ': r) w -> s -> Eff r (w,s)
-- -- runState (Val x) s = return (x,s)
-- -- runState (E u q) s = case decomp u of
-- --   Right Get     -> runState (qApp q s) s
-- --   Right (Put s) -> runState (qApp q ()) s
-- --   Left  u -> E u (tsingleton (\x -> runState (qApp q x) s))
-- -- loop w m@(E u q) = loopE w (natVal' @j0 proxy#) m
-- --   where loopE w n (Val x) = Val (x, w)
-- --         loopE w 0 (E u q) =
-- --           case unsafeCoerce u of
-- --             (Writer o :: Writer t ()) -> loopE (o:w) 0 $ qApp (unsafeCoerce q) ()
-- --         loopE w n (E u q) = E u (tsingleton (qComp q (loopE w (n-1))))
-- showRun
--     :: Eff '[] '[] j a -> Eff '[] '[] j a
-- showRun = id

-- -- t1' =
-- --     [ido|do
-- --   a <- ask
-- --   ireturn (a + (1 :: Int))
-- -- |]
-- --
-- -- t1 =
-- --     ask >>>=
-- --     (\a ->
-- --           ireturn (a + (2 :: Int)))
-- --
-- -- t2' =
-- --     [ido|do
-- --   float5 :: Float <- Debug.trace "ask Float" ask
-- --   int1   :: Int <- Debug.trace "ask Int" ask
-- --   int2   :: Int <- Debug.trace "ask Int" ask
-- --   int3   :: Int <- Debug.trace "ask Int" ask
-- --   float1 :: Float <- Debug.trace "ask Float" ask
-- --   float2 :: Float <- Debug.trace "ask Float" ask
-- --   int4   :: Int <- Debug.trace "ask Int" ask
-- --   float3 :: Float <- Debug.trace "ask Float" ask
-- --   float4 :: Float <- Debug.trace "ask Float" ask
-- --   ireturn (int1, int2, int3, int4, float1, float2, float3, float4)
-- -- |]
-- -- t2'rr = run $ runReader (runReader t2' (5 :: Int)) (10 :: Float)
-- --
-- -- t2 =
-- --     ask >>>=
-- --     (\a ->
-- --           (ask >>>=
-- --            \(b :: Integer) ->
-- --                 ireturn (a + fromIntegral b + (1 :: Int))))
-- --
-- -- t3rr' =
-- --     run .
-- --     flip runWriter ([] :: [String]) .
-- --     flip runReader (5 :: Int) .
-- --     flip runReader (5 :: Float) . flip runReader ("foo" :: String) $
-- --     t3
-- -- type UMember t r h = (KnownNat (Length r), KnownNat (Length h), KnownNat (FindElem t (r :++ '[t] :++ h)))
-- --
-- -- -- {-# INLINE handleRelay #-}
-- -- -- handleRelay :: forall t r h w a. UMember t r h
-- -- --             => (a -> Eff r (t ': h) w)
-- -- --             -> (forall v. t v -> Arr r (t ': h) v w -> Eff r (t ': h) w)
-- -- --             -> Eff (t ': r) h a -> Eff r (t ': h) w
-- -- -- handleRelay ret handler m = loop m
-- -- --  where
-- -- --   loop (Val x) = ret x
-- -- --   loop e = loopE (natVal $ SNat @(Length r)) (natVal $ SNat @(Length h)) e
-- -- --   -- -- loopE _ _ (Val x) =
-- -- --   -- --      Debug.trace ("@(Length r) = " ++ show (natVal (Proxy @(Length r)))
-- -- --   -- --              ++ "\n@(Length h) = " ++ show (natVal (Proxy @(Length h)))
-- -- --   -- --              ++ "\n returning Val x"
-- -- --   -- --                  ) ret x
-- -- --   loopE _ _ (Val x) = ret x
-- -- --   loopE r 0 (E u q) =
-- -- --     let k = qComp q loop
-- -- --      in Debug.trace ("float @(Length r) = " ++ show (natVal (Proxy @(Length r)))
-- -- --                             ++ "\t@(Length h) = " ++ show (natVal (Proxy @(Length h)))
-- -- --                             ++ "\t@(Length h) = " ++ show (natVal (Proxy @(Length h)))
-- -- --                             ++ "\t returning singleton x"
-- -- --                             ) $ E u (tsingleton (qComp q (loopE (r-1) 0)))
-- -- --   loopE r h (E u q) =
-- -- --     let k = qComp q loop
-- -- --      in Debug.trace ("float @(Length r) = " ++ show (natVal (Proxy @(Length r)))
-- -- --                             ++ "\t@(Length h) = " ++ show (natVal (Proxy @(Length h)))
-- -- --                             ++ "\t returning coersion x"
-- -- --               ) $ handler (unsafeCoerce u) (qComp q (loopE (r-1) h))
-- --
-- -- {-# INLINE handleRelay #-}
-- -- -- handleRelay :: forall a r i n j w t. KnownNat n => (a -> Eff r i (Sing (SNat n ': j)) w) ->
-- -- --                 (forall v. t v -> Arr r i (Sing (SNat n ': j)) v w -> Eff r i (Sing (SNat n ': j)) w) ->
-- -- --                 Eff (t ': r) i (Sing (SNat n ': j)) a -> Eff r i (Sing (SNat n ': j)) w
-- -- handleRelay ret h m = loop m
-- --   where
-- --     loop (Val x)   = ret x
-- --     loop e = loopE (natVal' @0 proxy#) e
-- --       where loopE 0 (E u q) = h (unsafeCoerce u) (qComp q loop)
-- --             loopE n (E u q) = E u (tsingleton (qComp q (relabel (loopE (n-1)))))
-- -- {-# INLINE handleRelay' #-}
-- -- handleRelay' :: forall t r h w a. UMember t r h
-- --             => String -> (a -> Eff r (t ': h) w)
-- --             -> (forall v. t v -> Arr r (t ': h) v w -> Eff r (t ': h) w)
-- --             -> Eff (t ': r) h a -> Eff r (t ': h) w
-- -- handleRelay' str ret handler m = loop m
-- --  where
-- --   loop (Val x) = ret x
-- --   loop e@(E (u :: t1 v) q) = loopE (natVal' @(FindElem t1 (t ': r)) proxy#) e
-- --     where loopE _ (Val x) = ret x
-- --           loopE 0 e = handler (unsafeCoerce u) (qComp q (loopE 0))
-- --           loopE n e = undefined -- unsafeCoerce $ E u (tsingleton (qComp q (loopE (n-1))))
-- --
-- -- -- handleRelay str ret handler n u q = loop n
-- -- --   where loop 0 = handler (unsafeCoerce u) (qComp q (loopE 0))
-- -- --         loop n = E u (tsingleton (qComp q (loopE (n-1))))
-- --     -- let k = qComp q loop
-- --     --  in case u of
-- --           -- (v :: t1 v) -> loopE n (E u q)
-- --           --   case SNat @(FindElem t1 (t ': r)) %~ SNat @0 of
-- --           --     Proved _ ->  Debug.trace (str ++ " @(Length r) = " ++ show (natVal (Proxy @(Length r)))
-- --           --                          ++ "\tFindElem = " ++ show (natVal (Proxy @(FindElem t1 (t ': r))))
-- --           --                          ++ "\treturning coersion x"
-- --           --              ) $ handler (unsafeCoerce v) k
-- --           --     _        -> Debug.trace (str ++ " @(Length r) = " ++ show (natVal (Proxy @(Length r)))
-- --           --                          ++ "\tFindElem = " ++ show (natVal (Proxy @(FindElem t1 (t ': r))))
-- --           --                          ++ "\t returning singleton x"
-- --           --              ) $ undefined -- $ E v (tsingleton k)
-- --
-- --
-- --
-- --     -- TOne k -> handler (unsafeCoerce u) (qComp q loop)
-- --     -- k :| t -> E u (_ k t)
-- --   -- loop e = loopE (natVal $ SNat @(Length r)) (natVal $ SNat @(Length h)) e
-- --   -- -- -- loopE _ _ (Val x) =
-- --   -- -- --      Debug.trace ("@(Length r) = " ++ show (natVal (Proxy @(Length r)))
-- --   -- -- --              ++ "\n@(Length h) = " ++ show (natVal (Proxy @(Length h)))
-- --   -- -- --              ++ "\n returning Val x"
-- --   -- -- --                  ) ret x
-- --   -- loopE _ _ (Val x) = ret x
-- --   -- loopE r 0 (E u q) =
-- --     -- let k = qComp q loop
-- --     --  in Debug.trace (str ++ " @(Length r) = " ++ show (natVal (Proxy @(Length r)))
-- --     --                         ++ "\t@(Length h) = " ++ show (natVal (Proxy @(Length h)))
-- --     --                         ++ "\t@(FindElem t (r :++ '[t] :++ h)) = " ++ show (natVal (Proxy @(FindElem t (r :++ '[t] :++ h))))
-- --     --                         ++ "\t returning singleton x"
-- --     --                         ) $ E u (tsingleton (qComp q (loopE r 0)))
-- --   -- loopE r h (E u q) =
-- --   --   let k = qComp q loop
-- --   --    in Debug.trace (str ++ " @(Length r) = " ++ show (natVal (Proxy @(Length r)))
-- --   --                           ++ "\t@(Length h) = " ++ show (natVal (Proxy @(Length h)))
-- --   --                           ++ "\t@(FindElem t (r :++ '[t] :++ h)) = " ++ show (natVal (Proxy @(FindElem t (r :++ '[t] :++ h))))
-- --   --                           ++ "\t returning coersion x"
-- --   --             ) $ handler (unsafeCoerce u) (qComp q (loopE r h))
-- --
-- --   -- -- loopE r 0 (E u q) = Debug.trace ("@(Length r) = " ++ show (natVal (Proxy @(Length r)))
-- --   -- --                      ++ "\n@(Length h) = " ++ show (natVal (Proxy @(Length h)))
-- --   -- --                      ++ "\n returning E u loop x"
-- --   -- --        ) $ E u (tsingleton (qComp q (loopE (r - 1) h)))
-- --
-- --   -- -- GOOD:
-- --   -- loop (E u q) =
-- --   --   let k = qComp q loop
-- --   --    in case
-- --   --         Debug.trace ("@(Length r) = " ++ show (natVal (Proxy @(Length r)))
-- --   --                 ++ "\n@(Length h) = " ++ show (natVal (Proxy @(Length h)))
-- --   --                     )
-- --   --         $ SNat @(FindElem t (t ': r)) %~ SNat @(Length r) of
-- --   --             Proved _ -> Debug.trace "Coercing" $ h (unsafeCoerce u) k
-- --   --             _        -> Debug.trace "Returning E" $ E u (tsingleton k)
-- --
-- --
-- -- {-# INLINE [2] ask #-}
-- -- ask :: forall e r h. (KnownNat (FindElem (Reader e) r)) => Eff r h e
-- -- ask :: Eff r i (AddIndex (_) r i) a
-- -- -- {-# RULES
-- -- -- "get/bind" forall k. ask >>= k = send Reader >>= k
-- -- -- #-}
-- --
-- -- capEff :: Eff r '[] ()
-- -- capEff = Val ()
-- --
-- -- initEff = (capEff >>)
-- -- handleRelay :: forall a r i n j w t. KnownNat n => (a -> Eff r i (Sing (SNat n ': j)) w) ->
-- --                 (forall v. t v -> Arr r i (Sing (SNat n ': j)) v w -> Eff r i (Sing (SNat n ': j)) w) ->
-- --                 Eff (t ': r) i (Sing (SNat n ': j)) a -> Eff r i (Sing (SNat n ': j)) w
-- -- runReader :: Eff (Reader e ': r) _ _ w -> e -> Eff r _ _ w
-- -- runReader m e = loop m
-- --   where
-- --     loop (Val x)   = ireturn x
-- --     loop eff = loopE (natVal' @0 proxy#) eff
-- --       where loopE 0 (E u q) = loop $ relabel (qApp q) e
-- --             loopE n (E u q) = E u (tsingleton (qComp q (relabel (loopE (n-1)))))
-- -- -- runReader :: UMember (Reader e) r h => Eff (Reader e ': r) h w -> e -> Eff r (Reader e ': h) w
-- -- -- runReader m e = handleRelay return (\Reader k -> k e) m
-- --
-- -- runReader' :: UMember (Reader e) r h => String -> Eff (Reader e ': r) h w -> e -> Eff r (Reader e ': h) w
-- -- runReader' str m e = Debug.trace ("runReader " ++ str) $ handleRelay' str return (\Reader k -> Debug.trace ("handle " ++ str) $ k e) m
-- --
-- add
--     :: Monad m
--     => m Int -> m Int -> m Int
-- add = liftM2 (+)--
--                 -- t1 :: KnownNat (FindElem (Reader Int) r) => Eff r h Int
--                 -- -- t1 :: UMember (Reader Int) r '[] => Eff r '[] Int
--                 -- t1 :: Eff r

-- -- f, f1, f2
-- --     :: String
-- --     -> Eff r '[] '[ '(Reader String, FindElem (Reader String) r),
-- --   '(Reader Int, FindElem (Reader Int) r),
-- --   '(Writer String, FindElem (Writer String) r)] Int
-- -- f c =
-- --     ask >>>=
-- --     (\b ->
-- --           ask >>>=
-- --           (\a ->
-- --                 tell (b ++ c) >>>=
-- --                 (\() ->
-- --                       ireturn (a :: Int))))

-- -- f1 c =
-- --     E Reader (Leaf Val) >>>=
-- --     (\b ->
-- --           E Reader (Leaf Val) >>>=
-- --           (\a ->
-- --                 E (Writer $ (b :: String) ++ (c :: String)) (Leaf Val) >>>=
-- --                 (\() ->
-- --                       Val (a :: Int))))

-- -- f2 c =
-- --     E
-- --         Reader
-- --         (Node            -- 1st node
-- --              (Leaf Val)  -- Left edge of 1st node
-- --              (Leaf       -- Right edge of 1st node
-- --                   (\b ->
-- --                         E
-- --                             Reader
-- --                             (Node
-- --                                  (Leaf Val)
-- --                                  (Leaf
-- --                                       (\a ->
-- --                                             E
-- --                                                 (Writer $
-- --                                                  (b :: String) ++ (c :: String))
-- --                                                 (Node
-- --                                                      (Leaf Val)
-- --                                                      (Leaf
-- --                                                           (\() ->
-- --                                                                 Val (a :: Int))))))))))

-- -- tviewl of the first Node is: Val :| (right edge)


-- --
-- -- f1 = frInt . qApp (getQ f' "bar"):
-- -- Run order:
-- rf f =
--     run .
--     flip runWriter ([] :: [String]) .
--     flip runReader ("foo" :: String) . flip runReader (5 :: Int) $
--     f "bar"
