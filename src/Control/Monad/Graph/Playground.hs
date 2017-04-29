{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ApplicativeDo #-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeInType #-}

{-# LANGUAGE FlexibleContexts #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE LiberalTypeSynonyms #-}

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}

{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE PartialTypeSignatures #-}

{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE NoMonoLocalBinds #-}
{-# LANGUAGE InstanceSigs #-}

{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MagicHash #-}

{-# LANGUAGE StrictData #-}

{-# OPTIONS_GHC -Wno-unticked-promoted-constructors -Wno-missing-signatures -Wno-unused-imports -Wno-type-defaults -Wno-partial-type-signatures #-}

module Control.Monad.Graph.Playground where

import Control.Monad.Graph.Eff

import qualified Control.Monad.Graph.Prelude as G

import GHC.Exts (Constraint)

import GHC.TypeLits hiding (type (*))
import Data.Kind (type (*))
import Data.Proxy
import GHC.Types (SPEC(..))
-- import Data.Singletons.Prelude
-- import Data.Singletons.Prelude.Bool
-- import Data.Singletons.TypeRepStar
-- import Data.Singletons.Decide
import Unsafe.Coerce
-- import Control.Lens hiding ((%~), (:<))
import qualified Debug.Trace as Debug (trace, traceShow)
import Data.IORef
import System.IO.Unsafe

-- import Debug.Trace

import Prelude hiding (
    -- Functor
    fmap, (<$), (<$>),
    -- Applicative
    pure, (<*>), (*>), (<*), 
    -- Monad
    return, (>>=), (=<<), (>>),
    fail
    )


infixl 4  <$
infixl 1  >>, >>=
-- infixr 1  =<<
infixl 4 <*>, <*, *>

{-# INLINE fmap #-}
fmap :: (a -> b) -> GraphEff u i a -> GraphEff u (GraphMap i) b
fmap = G.fmap

{-# INLINE (<$) #-}
(<$) :: b -> GraphEff u i a -> GraphEff u (GraphMap i) b
(<$) = (G.<$)

{-# INLINE (<$>) #-}
(<$>) :: (a -> b) -> GraphEff u i a -> GraphEff u (GraphMap i) b
(<$>) = G.fmap

{-# INLINE pure #-}
pure :: a -> GraphEff u 'Pure a
pure = G.pure

{-# INLINE (<*>) #-}
(<*>) :: GraphEff u i (a -> b) -> GraphEff u j a -> GraphEff u (GraphAp i j) b
(<*>) = (G.<*>)

{-# INLINE return #-}
return :: a -> GraphEff u 'Pure a
return = G.pure

{-# INLINE (>>=) #-}
(>>=) :: GraphEff u i a -> (a -> GraphEff u j b) -> GraphEff u (GraphBind i j) b
(>>=) = (G.>>=)

{-# INLINE join #-}
join :: GraphEff u i (GraphEff u j b) -> GraphEff u (GraphBind i j) b
join = G.join

{-# INLINE (<*) #-}
(<*) :: GraphEff u i a -> GraphEff u j b -> GraphEff u (GraphAp (GraphMap i) j) a
(<*) = (G.<*)

{-# INLINE (*>) #-}
(*>) :: GraphEff u i a -> GraphEff u j b -> GraphEff u (GraphAp (GraphMap i) j) b
(*>)= (G.*>)

{-# INLINE (>>) #-}
(>>) :: GraphEff u i a -> GraphEff u j b -> GraphEff u (GraphAp (GraphMap i) j) b
m >> k = (G.*>) m k

{-# INLINE (=<<) #-}
(=<<) :: (a -> GraphEff u j b) -> GraphEff u i a -> GraphEff u (GraphBind i j) b
(=<<) = flip (>>=)

fail = G.fail

{-       ######## ######## ######## ########  ######  ########  ######  
         ##       ##       ##       ##       ##    ##    ##    ##    ## 
         ##       ##       ##       ##       ##          ##    ##       
         ######   ######   ######   ######   ##          ##     ######  
         ##       ##       ##       ##       ##          ##          ## 
         ##       ##       ##       ##       ##    ##    ##    ##    ## 
         ######## ##       ##       ########  ######     ##     ######        -}


data Reader e where Ask :: Reader e
type instance Output (Reader e) = e

ask :: forall e u. GraphEff u ('Do (Reader e)) e
ask = send Ask

newtype Writer o where Tell :: o -> Writer o
    deriving (Show)

type instance Output (Writer o) = ()

tell :: o -> GraphEff u ('Do (Writer o)) ()
tell = send . Tell

data Get s = Get
newtype Put s where Put :: s -> Put s

{-# INLINE get #-}
get :: forall e u. GraphEff u ('Do (Get e)) e
get = send Get

{-# INLINE put #-}
put :: forall e u. e -> GraphEff u ('Do (Put e)) ()
put = send . Put

type instance Output (Get s) = s
type instance Output (Put s) = ()

data Call (n :: Nat) a where
    Call :: GraphEff u i a -> Call n a

call :: forall n u i a. GraphEff u i a -> GraphEff u ('Do (Call n a)) a
call = send . Call

type instance Output (Call i a) = a

-- -- Type is inferred.
-- -- t1 :: GraphEff u ('Aps ('Aps ('Do (Reader Int)) ('Do (Reader Float))) ('Do (Reader String))) (Int, Float, String)
-- -- t1 :: GraphEff U (('Do (Reader Int) ':<*> 'Do (Reader Float)) ':<*> 'Do (Reader String)) (Int, Float, String)
-- t1 = do
--     a <- ask @Int
--     b <- ask @Float
--     c <- ask @String
--     G.pure (a, b, c)

-- -- t2 :: GraphEff U ('Do (Reader Int) ':>>= 'TLeaf ('Do (Writer String))) Int
t2 = do 
    a <- ask @Int
    tell (show a)
    G.pure (a + 1)

-- simpleEff :: GraphEff U i a -> GraphEff U i a
-- simpleEff a = a

-- auto :: ((GraphEff u i a -> GraphEff u ('Do (Call 0 a)) a) -> GraphEff u i a) -> GraphEff u i a
-- auto m = m undefined

-- tloop :: GraphEff u ('Do (Writer [Char]) ':<*> 'Do (Call 0 a)) a
-- tloop = auto $ \cc -> do
--     tell "Foobar"
--     cc tloop

data HVect (ts :: [*]) where
    HNil  :: HVect '[]
    (:&:) :: !t -> !(HVect ts) -> HVect (t ': ts)

infixr 9 :&:

newtype Tagged (t :: *) where Tagged :: TagData t -> Tagged t

instance Show (TagData t) => Show (Tagged t) where
    show (Tagged a) = show a

instance Show (HVect '[]) where
    show _ = "HNil"

instance (Show t, Show (HVect ts)) => Show (HVect (t ': ts)) where
    show (t :&: ts) = show t ++ " :&: " ++ show ts

class HasTag t ts where
    getVec :: HVect ts -> TagData (t)
    putVec :: TagData (t) -> HVect ts -> HVect ts
    mutVec :: (TagData (t) -> TagData (t)) -> HVect ts -> HVect ts

instance {-# OVERLAPPING #-} HasTag t (Tagged t ': xs) where
    {-# INLINE getVec #-}
    {-# INLINE putVec #-}
    {-# INLINE mutVec #-}
    getVec   ((Tagged a) :&:  _) = a
    putVec a (        _  :&: xs) = (Tagged a) :&: xs
    mutVec f ((Tagged a) :&: xs) = (Tagged $ f a) :&: xs

instance {-# OVERLAPPABLE #-} HasTag t xs => HasTag t (Tagged t1 ': xs) where
    {-# INLINE getVec #-}
    {-# INLINE putVec #-}
    {-# INLINE mutVec #-}
    getVec   (a :&: xs) = getVec @t xs
    putVec a (b :&: xs) = b :&: putVec @t a xs 
    mutVec f (b :&: xs) = b :&: mutVec @t f xs

data State s

type family TagOf (effect :: *) :: *
type instance TagOf (Reader e) = Reader e
type instance TagOf (Writer o) = Writer o
type instance TagOf (State s) = State s
type instance TagOf (Put s) = State s
type instance TagOf (Get s) = State s

type family TagData (effect :: *) :: *

type instance TagData (Writer a) = [a]
type instance TagData (Reader e) = Output (Reader e)
type instance TagData (Reader e) = Output (Reader e)
type instance TagData (State s) = IORef s

class HasAlg e es where
    getAlg :: HVect es -> Alg e

instance {-# OVERLAPPING #-} HasAlg e (Alg e ': xs) where
    {-# INLINE getAlg #-}
    getAlg (a :&:  _) = a

instance {-# OVERLAPPABLE #-} HasAlg e es => HasAlg e (Alg e' ': es) where
    {-# INLINE getAlg #-}
    getAlg (a :&: xs) = getAlg @e xs

type EffectAlgebra effect = forall s b. HasTag (TagOf effect) s => effect -> (Output effect -> b) -> (HVect s -> (# b, HVect s #))

newtype Alg effect where Alg :: EffectAlgebra effect -> Alg effect

-- algWriter :: forall o s b. HasTag (Writer o) s => (Writer o) -> (Output (Writer o) -> b) -> (HVect s -> (b, HVect s))
algWriter :: forall o. EffectAlgebra (Writer o)
algWriter (Tell o') q = \s -> (# q (), mutVec @(Writer o) (o' :) s #)

algReader :: forall e. EffectAlgebra (Reader e)
algReader (Ask) q = \s -> (# q (getVec @(Reader e) s), s #)

genWriter :: forall o ts. HVect ts -> HVect (Tagged (Writer o) ': ts)
genWriter = (Tagged [] :&:)

genReader :: forall e ts. e -> HVect ts -> HVect (Tagged (Reader e) ': ts)
genReader e = (Tagged e :&:)

genInit :: HVect '[]
genInit = HNil

{-# INLINE algPut #-}
algPut :: forall s. EffectAlgebra (Put s)
algPut (Put s) q = \vec -> 
    let ref = getVec @(State s) vec
    in unsafePerformIO (writeIORef ref s) `seq` (# q (), vec #)
    -- (q (), mutVec @(State s) (\ref -> unsafePerformIO (writeIORef ref s)) vec)

{-# INLINE algGet #-}
algGet :: forall s. IORef (Output (Get s)) ~ TagData (State s) => EffectAlgebra (Get s)
algGet (Get) q = \vec -> 
    let ref = getVec @(State s) vec
        val = unsafePerformIO (readIORef ref)
    in (# q $! val, vec #)
-- algGet (Get) q = \vec -> (q (getVec @(State s) vec), vec)

addAlgState :: forall s ts. HVect ts -> HVect (Alg (Put s) ': Alg (Get s) ': ts)
addAlgState vec = Alg (algPut) :&: Alg (algGet) :&: vec

{-# INLINE genState #-}
genState :: forall s ts. s -> HVect ts -> HVect (Tagged (State s) ': ts)
genState e = 
    let ref = unsafePerformIO $ newIORef e
    in ref `seq` (Tagged ref :&:)

newtype Trace where Trace :: String -> Trace

type instance TagOf (Trace) = (Trace)
type instance Output (Trace) = ()
type instance TagData (Trace) = ()

class HasTag (TagOf effect) s => AlgebraInstance effect s where
    runAlgebra :: forall b. effect -> (Output effect -> b) -> (HVect s -> (# b, HVect s #))

instance HasTag (TagOf Trace) ts => AlgebraInstance Trace ts where
    {-# INLINABLE runAlgebra #-}
    runAlgebra (Trace s) q = \vec -> Debug.trace s () `seq` (# q (), vec #)

instance (HasTag (TagOf (Get s)) ts, TagData (State s) ~ IORef (Output (Get s))) => AlgebraInstance (Get s) ts where
    {-# INLINABLE runAlgebra #-}
    runAlgebra (Get) q = \vec -> 
        let ref = getVec @(State s) vec
            val = unsafePerformIO (readIORef ref)
        in (# q $! val, vec #)

instance (HasTag (TagOf (Put s)) ts, TagData (State s) ~ IORef (Output (Get s))) => AlgebraInstance (Put s) ts where
    {-# INLINABLE runAlgebra #-}
    runAlgebra (Put s) q = \vec -> 
        let ref = getVec @(State s) vec
        in unsafePerformIO (writeIORef ref s) `seq` (# q (), vec #)

{-# INLINE algTrace #-}
algTrace :: EffectAlgebra (Trace)
algTrace (Trace s) q = \vec -> Debug.trace s () `seq` (# q (), vec #)

genTrace :: HVect ts -> HVect (Tagged Trace ': ts)
genTrace = (Tagged () :&:)

traceShow :: Show s => s -> GraphEff u ('Do Trace) ()
traceShow = send . Trace . show

trace = send . Trace

type family HasTagsFor i ts :: Constraint where
    HasTagsFor 'Pure      ts = ()
    HasTagsFor ('Do e)    ts = (AlgebraInstance e ts, HasTag (TagOf e) ts)
    HasTagsFor (i :>>= j) ts = (HasTagsFor i ts, HasTagsFor (FViewL j) ts)
    HasTagsFor (i :<*> j) ts = (HasTagsFor i ts, HasTagsFor j ts)

run :: forall i u ts a. HasTagsFor i ts => HVect ts -> GraphEff u i a -> (a, HVect ts)
run ts m = case run' SPEC ts m of
    (# r, ts' #) -> (r, ts')

{-# INLINABLE run' #-}
run' :: forall i u ts a. HasTagsFor i ts => SPEC -> HVect ts -> GraphEff u i a -> (# a, HVect ts #)
run' _ ts (V x) = (# x, ts #)
run' _ ts m@(E _ _) = go m
    where
        {-# INLINE go #-}
        go :: forall e. (AlgebraInstance e ts, HasTag (TagOf e) ts) => GraphEff u ('Do e) a -> (# a, HVect ts #)
        go (E u q) = runAlgebra @e u q ts
run' sPEC ts m@(B _ _) = go sPEC m
    where 
        {-# INLINE go #-}
        go :: forall i j. HasTagsFor (i :>>= j) ts => SPEC -> GraphEff u (i :>>= j) a -> (# a, HVect ts #)
        go sPEC (B u q) = loop sPEC (run' @i sPEC ts u) q
            where
                {-# INLINABLE loop #-}
                loop :: forall x k. (HasTagsFor (FViewL k) ts)
                     => SPEC -> (# x, HVect ts #) -> FTCQueue (GraphEff u) k x a -> (# a, HVect ts #)
                loop sPEC (# x, ts' #) q = case tviewl q of
                    TOne q'  -> run' sPEC ts' (q' x)
                    q' :< qs' -> loop sPEC (run' sPEC ts' (q' x)) qs'
run' sPEC ts m@(A _ _) = go sPEC m
    where
        {-# INLINE go #-}
        go :: forall i j. HasTagsFor (i :<*> j) ts => SPEC -> GraphEff u (i :<*> j) a -> (# a, HVect ts #)
        go sPEC (A f a) = 
            let (# f', ts'  #) = run' @i sPEC ts f
                (# a', ts'' #) = run' @j sPEC ts' a
            in (# f' a', ts'' #)

-- class RunEffect i where
--     -- {-# INLINABLE run #-}
--     run :: (HasTagsFor i ts) => HVect ts -> GraphEff u i a -> (a, HVect ts)
--     run ts g = case runS ts g of
--         (# a, t #) -> (a, t)

--     runS :: (HasTagsFor i ts) => HVect ts -> GraphEff u i a -> (# a, HVect ts #)

-- instance RunEffect 'Pure where
--     -- {-# INLINABLE runS #-}
--     runS ts (V x) = (# x, ts #)

-- instance RunEffect ('Do e) where
--     -- {-# INLINABLE runS #-}
--     runS ts (E u q) = (runAlgebra @e u q) ts

-- instance (BindStep (i :>>= j)) => RunEffect (i :>>= j) where
--     -- {-# INLINABLE runS #-}
--     runS :: forall ts a u. (HasTagsFor (i :>>= j) ts, BindStep (i :>>= j))
--          => HVect ts -> GraphEff u (i ':>>= j) a -> (# a, HVect ts #)
--     runS ts (B u q) = go (runS @i ts u) q
--       where 
--         -- These constraints can't be inferred.
--         -- {-# INLINABLE go #-}
--         go :: forall x k. (BindStep (FViewL k), RunEffect (FViewL k), HasTagsFor (FViewL k) ts) 
--            => (# x, HVect ts #) -> FTCQueue (GraphEff u) k x a -> (# a, HVect ts #)
--         go (# x, ts' #) q   = case tviewl q of
--             TOne q'   -> runS ts' (q' x)
--             q' :< qs' -> go (runS ts' (q' x)) qs'
--     -- {-# INLINE runS #-}
--     -- runS :: forall ts a u. (HasTagsFor (i :>>= j) ts, BindStep (i :>>= j))
--     --      => SPEC -> HVect ts -> GraphEff u (i ':>>= j) a -> (# a, HVect ts #)
--     -- runS sPEC ts (B u q) = go sPEC (runS @i sPEC ts u) q
--     --   where 
--     --     -- These constraints can't be inferred.
--     --     {-# INLINE go #-}
--     --     go :: forall x k. (BindStep (FViewL k), RunEffect (FViewL k), HasTagsFor (FViewL k) ts) 
--     --        => SPEC -> (# x, HVect ts #) -> FTCQueue (GraphEff u) k x a -> (# a, HVect ts #)
--     --     go sPEC (# x, ts' #) q   = case tviewl q of
--     --         TOne q'   -> runS sPEC ts' (q' x)
--     --         q' :< qs' -> go sPEC (runS sPEC ts' (q' x)) qs'

-- instance (RunEffect i, RunEffect j) => RunEffect (i :<*> j) where
--     {-# INLINABLE runS #-}
--     runS ts (A f a) = 
--         let (# f', ts'  #) = runS @i ts f
--             (# a', ts'' #) = runS @j ts' a
--         in (# f' a', ts'' #)


-- t2init = genWriter @String $ genReader @Int 42 $ genInit
-- t2alg  = Alg (algWriter @String) :&: Alg (algReader @Int) :&: HNil 
-- t2r = run t2init t2alg t2


-- t3init = genTrace (genState @Int 42 $ genState @Float (0.1 + 0.2) $ genInit)
-- t3alg = Alg algTrace :&: (addAlgState @Int $ addAlgState @Float $ HNil)

-- t3 z = run t3init t3alg $ do
--     let do_once z = do
--             x <- get @Int
--             y <- get @Float
--             _ <- trace ("x : " ++ show x)
--             _ <- trace ("y : " ++ show y)
--             _ <- put @Float (fromIntegral x * y + fromIntegral z)
--             _ <- put @Int (x + round (log y) + z)
--             return (x + round y + z)
--         do_4 z = do_once z >>= do_once >>= do_once >>= do_once
--         do_8 z = do_4 z >>= do_4
--     z' <- do_8 z
--     x <- get @Int
--     y <- get @Float
--     return (x, y)

-- -- Inferred type:
-- t3r = run t3init t3alg (t3 5)
