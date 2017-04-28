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

{-# OPTIONS_GHC -Wno-unticked-promoted-constructors -Wno-missing-signatures -Wno-unused-imports -Wno-type-defaults -Wno-partial-type-signatures #-}

module Control.Monad.Graph.Playground where

import Control.Monad.Graph.Eff

import qualified Control.Monad.Graph.Prelude as G

import GHC.Exts (Constraint)

import GHC.TypeLits hiding (type (*))
import Data.Kind (type (*))
import Data.Proxy
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Bool
-- import Data.Singletons.TypeRepStar
import Data.Singletons.Decide
import Unsafe.Coerce
-- import Control.Lens hiding ((%~), (:<))
import qualified Debug.Trace as Debug (trace, traceShow)

-- import Debug.Trace

import Prelude hiding (
    -- Functor
    fmap, (<$), (<$>),
    -- Applicative
    pure, (<*>), (*>), (<*), 
    -- Monad
    return, (>>=), (=<<), (>>)
    )


infixl 4  <$
infixl 1  >>, >>=
-- infixr 1  =<<
infixl 4 <*>, <*, *>


fmap :: (a -> b) -> GraphEff u i a -> GraphEff u (GraphMap i) b
fmap = G.fmap

(<$) :: b -> GraphEff u i a -> GraphEff u (GraphMap i) b
(<$) = (G.<$)

(<$>) :: (a -> b) -> GraphEff u i a -> GraphEff u (GraphMap i) b
(<$>) = G.fmap

pure :: a -> GraphEff u 'Pure a
pure = G.pure

(<*>) :: GraphEff u i (a -> b) -> GraphEff u j a -> GraphEff u (GraphAp i j) b
(<*>) = (G.<*>)

return :: a -> GraphEff u 'Pure a
return = G.pure

(>>=) :: GraphEff u i a -> (a -> GraphEff u j b) -> GraphEff u (GraphBind i j) b
(>>=) = (G.>>=)

join :: GraphEff u i (GraphEff u j b) -> GraphEff u (GraphBind i j) b
join = G.join


(<*) :: GraphEff u i a -> GraphEff u j b -> GraphEff u (GraphAp (GraphMap i) j) a
(<*) = (G.<*)
(*>) :: GraphEff u i a -> GraphEff u j b -> GraphEff u (GraphAp (GraphMap i) j) b
(*>)= (G.*>)

(>>) :: GraphEff u i a -> GraphEff u j b -> GraphEff u (GraphAp (GraphMap i) j) b
m >> k = (G.*>) m k

(=<<) :: (a -> GraphEff u j b) -> GraphEff u i a -> GraphEff u (GraphBind i j) b
(=<<) = flip (>>=)

{-       ######## ######## ######## ########  ######  ########  ######  
         ##       ##       ##       ##       ##    ##    ##    ##    ## 
         ##       ##       ##       ##       ##          ##    ##       
         ######   ######   ######   ######   ##          ##     ######  
         ##       ##       ##       ##       ##          ##          ## 
         ##       ##       ##       ##       ##    ##    ##    ##    ## 
         ######## ##       ##       ########  ######     ##     ######        -}


data Reader e where
    Ask :: Reader e
type instance Output (Reader e) = e

ask :: forall e u. GraphEff u ('Do (Reader e)) e
ask = send Ask

data Writer o where
    Tell :: o -> Writer o
    deriving (Show)

type instance Output (Writer o) = ()

tell :: o -> GraphEff u ('Do (Writer o)) ()
tell = send . Tell

data Get s = Get
newtype Put s where Put :: s -> Put s

get :: forall e u. GraphEff u ('Do (Get e)) e
get = send Get
put :: forall e u. e -> GraphEff u ('Do (Put e)) ()
put = send . Put

type instance Output (Get s) = s
type instance Output (Put s) = ()

data Call (n :: Nat) a where
    Call :: GraphEff u i a -> Call n a

call :: forall n u i a. GraphEff u i a -> GraphEff u ('Do (Call n a)) a
call = send . Call

type instance Output (Call i a) = a

-- Type is inferred.
-- t1 :: GraphEff u ('Aps ('Aps ('Do (Reader Int)) ('Do (Reader Float))) ('Do (Reader String))) (Int, Float, String)
-- t1 :: GraphEff U (('Do (Reader Int) ':<*> 'Do (Reader Float)) ':<*> 'Do (Reader String)) (Int, Float, String)
t1 = do
    a <- ask @Int
    b <- ask @Float
    c <- ask @String
    G.pure (a, b, c)

-- t2 :: GraphEff U ('Do (Reader Int) ':>>= 'TLeaf ('Do (Writer String))) Int
t2 = do 
    a <- ask @Int
    tell (show a)
    G.pure (a + 1)

-- simpleEff :: GraphEff U i a -> GraphEff U i a
-- simpleEff a = a

auto :: ((GraphEff u i a -> GraphEff u ('Do (Call 0 a)) a) -> GraphEff u i a) -> GraphEff u i a
auto m = m undefined

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

head :: HVect (t ': ts) -> t
head (a :&: b) = a

class HasTag t ts where
    getVec :: HVect ts -> TagData (t)
    putVec :: TagData (t) -> HVect ts -> HVect ts
    mutVec :: (TagData (t) -> TagData (t)) -> HVect ts -> HVect ts

instance {-# OVERLAPPING #-} HasTag t (Tagged t ': xs) where
    getVec   ((Tagged a) :&:  _) = a
    putVec a (        _  :&: xs) = (Tagged a) :&: xs
    mutVec f ((Tagged a) :&: xs) = (Tagged $ f a) :&: xs

instance {-# OVERLAPPABLE #-} HasTag t xs => HasTag t (Tagged t1 ': xs) where
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
type instance TagData (State s) = Output (Get s)

mkTag :: forall effect. TagData effect -> Tagged effect
mkTag = Tagged

testVec = mkTag @(Writer String) ["Foobar"] :&: HNil

testGetter = getVec @(Writer String)

testVecGet = testGetter testVec

class HasAlg e es where
    getAlg :: HVect es -> Alg e

instance {-# OVERLAPPING #-} HasAlg e (Alg e ': xs) where
    getAlg (a :&:  _) = a

instance {-# OVERLAPPABLE #-} HasAlg e es => HasAlg e (Alg e' ': es) where
    getAlg (a :&: xs) = getAlg @e xs

type EffectAlgebra effect = forall s b. HasTag (TagOf effect) s => effect -> (Output effect -> b) -> (HVect s -> (b, HVect s))

newtype Alg effect where Alg :: EffectAlgebra effect -> Alg effect

-- algWriter :: forall o s b. HasTag (Writer o) s => (Writer o) -> (Output (Writer o) -> b) -> (HVect s -> (b, HVect s))
algWriter :: forall o. EffectAlgebra (Writer o)
algWriter (Tell o') q = \s -> (q (), mutVec @(Writer o) (o' :) s)

algReader :: forall e. EffectAlgebra (Reader e)
algReader (Ask) q = \s -> (q (getVec @(Reader e) s), s)

genWriter :: forall o ts. HVect ts -> HVect (Tagged (Writer o) ': ts)
genWriter = (Tagged [] :&:)

genReader :: forall e ts. e -> HVect ts -> HVect (Tagged (Reader e) ': ts)
genReader e = (Tagged e :&:)

genInit :: HVect '[]
genInit = HNil

algPut :: forall s. EffectAlgebra (Put s)
algPut (Put s) q = \vec -> (q (), putVec @(State s) s vec)

algGet :: forall s. EffectAlgebra (Get s)
algGet (Get) q = \vec -> (q (getVec @(State s) vec), vec)

addAlgState :: forall s ts. HVect ts -> HVect (Alg (Put s) ': Alg (Get s) ': ts)
addAlgState vec = Alg (algPut) :&: Alg (algGet) :&: vec

genState :: forall s ts. s -> HVect ts -> HVect (Tagged (State s) ': ts)
genState e = (Tagged e :&:)

newtype Trace where Trace :: String -> Trace

type instance TagOf (Trace) = (Trace)
type instance Output (Trace) = ()
type instance TagData (Trace) = ()

algTrace :: EffectAlgebra (Trace)
algTrace (Trace s) q = \vec -> Debug.trace s $ (q (), vec)

genTrace :: HVect ts -> HVect (Tagged Trace ': ts)
genTrace = (Tagged () :&:)

traceShow :: Show s => s -> GraphEff u ('Do Trace) ()
traceShow = send . Trace . show

trace = send . Trace

type family HasTagsFor i ts algs :: Constraint where
    HasTagsFor 'Pure      ts algs = ()
    HasTagsFor ('Do e)    ts algs = (HasTag (TagOf e) ts, HasAlg e algs)
    HasTagsFor (i :>>= j) ts algs = (HasTagsFor i ts algs, HasTagsFor (FViewL j) ts algs)
    HasTagsFor (i :<*> j) ts algs = (HasTagsFor i ts algs, HasTagsFor j ts algs)
    -- HasTagsFor (i :*> j) ts algs = (HasTagsFor i ts algs, HasTagsFor j ts algs)
    -- HasTagsFor (i :<* j) ts algs = (HasTagsFor i ts algs, HasTagsFor j ts algs)
    -- HasTagsFor (GJoin i j) ts algs = (HasTagsFor i ts algs, HasTagsFor j ts algs)
    -- HasTagsFor (GConst i) ts algs = (HasTagsFor i ts algs)

type family BindStep i :: Constraint where
    BindStep (i :>>= j) = (RunEffect i, RunEffect (FViewL j), BindStep i, BindStep (FViewL j))
    BindStep ('Do e)    = RunEffect ('Do e)
    BindStep (i :<*> j) = (BindStep i, BindStep j)
    -- BindStep (i :*> j) = (BindStep i, BindStep j)
    -- BindStep (i :<* j) = (BindStep i, BindStep j)
    -- BindStep (GJoin i j) = (BindStep i, BindStep j)
    -- BindStep (GConst i) = (BindStep i)
    BindStep 'Pure      = ()

class RunEffect i where
    run :: (HasTagsFor i ts algs) => HVect ts -> HVect algs -> GraphEff u i a -> (a, HVect ts)

instance RunEffect 'Pure where
    run ts _ (V x) = (x, ts)

instance RunEffect ('Do e) where
    run ts algs (E u q) = 
        let (Alg alg) = getAlg @e algs
            (r, ts') = (alg u q) ts
        in (r, ts')

instance (BindStep (i :>>= j)) => RunEffect (i :>>= j) where
    run :: forall ts algs a u. (HasTagsFor (i :>>= j) ts algs, BindStep (i :>>= j)) => HVect ts -> HVect algs -> GraphEff u (i ':>>= j) a -> (a, HVect ts)
    run ts algs (B u q) = 
        go (run @i ts algs u) q
      where 
        -- These constraints can't be inferred.
        go :: forall x k. (BindStep (FViewL k), RunEffect (FViewL k), HasTagsFor (FViewL k) ts algs) => (x, HVect ts) -> FTCQueue (GraphEff u) k x a -> (a, HVect ts)
        go (x, ts') q   = case tviewl q of
            TOne q'   -> run ts' algs (q' x)
            q' :< qs' -> go (run ts' algs (q' x)) qs'

instance (RunEffect i, RunEffect j) => RunEffect (i :<*> j) where
    run ts algs (A f a) = 
        let (f', ts') = run @i ts algs f
            (a', ts'') = run @j ts' algs a
        in (f' a', ts'')

-- instance (RunEffect i, RunEffect j) => RunEffect (i :*> j) where
--     run ts algs (Then a b) = 
--         let (a', ts') = run @i ts algs a
--             (b', ts'') = run @j ts' algs b
--         in (b', ts'')

-- instance (RunEffect i, RunEffect j) => RunEffect (i :<* j) where
--     run ts algs (But a b) = 
--         let (a', ts') = run @i ts algs a
--             (b', ts'') = run @j ts' algs b
--         in (a', ts'')

-- instance (RunEffect i) => RunEffect (GConst i) where
--     run ts algs (Const m b) = 
--         let (_, ts') = run @i ts algs m
--         in (b, ts')

-- instance (RunEffect i, RunEffect j) => RunEffect (GJoin i j) where
--     run ts algs (J m) = 
--         let (m', ts') = run @i ts algs m
--             (r, ts'') = run @j ts' algs m'
--         in (r, ts'')

-- t2init = genWriter @String $ genReader @Int 42 $ genInit
-- t2alg  = Alg (algWriter @String) :&: Alg (algReader @Int) :&: HNil 
-- t2r = run t2init t2alg t2

-- t3_1 :: Int -> GraphEff u ('GJoin ('Do (Get Int) ':<*> 'Do (Get Float)) (GraphAp (GraphAp (GraphAp (GraphMap ('Do Trace ':*> j1)) ('Do Trace ':*> j)) ('Do (Put Float) ':*> j2)) ('Do (Put Int) ':*> j3))) Int
t3_1 z = do
    x <- get @Int
    y <- get @Float
    _ <- trace ("x : " ++ show x)
    _ <- trace ("y : " ++ show y)
    _ <- put @Float (fromIntegral x * y + fromIntegral z)
    _ <- put @Int (x + round (log y) + z)
    return (x + round y + z)

t3_2 z = do
    z' <- t3_1 z
    t3_1 z'

t3_4 z = do
    z' <- t3_2 z
    t3_2 z'

t3_8 z = do
    z' <- t3_4 z
    t3_4 z'

t3 z = do
    let do_once z = do
            x <- get @Int
            y <- get @Float
            _ <- trace ("x : " ++ show x)
            _ <- trace ("y : " ++ show y)
            _ <- put @Float (fromIntegral x * y + fromIntegral z)
            _ <- put @Int (x + round (log y) + z)
            return (x + round y + z)
        do_4 z = do_once z >>= do_once >>= do_once >>= do_once
        do_8 z = do_4 z >>= do_4
    z' <- do_8 z
    x <- get @Int
    y <- get @Float
    return (x, y)

t3init = genTrace (genState @Int 42 $ genState @Float (0.1 + 0.2) $ genInit)
t3alg = Alg algTrace :&: (addAlgState @Int $ addAlgState @Float $ HNil)
-- -- Inferred type:
t3r :: ((Int, Float), HVect '[Tagged (Trace), Tagged (State Int), Tagged (State Float)])
t3r = run t3init t3alg (t3 5)
-- == ((),141 :&: 5.2924017e13 :&: HNil)t3r
