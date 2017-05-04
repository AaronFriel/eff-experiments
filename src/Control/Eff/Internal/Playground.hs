{-# LANGUAGE ApplicativeDo          #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NoImplicitPrelude      #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE RebindableSyntax       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UnboxedTuples          #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE UndecidableInstances   #-}

module Control.Eff.Internal.Playground where

import qualified Prelude

import Control.Eff.Internal.Eff
import Control.Eff.Internal.Types hiding (Tagged)
import Control.Eff.Internal.FTCQueue
import Prelude.Graphted

import GHC.TypeLits
import GHC.Types    (Constraint, SPEC (..))

import Control.Lens (view, set, Lens, Lens', ALens', LensLike')

import Data.Functor.Identity
import           Data.IORef
import qualified Debug.Trace      as Debug (trace, traceIO, traceShow)
import           System.IO.Unsafe

data Call (n :: Nat) a where
    Call :: Eff u i a -> Call n a

-- type instance TagOf (Call n a) = (Call n a)
type instance EffectResult (Call n a) = a
-- type instance TagData (Call n a) = ()

call :: Eff ('Graph ps hs) i a -> Eff ('Graph ( '(1, EvenT i) ': EvenPaths ps) hs) ('Do (Call 1 a)) a
call = send . Call


data Reader e where Ask :: Reader e
type instance EffectResult (Reader e) = e

ask :: forall e u. Eff u ('Do (Reader e)) e
ask = send Ask

newtype Writer o where Tell :: o -> Writer o
    deriving (Show)

type instance EffectResult (Writer o) = ()

tell :: o -> Eff u ('Do (Writer o)) ()
tell = send . Tell

data Get s = Get
newtype Put s where Put :: s -> Put s

{-# INLINE get #-}
get :: forall e u. Eff u ('Do (Get e)) e
get = send Get

{-# INLINE put #-}
put :: forall e u. e -> Eff u ('Do (Put e)) ()
put = send . Put

type instance EffectResult (Get s) = s
type instance EffectResult (Put s) = ()

-- type family AddCall u2 i2 a u1 i1 where
--     AddCall ('Graph ps2) i2 a ('Graph ps1) i1 =
--         Eff ('Graph ( '(1, i2) ': Interleave (EvenPaths ps2) (OddPaths ps1) )) i1 a

-- type family SimpleCall u2 i2 a = r | r -> u2 i2 a where
--     SimpleCall ('Graph ps) i a =
--         Eff ('Graph ( '(1, i) ': ps) ) ('Do (Call 1 a)) a

-- We need a strong existential type here that verifies for each effect in the universe u
-- there is a handler for that effect. That way we can know how to run the call effect.

-- algCall :: forall u b. (Call n a) -> (EffectResult (Call n a) -> b) -> (HVect s -> (# b, HVect s #))
-- algCall (Call a n) q = \vec -> (q )

simpleEff :: Eff U i a -> Eff U i a
simpleEff a = a

data StdReader (e :: *)

type IdentityT a = a

type instance EffectResult (StdReader e) = e

instance HandlerBase (StdReader e) where
    type HandlerData (StdReader e) = 'Getting e

    -- type HandlerOutput (StdReader e) r = r
    -- getLower = snd . untag

    applyResult = id

-- instance EffectHandler (StdReader e) (Reader e) (LensLike' Identity s e) where
--     handle s Ask = (view s, s)
    -- handle' s Ask = (# view s, s #)

data StdWriter (o :: *)

-- instance HandlerBase (StdWriter o) where
--     type HandlerData (StdWriter o) = 'Just [o]
--     -- type HandlerData (StdWriter o) ('Just l) = Tagged (StdWriter o) ([o], s)
--     -- type HandlerData (StdWriter o) Nothing   = Tagged (StdWriter o) ([o], s)
--     type HandlerOutput (StdWriter o) r = (r, [o])

--     getLower = snd . untag

-- instance EffectHandler (StdWriter o) (Writer o) where
--     handle' (Tell o') q = \(Tagged (o, l)) -> (# q (), Tagged (o' : o, l) #)

-- data StdState (s :: *)

-- instance HandlerBase (StdState s) where
--     type HandlerData (StdState s) lower = Tagged (StdState s) (s, lower)
--     type HandlerOutput (StdState s) r = (r, s)

--     getLower = snd . untag

-- instance EffectHandler (StdState s) (Put s) where
--     handle' (Put s) q = \(Tagged (_, l)) -> (# q (), Tagged (s, l) #)

-- instance EffectHandler (StdState s) (Get s) where
--     handle'  Get    q = \x@(Tagged (s, l)) -> (# q s, x #)

-- data StdTrace

-- instance HandlerBase (StdTrace) where
--     type HandlerData (StdTrace) lower = Tagged StdTrace lower
--     type HandlerOutput (StdTrace) r = r

--     getLower = id . untag

-- instance EffectHandler (StdTrace) (Trace) where
--     handle' (Trace str) q = \l -> seq (unsafePerformIO (Debug.traceIO str)) (# q (), l #)


-- test2 :: Int -> Eff U ('Do (Get Int) :>>= 'TLeaf 'Pure) Int
-- type inferred see testCall
test2 a = simpleEff $ do
    b <- get @Int
    return (a + b)

test1 a = do
    b <- get @Int
    _ <- put @Int (b+1)
    r <- call $ test2 a
    return (b + a + r)

-- This type is inferred!
testCall
  :: Int
     -> Eff
          ('Graph
             '[ '(1,
                 ('Do (Get Int)
                    ':>>= 'TNode ('TLeaf ('Fmapped ('Do (Put Int)))) ('TLeaf 'Pure))
                      ':<*> 'Do (Call 2 Int)),
               '(2, 'Fmapped ('Do (Get Int)))]
             '[])
          ('Do (Get Int) ':>>= 'TLeaf ('Fmapped ('Do (Put Int)) ':<*> 'Do (Call 1 Int)))
          Int
testCall a = do
    b <- get @Int
    _ <- put @Int (a * b)
    r <- call (test1 b)
    return r

type instance EffectResult (Call i a) = a


data HVect (ts :: [*]) where
    HNil  :: HVect '[]
    (:&:) :: !t -> !(HVect ts) -> HVect (t ': ts)

infixr 9 :&:


instance Show (TagData t) => Show (Tagged t) where
    show (Tagged a) = show a

instance Show (HVect '[]) where
    show _ = "HNil"

instance (Show t, Show (HVect ts)) => Show (HVect (t ': ts)) where
    show (t :&: ts) = show t ++ " :&: " ++ show ts

instance (Show t) => Show (IORef t) where
    show t = unsafePerformIO $ Prelude.fmap show (readIORef t)

newtype Tagged t where Tagged :: TagData t -> Tagged t

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

-- class HasAlg e es where
--     getAlg :: HVect es -> Alg e

-- instance {-# OVERLAPPING #-} HasAlg e (Alg e ': xs) where
--     {-# INLINE getAlg #-}
--     getAlg (a :&:  _) = a

-- instance {-# OVERLAPPABLE #-} HasAlg e es => HasAlg e (Alg e' ': es) where
--     {-# INLINE getAlg #-}
--     getAlg (a :&: xs) = getAlg @e xs

-- type EffectAlgebra effect = forall s b. HasTag (TagOf effect) s => effect -> (EffectResult effect -> b) -> (HVect s -> (# b, HVect s #))

-- newtype Alg effect where Alg :: EffectAlgebra effect -> Alg effect

-- -- algWriter :: forall o s b. HasTag (Writer o) s => (Writer o) -> (EffectResult (Writer o) -> b) -> (HVect s -> (b, HVect s))
-- algWriter :: forall o. EffectAlgebra (Writer o)
-- algWriter (Tell o') q = \s -> (# q (), mutVec @(Writer o) (o' :) s #)

-- algReader :: forall e. EffectAlgebra (Reader e)
-- algReader (Ask) q = \s -> (# q (getVec @(Reader e) s), s #)

genWriter :: forall o ts. HVect ts -> HVect (Tagged (Writer o) ': ts)
genWriter = (Tagged [] :&:)

genReader :: forall e ts. e -> HVect ts -> HVect (Tagged (Reader e) ': ts)
genReader e = (Tagged e :&:)

genInit :: HVect '[]
genInit = HNil

-- {-# INLINE algPut #-}
-- algPut :: forall s. EffectAlgebra (Put s)
-- algPut (Put s) q = \vec ->
--     let ref = getVec @(State s) vec
--     in unsafePerformIO (writeIORef ref s) `seq` (# q (), vec #)

-- {-# INLINE algGet #-}
-- algGet :: forall s. IORef (EffectResult (Get s)) ~ TagData (State s) => EffectAlgebra (Get s)
-- algGet (Get) q = \vec ->
--     let ref = getVec @(State s) vec
--         val = unsafePerformIO (readIORef ref)
--     in (# q $! val, vec #)

-- addAlgState :: forall s ts. HVect ts -> HVect (Alg (Put s) ': Alg (Get s) ': ts)
-- addAlgState vec = Alg (algPut) :&: Alg (algGet) :&: vec

{-# INLINE genState #-}
genState :: forall s ts. s -> HVect ts -> HVect (Tagged (State s) ': ts)
genState e =
    let ref = unsafePerformIO $ newIORef e
    in ref `seq` (Tagged ref :&:)


newtype Trace where Trace :: String -> Trace

type family TagData e
type family TagOf e

type instance TagOf (Trace) = (Trace)
type instance TagOf (Put s) = (State s)
type instance TagOf (Get s) = (State s)
type instance EffectResult (Trace) = ()
type instance EffectResult (Get s) = s
type instance EffectResult (Put s) = ()
type instance TagData (Trace) = ()
type instance TagData (State s) = IORef s
type instance TagData (Writer o) = [o]
type instance TagData (Reader e) = e

class HasTag (TagOf effect) s => AlgebraInstance effect s where
    runAlgebra :: forall b. effect -> (EffectResult effect -> b) -> (HVect s -> (# b, HVect s #))

instance HasTag (TagOf Trace) ts => AlgebraInstance Trace ts where
    {-# INLINABLE runAlgebra #-}
    runAlgebra (Trace s) q = \vec -> Debug.trace s () `seq` (# q (), vec #)

instance (HasTag (TagOf (Get s)) ts, TagData (State s) ~ IORef (EffectResult (Get s))) => AlgebraInstance (Get s) ts where
    {-# INLINABLE runAlgebra #-}
    runAlgebra (Get) q = \vec ->
        let ref = getVec @(State s) vec
            val = unsafePerformIO (readIORef ref)
        in (# q $! val, vec #)

instance (HasTag (TagOf (Put s)) ts, TagData (State s) ~ IORef (EffectResult (Get s))) => AlgebraInstance (Put s) ts where
    {-# INLINABLE runAlgebra #-}
    runAlgebra (Put s) q = \vec ->
        let ref = unsafePerformIO $ newIORef s
        in ref `seq` (# q (), putVec @(State s) ref vec #)
    -- If deterministic, can directly mutate:
    -- runAlgebra (Put s) q = \vec ->
    --     let ref = getVec @(State s) vec
    --     in unsafePerformIO (writeIORef ref s) `seq` (# q (), vec #)

genTrace :: HVect ts -> HVect (Tagged Trace ': ts)
genTrace = (Tagged () :&:)

-- traceShow :: Show s => s -> Eff u ('Do Trace) ()
-- traceShow = send . Trace . show

trace = send . Trace

-- type family HasTagsForTree i ts :: Constraint where
--     HasTagsForTree 'Pure      ts = ()
--     HasTagsForTree ('Do e)    ts = (AlgebraInstance e ts, HasTag (TagOf e) ts)
--     HasTagsForTree (i :>>= j) ts = (HasTagsForTree i ts, HasTagsForTree (FViewL j) ts)
--     HasTagsForTree (i :<*> j) ts = (HasTagsForTree i ts, HasTagsForTree j ts)

-- type family HasTagsForPaths u ts :: Constraint where
--     HasTagsForPaths               '[]   ts = ()
--     HasTagsForPaths ( '(n1, p1) ': ps ) ts = (HasTagsFor p1 ts, HasTagsForPaths ps ts)

-- type family HasTagsForU u ts :: Constraint where
--     HasTagsForU ('Graph ps) ts = HasTagsForPaths ps ts

type family HasTagsFor i ts :: Constraint where
    HasTagsFor 'Pure         ts = ()
    HasTagsFor ('Do e)       ts = (AlgebraInstance e ts, HasTag (TagOf e) ts)
    HasTagsFor ('Fmapped i)  ts = (HasTagsFor i ts)
    HasTagsFor (i :>>= j) ts = (HasTagsFor i ts, HasTagsFor (FViewL j) ts)
    HasTagsFor (i :<*> j) ts = (HasTagsFor i ts, HasTagsFor j ts)

run :: forall i u ts a. HasTagsFor i ts => HVect ts -> Eff u i a -> (a, HVect ts)
run ts m = case run' SPEC ts m of
    (# r, ts' #) -> (r, ts')

-- {-# INLINABLE run' #-}
run' :: forall i u ts a. HasTagsFor i ts => SPEC -> HVect ts -> Eff u i a -> (# a, HVect ts #)
run' _ ts (V x) = (# x, ts #)
run' _ ts m@(E _) = go m
    where
        {-# INLINE go #-}
        go :: forall e. (AlgebraInstance e ts, HasTag (TagOf e) ts) => Eff u ('Do e) a -> (# a, HVect ts #)
        go (E u) = runAlgebra @e u id ts
run' sPEC ts m@(F _ _) = go m
    where
        {-# INLINE go #-}
        go :: forall i. (HasTagsFor ('Fmapped i) ts) => Eff u ('Fmapped i) a -> (# a, HVect ts #)
        go (F a f) = 
            let (# a', ts' #) = run' @i sPEC ts a
            in (# f a', ts' #) 
run' sPEC ts m@(B _ _) = go sPEC m
    where
        {-# INLINE go #-}
        go :: forall i j. HasTagsFor (i :>>= j) ts => SPEC -> Eff u (i :>>= j) a -> (# a, HVect ts #)
        go sPEC (B u q) = loop sPEC (run' @i sPEC ts u) q
            where
                {-# INLINABLE loop #-}
                loop :: forall x k. (HasTagsFor (FViewL k) ts)
                     => SPEC -> (# x, HVect ts #) -> FTCQueue (Eff u) k x a -> (# a, HVect ts #)
                loop sPEC (# x, ts' #) q = case tviewl q of
                    TOne q'  -> run' sPEC ts' (q' x)
                    q' :< qs' -> loop sPEC (run' sPEC ts' (q' x)) qs'
run' sPEC ts m@(A _ _) = go sPEC m
    where
        {-# INLINE go #-}
        go :: forall i j. HasTagsFor (i :<*> j) ts => SPEC -> Eff u (i :<*> j) a -> (# a, HVect ts #)
        go sPEC (A f a) =
            let (# f', ts'  #) = run' @i sPEC ts f
                (# a', ts'' #) = run' @j sPEC ts' a
            in (# f' a', ts'' #)


type family EvenQ q where
    EvenQ (TLeaf r) = TLeaf (EvenT r)
    EvenQ (TNode t1 t2) = TNode (EvenQ t1) (EvenQ t2)


type family OddQ q where
    OddQ (TLeaf r) = TLeaf (OddT r)
    OddQ (TNode t1 t2) = TNode (OddQ t1) (OddQ t2)

type family EvenT t = r where
    EvenT    'Pure       = 'Pure
    EvenT   ('Fmapped i)     = 'Fmapped (EvenT i) 
    EvenT ( 'Do (Call n a) ) = 'Do (Call (n + n) a)
    EvenT (    'Do e ) = 'Do e
    EvenT ( i :<*> j ) = EvenT i :<*> EvenT j
    EvenT ( i :>>= j ) = EvenT i :>>= EvenQ j

type family OddT t where
    OddT    'Pure         = 'Pure
    OddT   ('Fmapped i)     = 'Fmapped (OddT i)
    OddT ( 'Do (Call n a) ) = 'Do (Call ((n * 2) + 1) a)
    OddT (    'Do e ) = 'Do e
    OddT ( i :<*> j ) = OddT i :<*> OddT j
    OddT ( i :>>= j ) = OddT i :>>= EvenQ j

type family EvenPaths u = r where
    EvenPaths '[] = '[]
    EvenPaths ( '(n, t) ': rs) = '(n * 2, EvenT t) ': rs

type family OddPaths u where
    OddPaths '[] = '[]
    OddPaths ( '(n, t) ': rs) = '((n * 2) + 1, OddT t) ': rs

-- This generates nicer types than just appending.
type family Interleave xs ys where
    Interleave      '[]        ys  = ys
    Interleave       xs       '[]  = xs
    Interleave (x ': xs) (y ': ys) = x ': y ': Interleave xs ys



-- -- Type is inferred.
-- -- t1 :: Eff u ('Aps ('Aps ('Do (Reader Int)) ('Do (Reader Float))) ('Do (Reader String))) (Int, Float, String)
-- -- t1 :: Eff U (('Do (Reader Int) ':<*> 'Do (Reader Float)) ':<*> 'Do (Reader String)) (Int, Float, String)
-- t1 = do
--     a <- ask @Int
--     b <- ask @Float
--     c <- ask @String
--     G.pure (a, b, c)

-- -- t2 :: Eff U ('Do (Reader Int) ':>>= 'TLeaf ('Do (Writer String))) Int
t2 = do 
    a <- ask @Int
    tell (show a)
    return (a + 1)

t2init = genWriter @String $ genReader @Int 42 $ genInit
-- t2alg  = Alg (algWriter @String) :&: Alg (algReader @Int) :&: HNil 
-- t2r = run t2init t2

t3init = genTrace (genState @Int 42 $ genState @Float (0.1 + 0.2) $ genInit)
-- t3alg = Alg algTrace :&: (addAlgState @Int $ addAlgState @Float $ HNil)

t3_once z = do
    x <- get @Int
    y <- get @Float
    _ <- trace ("x : " ++ show x)
    _ <- trace ("y : " ++ show y)
    let y' = log (fromIntegral x * y + fromIntegral z)
        x' = (x + round y + z) `div` 2
    _ <- put @Float y'
    _ <- put @Int x'
    return $ x' + round y' + z `div` 2

t3 z = do
    let do_once z = t3_once z
        do_4 z = do_once z >>= do_once >>= do_once >>= do_once
        do_16 z = do_4 z >>= do_4 >>= do_4 >>= do_4
        do_64 z = do_16 z >>= do_16 >>= do_16 >>= do_16
    z' <- do_64 z
    x <- get @Int
    y <- get @Float
    return (x, y, z')

-- -- Inferred type:
Couldn't guess that module name. Does it exist?
t3r = let (r, y) = run t3init (t3 5) in y `seq` (r, y) 
