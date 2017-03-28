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
-- {-# OPTIONS_GHC -fprint-explicit-kinds #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ExistentialQuantification #-}

{-# OPTIONS_GHC -Wno-unticked-promoted-constructors -Wno-missing-signatures #-}

module Data.Iota.Unified.Indexed4
 -- ( Eff )
 where

import Prelude hiding (return, (>>), (<*>), (>>=), fmap, pure, (<$>))
-- import Control.Monad.Cx.Rebound hiding ((<*>), (>>=))
-- import           Control.Monad.Indexed hiding ((>>>=), (=<<<), iap, IxApplicative (..), IxMonad (..))
-- import Language.Haskell.IndexedDo (ido)
-- import           Data.Proxy
import Data.Singletons

import Data.Promotion.TH
import Data.Singletons.Decide
import Data.Singletons.Prelude hiding (SList)
import Data.Singletons.Prelude.Enum
-- import Data.Singletons.Prelude.List
import Data.Singletons.Prelude.Num
import Data.Singletons.TH
import Data.Singletons.TypeLits
-- import           Data.Singletons.Prelude.Ord
import           Data.Type.Equality

-- import           Data.Type.Map               hiding (Map)
-- import           Data.Type.Set               hiding ((:++))
import qualified Debug.Trace                 as Debug
-- import           GHC.Exts                    (inline)
import           GHC.Prim                    (Any, Proxy#, proxy#)
import           GHC.TypeLits                hiding (type (*))
import           GHC.Prim                    (coerce)
import           Unsafe.Coerce               (unsafeCoerce)
-- import Data.Proxy
-- import Data.Singletons.Prelude.Num
-- import Data.Singletons.Prelude.Enum
-- import           Control.Applicative
-- import           Control.Monad
import           Data.Kind
-- import           Data.Singletons.TypeLits

-- infixl 4 <$, <$>

-- infixl 4 <*>
-- infixl 1 >>, >>=
-- infixr 1 =<|, =<<

data FTCQueue m a b where
        Leaf :: (a -> m b) -> FTCQueue m a b
        Node :: FTCQueue m a x -> FTCQueue m x b -> FTCQueue m a b
        QPure :: (x -> b) -> FTCQueue m a x -> FTCQueue m a b

data IxQueue m a b where
    IxLeaf :: (a -> m b) -> IxQueue m a b
    IxNode :: IxQueue m a x -> IxQueue m x b -> IxQueue m a b
    IxPure :: (x -> b) -> IxQueue m a x -> IxQueue m a b

-- tsingleton :: (a -> m b) -> FTCQueue m a b
-- tsingleton r = Leaf r

-- (~>) :: FTCQueue m a x -> (x -> m b) -> FTCQueue m a b
-- t ~> r = Node t (Leaf r)

-- (><) :: FTCQueue m a x -> FTCQueue m x b -> FTCQueue m a b
-- t1 >< t2 = Node t1 t2

-- type Arrs a b = forall i j. IxQueue (MonadEff j) a b

type family BindOp a b where
  BindOp a b = BindNode a b

data Tree a = ApNode (Tree a) (Tree a) | BindNode (Tree a) (Tree a) | Ctor a | Pure

type family AddCtor ctor where
  AddCtor ctor = Ctor ctor

type family AddAp l r where
  AddAp l r = ApNode l r

type family AddBind l r = result | result -> l r where
  AddBind l r = BindNode l r


-- data MonadView e j a 
--   where
--     V     :: a -> MonadView e 'Pure a
--     E     :: e a -> (a -> b) -> MonadView e ('Ctor '(ctor, a)) b
--     O     :: ctor a -> (a -> b) -> MonadView e ('Ctor '(ctor, a)) b
--     A     :: MonadView e j (a -> b) -> MonadView e k a -> MonadView e ('ApNode j k) b
--     B     :: MonadView e j a -> (a -> MonadView e k b) -> MonadView e ('BindNode j k) b

class IfCxt (cxt :: Constraint) where
    ifCxt :: proxy cxt -> (cxt => a) -> b -> Either b a


instance {-# OVERLAPPABLE #-} IfCxt cxt where ifCxt _ t f = Left f

class IsCorrect (ctor :: * -> *) (v :: * -> *)

-- instance (ctor ~ v) => IsCorrect (ctor :: * -> *) (v :: * -> *)

-- instance {-# OVERLAPS #-} IfCxt (IsCorrect v v) where ifCxt _ t f = t

-- instance {-# OVERLAPS #-} IfCxt ((~) a a) where ifCxt _ t f = t
-- instance {-# OVERLAPS #-} IfCxt (Show a) where ifCxt _ t f = t

-- class ToView (e :: * -> *) j where
--   toView :: MonadEff j w -> MonadView e j w

-- instance ToView e 'Pure where
--   toView (Val a) = V a

-- instance {-# OVERLAPPABLE #-} ToView e ('Ctor '(ctor, a)) where
--   toView (Eff u q) = O u q

-- instance {-# OVERLAPPING #-} ToView e ('Ctor '(e, a)) where
--   toView (Eff u q) = E u q

-- instance (ToView e l, ToView e r) => ToView e ('ApNode l r) where
--   toView (l :<*> r) = A (toView l) (toView r)

-- instance (ToView e l, ToView e r) => ToView e ('BindNode l r) where
--   toView (l :>>= r) = B (toView l) (\a -> toView (r a))


-- class Decomp ctor e where
--   decomp :: MonadEff ('Ctor '(ctor, a)) b
--          -> (e a -> (a -> b) -> b)
--          -> b

-- instance {-# OVERLAPPING #-} Decomp e e where
--   decomp m h = ctorApp m h

-- class CanApply j e a

-- instance CanApply ('Ctor '(e, a)) e a 

-- instance {-# OVERLAPS #-} IfCxt (CanApply ('Ctor '(e, a)) e a) where ifCxt _ t f = Right t

-- class IfCxt' (cxt :: Bool -> Constraint) where
--     ifCxt' :: proxy cxt -> (cxt True => a) -> (cxt False => b) -> Either b a


-- ctorApp :: forall a b e. MonadEff (Ctor '(e, a)) b -> (e a -> (a -> b) -> b) -> b
-- ctorApp (Eff u q) h = h u q

-- type family RunSimple (j :: EffTree) (e :: * -> *) where
--   RunSimple 'Pure _ = 'Pure
--   RunSimple ('Ctor '(e, a)) e = 'Pure
--   RunSimple ('Ctor '(e', a)) e = ('Ctor '(e', a))

foo :: Int
foo = 5

-- run' :: Run j w
-- run' 


run :: MonadEff Pure w -> w
run (Val a) = a

-- runReader :: forall j w (e :: *). MonadEff j w -> e -> Run j w
-- runReader (Val a) e = \r -> Run (Val a) r
-- runReader m@(Eff u q) e = 
--     case ifCxt (Proxy :: Proxy (MonadEff j w ~ MonadEff ('Ctor '(Reader e, e)) w)) ( (\(Eff u q) -> Val $ q e) m) m of
--       Left w -> Run $ w
--       Left m -> error "Foobar!"
    -- case ifCxt (Proxy :: Proxy (MonadEff j w ~ MonadEff ('Ctor '(Reader e, e)) w)) ((\(Eff u q) -> Val $ q e) m) m of
    --   Right w -> w
    --   Left m -> error "Foobar!"


-- testFn :: forall j w (e :: *). MonadEff j w -> e -> MonadEff (RunSimple j (Reader e)) w
-- testFn m e =
--   case ifCxt (Proxy :: Proxy (MonadEff j w ~ MonadEff 'Pure w)) ((\(Val a) -> Val a) m) m of
--     Right w -> w
--     Left m -> case ifCxt (Proxy :: Proxy (MonadEff j w ~ MonadEff ('Ctor '(Reader e, e)) w)) ((\(Eff u q) -> Val $ q e) m) m of
--       Right w -> w
--       Left m -> undefined

-- instance ToView e 'Pure a where
--   toView (Val a) = V a

-- instance ToView e 'Pure a where
--   toView (Val a) = V a


type EffTree = Tree (* -> *, *)

data MonadEff j (a :: *)
  where
    Val     :: a -> MonadEff 'Pure a
    Eff     :: ctor a -> (a -> b) -> MonadEff ('Ctor '(ctor, a)) b
    (:<*>)  :: MonadEff j (a -> b) -> MonadEff k a -> MonadEff ('ApNode j k) b
    (:>>=)  :: MonadEff j a -> (a -> MonadEff k b) -> MonadEff ('BindNode j k) b


imap :: (a -> b) -> MonadEff j a -> MonadEff j b
imap f (Val a) = (Val (f a))
imap f (Eff u q) = Eff u (f . q)
imap f (m :<*> k) = (imap (f .) m :<*> k)
imap f (m :>>= k) = (m :>>= \a -> imap f (k a))

-- runEffect :: forall j w (ctor :: * -> *) a. MonadEff j w -> (ctor a -> (a -> w) -> MonadEff Pure w) -> MonadEff (RunEffect j ctor a) w
-- runEffect (Val a) _ = Val a
-- runEffect m@(Eff u q) h = case m of
--   (m :: MonadEff ('Ctor '(e', a')) w) -> case decomp m u of
--     Left _ -> undefined

-- runEffect m@(Eff u q) h = case decomp (Eff u q) h of
--   Left _ -> undefined
--   Right _ -> undefined

-- type family EqTree (a :: EffTree) (b :: EffTree) where
--   EqTree             'Pure               'Pure = 'True
--   EqTree ('Ctor '(e, a))   ('Ctor '(e, a)) = 'True
--   EqTree   ('ApNode l1 r1)     ('ApNode l2 r2) = (EqTree l1 l2) :&& (EqTree l2 r2)
--   EqTree ('BindNode l1 r1)   ('BindNode l2 r2) = (EqTree l1 l2) :&& (EqTree l2 r2)
--   EqTree                 _                   _ = 'False

-- type instance (a :: EffTree) == (b :: EffTree) = EqTree a b



-- instance {-# OVERLAPPABLE #-} Decomp 'Pure e a where
--   decomp m _ = Left m

-- instance {-# OVERLAPPABLE #-} Decomp j e a where
--   decomp m _ = Left m

-- instance {-# OVERLAPPING #-} (j == (Ctor '(e, a))) ~ True => Decomp (Ctor '(e, a)) e a where
--   decomp m h = Right $ ctorApp m h

-- ctorApp :: MonadEff (Ctor '(e, a)) b -> (e a -> (a -> b) -> MonadEff 'Pure b) -> MonadEff 'Pure b
-- ctorApp (Eff u q) h = h u q

-- -- testCtor :: (j ~ ('Ctor '(e', a')), t ~ (j == (Ctor '(e', a')))) => MonadEff j b -> (e a -> (a -> b) -> MonadEff 'Pure b) -> MonadEff (RunEffect j e a) b
-- -- testCtor m h = case decomp m h of
-- --   Left _ -> undefined

-- type TDecomp (j :: EffTree) (e :: * -> *) a = TDecomp' (j == (Ctor '(e, a))) j e a

-- type family TDecomp' test (j :: EffTree) (e :: * -> *) (a :: *) where
--   TDecomp' True j e a = 'Pure
--   TDecomp' False 'Pure e a = 'Pure
--   TDecomp' False j e a = j

-- type family RunEffect j e a where
--   RunEffect               'Pure _ a = 'Pure
--   RunEffect (Ctor '(e' a', a')) e a = TDecomp (Ctor '(e' a', a')) e a

-- type family EqCtor (a :: * -> *) (b :: * -> *) where
--   EqCtor (t v) (t v) = 'True
--   EqCtor     _     _ = 'False


-- type family RunEffect j eff where
--   RunEffect     ('Ctor '(t, t a)) eff = RunEffect' (EqCtor t eff) ('Ctor '(t, t a)) eff
--   RunEffect                     q eff = RunEffect' True q eff


-- runReader :: forall j w e. MonadEff j w -> e -> MonadEff (RunEffect j (Reader e)) w
-- runReader (Val a) _ = Val a
-- runReader m@(Eff u q) e = case m of
--   (Eff u q :: MonadEff ('Ctor '(t, t v)) w) -> 
--     case (sing :: Sing (EqCtor (Reader e) t)) %~ (sing :: Sing True) of
--       _ -> applyEffect m (\Reader -> e)

-- class ApplyEffect j e v w where
--   applyEffect :: MonadEff j w -> (e v -> v) -> MonadEff (RunEffect j e) w

-- instance ApplyEffect Pure e v w where
--   applyEffect m _ = m

-- instance {-# OVERLAPPABLE #-} (EqCtor ctor e ~ False) => ApplyEffect (Ctor '(ctor, ctor a)) e v w where
--   applyEffect m _ = m

-- instance {-# OVERLAPS #-} (ctor ~ e, EqCtor ctor e ~ True) => ApplyEffect (Ctor '(e, e a)) e a a where
--   applyEffect m@(Eff u q) f = Val $ q (f u)


-- runReader :: MonadEff j w -> e -> MonadEff (RunEffect j (Reader e)) w
-- runReader (Val a) e = Val a
-- runReader m@(Eff u q) e = case m of
--   %==
--   (Eff u q :: MonadEff ('Ctor '(ctor, ctor a)) w) -> 


-- imap f (Val x) = Val (f x)
-- (:>>=)  :: MonadEff i a -> (a -> MonadEff (Reader Int ': j) b) -> MonadEff (i :++ (Reader Int ': j)) b


-- instance CxPointed MonadEff
--   ipoint = Val

-- instance CxFunctor MonadEff
--   imap f (Val x) = Val (f x)
--   imap f (Eff u q) = Eff u (f . q)
--   imap f (x :<*> y) = (imap (f .) x :<*> y)
--   imap f (x :>>= y) = (x :>>= \a -> imap f (y a))

pure = Val
return = pure

-- fmap :: (a -> b) -> MonadEff i a -> MonadEff i b
-- fmap f (Val x) = unsafeCoerce $ Val (f x)
-- fmap f (Eff u q) = Eff u (f . q)
-- fmap f (x :<*> y) = (fmap (f .) x :<*> y)
-- fmap f (x :>>= y) = (x :>>= \a -> fmap f (y a))
-- join = (>>= id)

-- instance CxApplicative MonadEff
--   -- Val f <|*|> Val x  = Val $ f x
-- n <*> m       = n :<*> m

-- instance CxMonad MonadEff
--   -- Val x |>= k = k x
-- m      >>= k = m :>>= k
-- m >> k = m >>= \_ -> k 
-- (<$) = fmap . const

-- -- b -> MonadEff k c
-- test :: (b -> MonadEff k c) -> MonadEff k (b -> c)
-- test m = (:<*>) (Val m) (Val const)


data State s v where
    Put :: s -> State s ()
    Get :: State s s

data NamedState (k :: Symbol) s v where
    IxPut :: s -> NamedState k s ()
    IxGet :: NamedState k s s

send :: forall ctor v. ctor v -> MonadEff ('Ctor '(ctor, v)) v
send t = Eff t id

ask :: forall e. MonadEff ('Ctor '(Reader e, e)) e
ask = send Reader

-- -- tell :: forall o. MonadEff (AddCtor (Writer o)) ()
-- tell o = send (Writer o)

-- put :: forall s. s -> MonadEff (AddCtor (State s ())) ()
-- put = send . Put

-- get :: forall s. MonadEff (AddCtor (State s s)) s
-- get = send Get

-- seal :: MonadEff j a -> MonadEff j a
-- seal = id

-- -- Type is inferred!
-- t1 :: MonadEff '[Reader Float, Reader Int] Int
-- t1 = do
--   a <- ask @Int
--   return a

-- if you squint
-- it looks like:
-- (ap 
--   (ctor Reader Int)
--   (ctor Reader Int ctor Reader Int)
-- )
-- t2 :: MonadEff '[Ap , L , Ctor (Reader Int) , R , L , Ctor (Reader Int), R] Int
-- t2 = seal $ do
--   a <- t1
--   a' <- t1
--   return (a * a')

-- (<$>) = fmap

-- OUT WITH THE OLD

-- t3do, t3applicative :: MonadEff
--        '[ 'Ap, 'L,
--             'Ap,
--                'L, 
--                 'Ctor (Reader Int),
--               'R, 'L, 
--                 'Ctor (Reader Float),
--               'R,
--             'R, 'L,
--               'Ctor (Reader Float),
--           'R]
--        Int

-- IN WITH THE NEW
-- t3do :: MonadEff
--        ('ApNode
--           ('ApNode ('Ctor (Reader Int)) ('Ctor (Reader Float)))
--           ('Ctor (Reader Float)))
--        Int
-- t3do = do
--   a <- ask @Int
--   a' <- ask @Float
--   a'' <- ask @Float
--   return (a * round a' + round a'')

-- t3applicative = (\a a' a'' -> a * round a' * round a'') <$> ask @Int <*> ask @Float <*> ask @Float

-- Dummy functions to use with GHCi to see how simplification type operator runs.
-- simpTest :: MonadEff j Int -> MonadEff (Simplify j) Int
-- simpTest = undefined

-- runInt' :: MonadEff j Int -> MonadEff (RunEffect j (Reader Int)) Int
-- runInt' = undefined

-- runFloat' :: MonadEff j Int -> MonadEff (RunEffect j (Reader Float)) Int
-- runFloat' = undefined


-- type family Member i (ctor :: * -> *) :: Bool where
--   Member '[] ctor        = TypeError ('Text "The effect " ':<>: 'ShowType ctor ':<>: 'Text " is not used.")
--   Member ('Ctor t : r) t = 'True
--   Member ('Ctor u : r) t = Member r t

-- type family Reduce a where
--   Reduce ( 'ApNode Empty Empty   ) = Empty
--   Reduce ( 'BindNode Empty Empty ) = Empty
--   Reduce a = a

-- type family Simplify a where
--   Simplify ('ApNode   l r) = Reduce ( 'ApNode (Reduce l) (Reduce r) )
--   Simplify ('BindNode l r) = Reduce ( 'BindNode (Reduce l) (Reduce r) )
--   Simplify a = a

-- type family RunEffect i ctor where
--   RunEffect ('ApNode   l r) ctor = Reduce ( 'ApNode   (RunEffect l ctor) (RunEffect r ctor) )
--   RunEffect ('BindNode l r) ctor = Reduce ( 'BindNode (RunEffect l ctor) (RunEffect r ctor) )
--   RunEffect ('Ctor ctor _ ) ctor = Empty
--   RunEffect               a    _ = a


-- runReader :: MonadEff j a -> e -> MonadEff (RunEffect j (Reader e)) a
-- runReader (Val a) e = Val a

-- class (Member j (Reader e)) ~ 'True => RunReader i j e where
--TODO: generalize to handleRelay like behavior

type family GetLhsRhs i where
  GetLhsRhs ('BindNode l r) = '(l, r)
  GetLhsRhs ('ApNode   l r) = '(l, r)

-- class RunReader j a e where
--   runReader :: MonadEff j a -> e -> MonadEff (RunEffect j (Reader e)) a

-- instance RunReader (Empty) e e where
--   runReader (Val a) _ = Val a

-- instance RunReader (Ctor (Reader e) v) v e where
--   runReader (Eff u q) e = case testEquality q id of
--     Just refl -> undefined
--     _ -> undefined
--     -- Val (q $ e)

-- instance (RunReader l (a -> b) e, RunReader r a e) => RunReader (ApNode l r) b e where
--   runReader (l :<*> r) e = 
--     let l' = unsafeCoerce l :: MonadEff l (a -> b)
--         r' = unsafeCoerce r :: MonadEff r a
--     in case (runReader l' e, runReader r' e) of
--       (Val f, Val a) -> Val (f a)

-- instance ( '(head, tail) ~ GetArgumentHead r,
--            RunReader '[] head (a -> b) e,
--            RunReader '[] tail a e,
--            Simplify (RunEffect' tail (Reader e))
--                         ~
--                         SimplifyOp' 'Bind (GetArguments (RunEffect' r (Reader e)))
--          ) => RunReader '[] ( 'Ap : r ) b e where
--   runReader (m :<*> k) e =
--     let m' = unsafeCoerce m :: MonadEff head (a -> b)
--         k' = unsafeCoerce k :: MonadEff tail a
--     in case (runReader m' e, runReader k' e) of
--       (Val f, Val a) -> Val (f a)

-- instance ( '(head, tail) ~ GetArgumentHead r,
--            RunReader '[] head a e,
--            RunReader '[] tail b e,
--            Simplify (RunEffect' tail (Reader e))
--                         ~
--                         SimplifyOp' 'Bind (GetArguments (RunEffect' r (Reader e)))
--          ) => RunReader '[] ( 'Bind : r ) b e where
--   runReader (m :>>= k) e =
--     case runReader (unsafeCoerce m :: MonadEff head a) e of
--       Val a  -> flip runReader e $ (unsafeCoerce k :: a -> MonadEff tail b) a
--       -- Eff u q -> undefined



-- instance RunReader '[] '[ 'Ctor (Reader e) ] e e where
--   runReader (Eff _ q) e = Val (unsafeCoerce q $ e)


-- run :: MonadEff (Empty) b -> b
-- run (Val b) = b
-- -- This is safe!
-- run _ = undefined


-- infixl 7 :<*>
-- infixl 6 :>>=

apPrec, bindPrec :: Int
apPrec = 7
bindPrec = 6


-- instance Show (MonadEff j a) where
--   showsPrec _ (Val _)  = showString "Val"
--   showsPrec _ (Eff _ _) = showString "Eff"
--   showsPrec p (a :<*> b) =
--     showParen (p > apPrec) $
--       showsPrec (apPrec+1) a
--       . showString " :<*> "
--       . showsPrec (apPrec+1) b

--   showsPrec p (a :>>= _) =
--     showParen (p > bindPrec) $
--       showsPrec (bindPrec+1) a
--       . showString " :>>= "
--       . showsPrec (bindPrec+1) "m"

--   show t = showsPrec 0 t ""


-- runReader (Val m :>>= k) e = (unsafeCoerce m)
-- runReader (Val x) e = Val x
  -- where
  --   loop (Val x) = Val x
  --   loop (Eff u q) = loop $ (unsafeCoerce q) e
    -- loop (a :<*> b) = undefined
    -- loop (a :>>= b) = undefined
-- t1 = seal [ido|do
--   a :: Float <- ask
--   b :: Int <- ask
--   ireturn (round a + b)
-- |]

-- run :: MonadEff '[] a -> a
-- run (Val b) = b
-- run (Eff u q) = error "Impossible"
-- t1r x = case t1 of
--   Val k -> k
--   Eff u q -> case u of
--     Reader -> undefined

-- -- -- equivalent to `ask`
-- -- t1 = E (Reader @Int) (Leaf (tsingleton Val))

-- -- -- equivalent to `ask >>>= \(a :: Int) -> Val (a + 1)`
-- -- -- t2 = E (Reader @Int) (Leaf (\(Reader a) -> Val $ a + 1))
-- -- -- t2' = E (Reader @Int) (Leaf (\(Reader a) -> Val a) |> (\a -> Val $ a + 1))

-- -- -- equivalent to:
-- -- -- [ido|do
-- -- --   a :: Int <- imap (1+) ask
-- -- --   b :: Float <- ask
-- -- --   ireturn $ a + round b
-- -- -- |]
-- -- -- t3 = E (Reader @Int) (Leaf (\(Reader a) -> Val $ a + 1) |> (\a ->
-- -- --       E (Reader @Float) (Leaf (\(Reader b) -> Val b) |> (\b ->
-- -- --         Val $ a + round b
-- -- --       ))))

-- -- t3r :: Int -> Int
-- -- t3r x = case t1 of
-- --   Val k -> undefined

-- -- equivalent to `ask >>>= \(a :: Int) -> ask >>>= \(b :: Float) ->

-- -- instance QApp a ([a -> Eff1 i j b, b -> Eff2 i j c]) c where
-- --     qApp (Node k t) x = case k x of
-- --         Val y -> qApp t y

-- -- qApp :: IxQueue (Eff i j) a r b -> a -> Eff i j b
-- -- qApp q x =
-- --     case q of
-- --         Leaf k -> k x
-- -- qApp q x =
-- --    case inline q of
-- --      TOne k  -> k x
-- --      k :| t -> case k x of
-- --        Val y -> qApp t y
-- --        E u q -> E u (q >< t)

-- -- qApp
-- --     :: forall i j b w.
-- --        Arrs b w -> b -> Eff i j w
-- -- qApp q x =
-- --     case inline _ q of
-- --         Leaf k ->
-- --             case k x of
-- --                 Val y -> Val y
-- --                 E u q -> E u q
-- --         Node k t -> undefined
--             -- case k x of
--             --     Val y -> qApp t y
--             --     E u q -> E u (q >< t)

-- -- qComp :: Arrs r a b -> (Eff b -> Eff r' c) -> Arr r' a c
-- -- qComp g h = h . qApp g


$(genPromotions [''Tree, ''Reader])

$(promoteOnly [d|

  |])

-- haltVal :: a -> Either Halt a
-- haltVal            a = Right a

-- haltCtor :: (Halt -> 
-- haltCtor _ Halt    _ = Left Halt
-- haltAp   _ Halt    _ = Left Halt
-- haltAp   _ _    Halt = Left Halt
-- haltBind _ Halt    _ = Left Halt

$(promote [d|

  data Writer (o :: *) (v :: *) where
    Writer :: o -> Writer o ()

  |])

$(promote [d|
  newtype Exc (e :: *) (v :: *) = Exc e

  data Halt = Halt

  data ETree a b c o = Opaque o | Ap (ETree a b c o) (ETree a b c o) | Bi (ETree a b c o) c | Pu b | Ct a 


  -- -- runError :: ETree (Exc Halt -> a) b ->
  -- runError Opaque = Opaque
  -- runError (Pu a) = Pu (Right a)
  -- runError (Ct _) = Pu (Left Halt)
  -- runError (Ap (Ct _)      r) = Pu (Left Halt) 
  -- runError (Ap      l (Ct _)) = Pu (Left Halt)
  -- runError (Ap      l      r) = Ap (runError l) (runError r)
  -- runError (Bi (Ct _)      r) = Pu (Left Halt) 
  -- runError (Bi      l (Ct _)) = Pu (Left Halt)
  -- runError (Bi      l      r) = Ap (runError l) (runError r)

  -- runReader' :: t -> ETree (t -> b) b -> ETree a b
  runReader' e (Opaque t) = t id
  runReader' e (Pu a)     = a id
  runReader' e (Ct f)     = Pu (f e)
  runReader' e (Ap l r) = Ap (runReader' e l) (runReader' e r)
  runReader' e (Bi l f) = Bi (runReader' e l) (f e)

  addWrite o a = (a, [o])
  -- mergeWrite (a, [o]) (a', [o']) = mergeWrite 

  -- runWriter' :: ETree k a -> ETree a (a, [t])
  runWriter' o (Opaque t) = t (addWrite o)
  runWriter' o (Pu a) = a (addWrite o)
  runWriter' o (Ct (k, f)) = Pu (f (), k:o)
  -- runWriter' o (Ap l r) = l
  -- runWriter' o (Bi l f) = f (runWriter' o l)

  -- runWriter' o (Ap l r) = Ap (runWriter' o l) (runWriter' o r)
  -- runWriter' o (Bi l r) = Ap (runWriter' e l) (runWriter' e r)

  |])

$(promote [d|

  -- recoverTree Opaque   t = t recoverTree Opaque
  -- recoverTree (Pu _)   = Pure
  -- recoverTree (Ct r)   = Ctor r
  -- recoverTree (Ap l r) = ApNode l r
    -- case h of
    --   Opaque -> t
    --   Pu _ -> Pure
    --   Ct r -> Ctor r
    --   Ap l r -> ApNode (recoverTree h l) (recoverTree h r)
    --   Bi l r -> BindNode (recoverTree h l) (recoverTree h r)

  -- convertTree :: forall (e :: * -> *) j a b. e -> Tree j -> a -> b -> ETree b a
  convertTree h e Pure a b o = Pu a
  -- convertTree e (Ctor (ctor, _)) a b o =
  --   case ctor == e of
  --     True -> Ct (e b)
  --     False -> (Opaque o)
  -- convertTree e (ApNode l r) a b = Ap (convertTree e l a b) (convertTree e r a b) 
  -- convertTree e (BindNode l r) a b = Bi (convertTree e l a b) (convertTree e r a b) 
  |])


runTest :: MonadEff j w 
runTest m = _ m (convertTree runReader')
  -- where
  --   go :: MonadEff j w -> ConvertTree (Reader e) j a b c -> MonadEff 
  --   go (Val x) h = convertTree 

data A = A
data B = B

-- testTree :: forall (e :: * -> *) j w a b c. MonadEff j w -> Demote (ConvertTree  
-- testTree m = case m of
--   Val x -> Pu A
  -- Eff u q -> Ct B
  -- (:<*>) l r -> Ap (testTree l) (testTree r)
  -- (:>>=) l r -> Bi (testTree l) (error "Foo")

-- convertTree :: MonadEff j w -> (ETree (t -> w) w -> ETree a w) -> ETree a w
-- convertTree (Val x) h = h (Pu x) 
-- convertTree (Eff u q) h = h (Pu x) 
-- convertTree (Val x) = runReader' (Pu x)
-- convertTree (Val x) = 

-- runEffect :: (a -> MonadEff r w) -> (ETree (e -> w) w -> ETree e' w) -> MonadEff 
-- runEffect ret h m = loop m
--   where
--     loop (Val x) = ret x


