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
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ApplicativeDo #-}

module Data.Iota.Unified.Indexed4
 -- ( Eff )
 where

import Prelude hiding (return, (>>), (<*>), (>>=), fmap, pure)
import Control.Monad.Cx.Rebound hiding ((<*>), (>>=))
-- import           Control.Monad.Indexed hiding ((>>>=), (=<<<), iap, IxApplicative (..), IxMonad (..))
-- import Language.Haskell.IndexedDo (ido)
-- import           Data.Proxy
-- import           Data.Singletons
-- import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding (SList)
import           Data.Singletons.Prelude.Enum
-- import           Data.Singletons.Prelude.List
import           Data.Singletons.Prelude.Num
-- import           Data.Singletons.Prelude.Ord
-- import           Data.Type.Equality
-- import           Data.Type.Map               hiding (Map)
-- import           Data.Type.Set               hiding ((:++))
import qualified Debug.Trace                 as Debug
-- import           GHC.Exts                    (inline)
-- import           GHC.Prim                    (Any, Proxy#, proxy#)
import           GHC.TypeLits                hiding (type (*))
import           Unsafe.Coerce               (unsafeCoerce)
-- import Data.Singletons.Prelude.Num
-- import Data.Singletons.Prelude.Enum
-- import           Control.Applicative
-- import           Control.Monad
import           Data.Kind
-- import           Data.Singletons.TypeLits

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

type Arrs a b = forall i j. IxQueue (MonadEff i j) a b

data a :<*>: b = a :<*>: b
data a :>>=: b = a :>>=: b

data SList a where
   Nil :: SList a
   L :: SList a
   R :: SList a
   Ctor :: a -> SList a
   Ap   :: SList a
   Bind :: SList a

type family Parenthesize a where
  Parenthesize '[] = '[ 'Nil ]
  Parenthesize   a = '[ 'L ] :++ a :++ '[ 'R ]

type family AddCtor' i ctor where
  AddCtor' i ctor = i :++ '[ 'Ctor ctor]

type family AddAp i l r where
  AddAp i l r = i :++ '[ 'Ap ] :++ Parenthesize l :++ Parenthesize r

type family AddBind i l r where
  AddBind i l r = i :++ '[ 'Bind ] :++ Parenthesize l :++ Parenthesize r

type family AddCtor i ctor where
  AddCtor i ctor = i :++ '[ctor]

data MonadEff (i :: [SList (* -> *)]) (j :: [SList (* -> *)]) (a :: *)
  where
    Pure    :: a -> MonadEff i i a
    Eff     :: ctor a -> (a -> b) -> MonadEff i (AddCtor' i ctor) b
    (:<*>)  :: MonadEff i j (a -> b) -> MonadEff j k a -> MonadEff i (AddAp i j k) b
    (:>>=)  :: MonadEff i j a -> (a -> MonadEff j k b) -> MonadEff i (AddBind i j k) b

-- (:>>=)  :: MonadEff i i a -> (a -> MonadEff j (Reader Int ': j) b) -> MonadEff i (i :++ (Reader Int ': j)) b


instance CxPointed MonadEff where
  ipoint = Pure

instance CxFunctor MonadEff where
  imap f (Pure x) = Pure (f x)
  imap f (Eff u q) = Eff u (f . q)
  imap f (x :<*> y) = (imap (f .) x :<*> y)
  imap f (x :>>= y) = (x :>>= \a -> imap f (y a))

-- instance CxApplicative MonadEff where
--   -- Pure f <|*|> Pure x  = Pure $ f x
n <*> m       = n :<*> m

-- instance CxMonad MonadEff where
--   -- Pure x |>= k = k x
m      >>= k = m :>>= k

-- -- b -> MonadEff j k c
-- test :: (b -> MonadEff j k c) -> MonadEff j k (b -> c)
-- test m = (:<*>) (Pure m) (Pure const)

data Reader e v where
    Reader :: Reader e e

data Writer o v where
    Writer :: o -> Writer o ()

send :: forall ctor v i. ctor v -> MonadEff i (AddCtor' i ctor) v
send t = Eff t id

ask :: forall e i. MonadEff i (AddCtor' i (Reader e)) e
ask = send Reader

-- tell :: forall o i. MonadEff i (AddCtor' i (Writer o)) ()
tell o = send (Writer o)

seal :: MonadEff '[] j a -> MonadEff '[] j a
seal = id

-- -- Type is inferred!
-- t1 :: MonadEff '[] '[Reader Float, Reader Int] Int
t1 = do
  a <- ask @Int
  return a

t2 = do
  a <- t1
  a' <- t1
  return (a * a')

t3 = do
  a <- ask @Int
  a' <- ask @Float
  a'' <- ask @Float
  return (a * round a' + round a'')

runTest :: MonadEff '[] i Int -> MonadEff '[] i Int
runTest = undefined

runTest' :: MonadEff '[] i Int -> MonadEff '[] (Simplify (RunEffect' i (Reader Int))) Int
runTest' = undefined

type family Member i (ctor :: * -> *) :: Bool where
  Member '[] ctor        = TypeError ('Text "The effect " ':<>: 'ShowType ctor ':<>: 'Text " is not used.")
  Member ('Ctor t : r) t = 'True
  Member ('Ctor u : r) t = Member r t

type family GetExpr'' (n :: Nat) h i where
  GetExpr'' 0 h r = '(h, r)
  GetExpr'' n h ('L : r) = GetExpr'' (n+1) (h :++ '[ 'L ]) r
  GetExpr'' n h ('R : r) = GetExpr'' (n-1) (h :++ '[ 'R ]) r
  GetExpr'' n h ( a : r) = GetExpr'' n     (h :++ '[  a ]) r
  GetExpr'' n h      '[] = TypeError ('Text "Invalid SList.")

type family GetSecondArgument i where
  GetSecondArgument '(fst, 'Nil : r) = '(fst, '( '[ 'Nil ], r ) )
  GetSecondArgument '(fst,   'L : r) = '(fst, GetExpr'' 1 '[ L ] r)

type family GetArguments i where
  GetArguments ('Nil : r) = GetSecondArgument '( '[ 'Nil ], r)
  GetArguments ('L   : r) = GetSecondArgument  (GetExpr'' 1 '[ 'L ] r) 

type family SimplifyOp' op i where
  SimplifyOp' op '( '[ 'L, 'R ], '(         snd, tail)) = SimplifyOp' op '( '[ 'Nil ], '(snd, tail) )
  SimplifyOp' op '(         fst, '( '[ 'L, 'R ], tail)) = SimplifyOp' op '( fst, '( '[ 'Nil ], tail) )
  SimplifyOp' op '(   '[ 'Nil ], '(   '[ 'Nil ], tail)) = Simplify tail
  SimplifyOp' op '(         fst, '         (snd, tail)) = op : Simplify fst :++ Simplify snd :++ Simplify tail

type family SimplifyOp op i where
  SimplifyOp op i = SimplifyOp' op (GetArguments i)

type family Simplify a where
  Simplify          '[]  = '[]
  Simplify (  'Ap  : r)  = SimplifyOp 'Ap r
  Simplify ('Bind  : r)  = SimplifyOp 'Bind r
  Simplify (  'Nil : r ) = Simplify r
  Simplify (    a : r )   = a : Simplify r

type family RunEffect' i (ctor :: * -> *) where
  RunEffect' '[]            ctor = '[]
  RunEffect' ('Ctor t : r )    t = RunEffect' r t
  RunEffect' (      a : r )    t = a : RunEffect' r t

type family RunEffect i (ctor :: * -> *) where
  RunEffect i ctor = Simplify (RunEffect' i ctor)

type family GetArgumentTypes' i where
  GetArgumentTypes' '(fst, '(snd, _)) = '(fst, snd)

type family GetArgumentHead i where
  GetArgumentHead ('Nil : r) = '( '[ 'Nil ], r)
  GetArgumentHead ('L   : r) = (GetExpr'' 1 '[ 'L ] r)

-- runReader :: MonadEff i j a -> e -> MonadEff i (RunEffect j (Reader e)) a
-- runReader (Pure a) e = Pure a

-- class (Member j (Reader e)) ~ 'True => RunReader i j e where
--TODO: generalize to handleRelay like behavior

class RunReader i j a e where
  runReader :: MonadEff i j a -> e -> MonadEff i (RunEffect j (Reader e)) a

instance RunReader '[] '[ 'Ctor (Reader e) ] e e where
  runReader (Eff _ q) e = Pure (unsafeCoerce q $ e)

-- instance ( '(head, tail) ~ GetArgumentHead r, 
--            RunReader '[] head (a -> b) e,
--            RunReader '[] tail a e,
--            Simplify (RunEffect' tail (Reader e))
--                         ~
--                         SimplifyOp' 'Bind (GetArguments (RunEffect' r (Reader e)))
--          ) => RunReader '[] ( 'Ap : r ) b e where
--   runReader (m :<*> k) e =
--     let m' = unsafeCoerce m :: MonadEff '[] head (a -> b)
--         k' = unsafeCoerce k :: MonadEff '[] tail a
--     in case (runReader m' e, runReader k' e) of
--       (Pure f, Pure a) -> Pure (f a)

-- instance ( '(head, tail) ~ GetArgumentHead r, 
--            RunReader '[] head a e,
--            RunReader '[] tail b e,
--            Simplify (RunEffect' tail (Reader e))
--                         ~
--                         SimplifyOp' 'Bind (GetArguments (RunEffect' r (Reader e)))
--          ) => RunReader '[] ( 'Bind : r ) b e where
--   runReader (m :>>= k) e =
--     case runReader (unsafeCoerce m :: MonadEff '[] head a) e of
--       Pure a  -> flip runReader e $ (unsafeCoerce k :: a -> MonadEff '[] tail b) a
--       -- Eff u q -> undefined
 

 
-- instance RunReader '[] '[ 'Ctor (Reader e) ] e e where
--   runReader (Eff _ q) e = Pure (unsafeCoerce q $ e)


-- This is safe!
run :: MonadEff '[] '[] b -> b
run (Pure b) = b


infixl 7 :<*> 
infixl 6 :>>=

apPrec, bindPrec :: Int
apPrec = 7
bindPrec = 6


instance Show (MonadEff i j a) where
  showsPrec _ (Pure _)  = showString "Pure"
  showsPrec _ (Eff _ _) = showString "Eff"
  showsPrec p (a :<*> b) = 
    showParen (p > apPrec) $ 
      showsPrec (apPrec+1) a
      . showString " :<*> "
      . showsPrec (apPrec+1) b

  showsPrec p (a :>>= _) = 
    showParen (p > bindPrec) $ 
      showsPrec (bindPrec+1) a
      . showString " :>>= "
      . showsPrec (bindPrec+1) "m"

  show t = showsPrec 0 t ""


-- runReader (Pure m :>>= k) e = (unsafeCoerce m)
-- runReader (Pure x) e = Pure x
  -- where
  --   loop (Pure x) = Pure x
  --   loop (Eff u q) = loop $ (unsafeCoerce q) e
    -- loop (a :<*> b) = undefined
    -- loop (a :>>= b) = undefined
-- t1 = seal [ido|do
--   a :: Float <- ask
--   b :: Int <- ask
--   ireturn (round a + b)
-- |]

-- run :: MonadEff '[] '[] a -> a
-- run (Pure b) = b
-- run (Eff u q) = error "Impossible"
-- t1r x = case t1 of 
--   Pure k -> k
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