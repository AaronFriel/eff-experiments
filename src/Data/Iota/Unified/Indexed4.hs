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
-- import Control.Monad.Cx.Rebound hiding ((<*>), (>>=))
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

-- type Arrs a b = forall i j. IxQueue (MonadEff j) a b

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

type family AddCtor ctor where
  AddCtor ctor = '[ 'Ctor ctor]

type family AddAp l r where
  AddAp l r = '[] :++ '[ 'Ap ] :++ Parenthesize l :++ Parenthesize r

type family AddBind l r where
  AddBind l r = '[] :++ '[ 'Bind ] :++ Parenthesize l :++ Parenthesize r

data MonadEff (j :: [SList (* -> *)]) (a :: *)
  where
    Pure    :: a -> MonadEff i a
    Eff     :: ctor a -> (a -> b) -> MonadEff (AddCtor ctor) b
    (:<*>)  :: MonadEff j (a -> b) -> MonadEff k a -> MonadEff (AddAp j k) b
    (:>>=)  :: MonadEff j a -> (a -> MonadEff k b) -> MonadEff (AddBind j k) b

-- (:>>=)  :: MonadEff i a -> (a -> MonadEff (Reader Int ': j) b) -> MonadEff (i :++ (Reader Int ': j)) b


-- instance CxPointed MonadEff
--   ipoint = Pure

-- instance CxFunctor MonadEff
--   imap f (Pure x) = Pure (f x)
--   imap f (Eff u q) = Eff u (f . q)
--   imap f (x :<*> y) = (imap (f .) x :<*> y)
--   imap f (x :>>= y) = (x :>>= \a -> imap f (y a))

pure = Pure
return = pure

fmap :: (a -> b) -> MonadEff i a -> MonadEff i b
fmap f (Pure x) = Pure (f x)
fmap f (Eff u q) = Eff u (f . q)
fmap f (x :<*> y) = (fmap (f .) x :<*> y)
fmap f (x :>>= y) = (x :>>= \a -> fmap f (y a))
join = (>>= id)

-- instance CxApplicative MonadEff
--   -- Pure f <|*|> Pure x  = Pure $ f x
n <*> m       = n :<*> m

-- instance CxMonad MonadEff
--   -- Pure x |>= k = k x
m      >>= k = m :>>= k

-- -- b -> MonadEff k c
-- test :: (b -> MonadEff k c) -> MonadEff k (b -> c)
-- test m = (:<*>) (Pure m) (Pure const)

data Reader e v where
    Reader :: Reader e e

data Writer o v where
    Writer :: o -> Writer o ()

data State s v where
    Put :: s -> State s ()
    Get :: State s s

data NamedState (k :: Symbol) s v where
    IxPut :: s -> NamedState k s ()
    IxGet :: NamedState k s s

send :: forall ctor v. ctor v -> MonadEff (AddCtor ctor) v
send t = Eff t id

ask :: forall e. MonadEff (AddCtor (Reader e)) e
ask = send Reader

-- tell :: forall o. MonadEff (AddCtor (Writer o)) ()
tell o = send (Writer o)

put :: forall s. s -> MonadEff (AddCtor (State s)) ()
put = send . Put

get :: forall s. MonadEff (AddCtor (State s)) s
get = send Get

seal :: MonadEff j a -> MonadEff j a
seal = id

-- -- Type is inferred!
-- t1 :: MonadEff '[Reader Float, Reader Int] Int
t1 = do
  a <- ask @Int
  return a

-- if you squint
-- it looks like:
-- (ap 
--   (ctor Reader Int)
--   (ctor Reader Int ctor Reader Int)
-- )
-- t2 :: MonadEff '[Ap , L , Ctor (Reader Int) , R , L , Ctor (Reader Int) , Ctor (Reader Int) , R] Int
t2 = seal $ do
  a <- t1
  a' <- t1
  return (a * a')

t3 :: MonadEff
       '[ 'Ap, 'L,
            'Ap,
               'L, 
                'Ctor (Reader Int),
              'R, 'L, 
                'Ctor (Reader Float),
              'R,
            'R, 'L,
              'Ctor (Reader Float),
          'R]
       Int
t3 = do
  a <- ask @Int
  a' <- ask @Float
  a'' <- ask @Float
  return (a * round a' + round a'')


simpTest :: MonadEff j Int -> MonadEff (Simplify j) Int
simpTest = undefined

runInt' :: MonadEff j Int -> MonadEff (RunEffect' j (Reader Int)) Int
runInt' = undefined

runFloat' :: MonadEff j Int -> MonadEff (RunEffect' j (Reader Float)) Int
runFloat' = undefined


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

-- runReader :: MonadEff j a -> e -> MonadEff (RunEffect j (Reader e)) a
-- runReader (Pure a) e = Pure a

-- class (Member j (Reader e)) ~ 'True => RunReader i j e where
--TODO: generalize to handleRelay like behavior

class RunReader j a e where
  runReader :: MonadEff j a -> e -> MonadEff (RunEffect j (Reader e)) a

instance RunReader '[ 'Ctor (Reader e) ] e e where
  runReader (Pure a) _ = Pure a
  runReader (Eff _ q) e = Pure (unsafeCoerce q $ e)

instance RunReader r a1 e => RunReader ( 'Ctor t : r ) a e where
  runReader (Pure a) _ = Pure a
  -- runReader (Eff u q) e = Eff u (flip runReader e . q)

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
--       (Pure f, Pure a) -> Pure (f a)

-- instance ( '(head, tail) ~ GetArgumentHead r,
--            RunReader '[] head a e,
--            RunReader '[] tail b e,
--            Simplify (RunEffect' tail (Reader e))
--                         ~
--                         SimplifyOp' 'Bind (GetArguments (RunEffect' r (Reader e)))
--          ) => RunReader '[] ( 'Bind : r ) b e where
--   runReader (m :>>= k) e =
--     case runReader (unsafeCoerce m :: MonadEff head a) e of
--       Pure a  -> flip runReader e $ (unsafeCoerce k :: a -> MonadEff tail b) a
--       -- Eff u q -> undefined



-- instance RunReader '[] '[ 'Ctor (Reader e) ] e e where
--   runReader (Eff _ q) e = Pure (unsafeCoerce q $ e)


-- This is safe!
run :: MonadEff '[] b -> b
run (Pure b) = b


infixl 7 :<*>
infixl 6 :>>=

apPrec, bindPrec :: Int
apPrec = 7
bindPrec = 6


instance Show (MonadEff j a) where
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

-- run :: MonadEff '[] a -> a
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