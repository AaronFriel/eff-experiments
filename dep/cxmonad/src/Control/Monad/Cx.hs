-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Cx
-- Copyright   :  (C) 2017 Aaron Friel
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Aaron Friel <mayreply@aaronfriel.com>
-- Stability   :  experimental
-- Portability :  portable
--
----------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeInType #-}

module Control.Monad.Cx
  ( module Data.Functor.Cx
  , CxMonad(..)
  , (=<|), ijoin
  ) where

import Prelude (id)

import Data.Functor.Cx
import Data.Singletons.Prelude

infixl 1 |>, |>=
infixr 1 =<|

class CxApplicative m => CxMonad m where
  ireturn :: a -> m i i a
  ireturn a = ipure a

  (|>=)  :: m i j a -> (a -> m j k b) -> m i k b

  (|>)   :: m i j a -> m j k b -> m i k b
  m |> k = m |>= \_ -> k
  
  {-# MINIMAL (|>=) #-}

(=<|) :: CxMonad m => (a -> m j k b) -> m i j a -> m i k b
m =<| k = k |>= m

ijoin :: CxMonad m => m i j (m j k a) -> m i k a
ijoin = (|>= id)
