-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Cx.Rebound
-- Copyright   :  (C) 2017 Aaron Friel
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Aaron Friel <mayreply@aaronfriel.com>
-- Stability   :  experimental
-- Portability :  portable
--
----------------------------------------------------------------------------
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

module Control.Monad.Cx.Rebound
  ( module Control.Monad.Cx
  , module Data.Functor.Cx.Rebound
  , return, (>>=), (=<<), (>>), join
  ) where

import Control.Monad.Cx
import Data.Functor.Cx.Rebound
import Data.Singletons.Prelude

return :: CxMonad m => a -> m i i a
return = ireturn

(>>=) :: CxMonad m => m i j a -> (a -> m j k b) -> m i k b
(>>=) = (|>=)

(=<<) :: CxMonad m => (a -> m j k b) -> m i j a -> m i k b
(=<<) = (=<|)

(>>) :: CxMonad m => m i j a -> m j k b -> m i k b
(>>) = (|>)

join :: CxMonad m => m i j (m j k a) -> m i k a
join = ijoin