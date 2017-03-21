-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Cx.Rebound
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

module Data.Functor.Cx.Rebound
  ( CxFunctor(..)
  , CxPointed(..)
  , CxApplicative(..)
  , fmap, (<$)
  , pure, (<*>)
  , point
  ) where

import Data.Functor.Cx
import Data.Singletons.Prelude

fmap :: CxFunctor f => (a -> b) -> f j k a -> f j k b
fmap = imap

(<$) :: CxFunctor f => b -> f j k a -> f j k b
(<$) = (<|$)

pure :: CxApplicative f => a -> f i i a
pure = ipure

(<*>) :: CxApplicative f => f i j (a -> b) -> f j k a -> f i k b
(<*>) = (<|*|>)

point :: CxPointed f => a -> f i i a
point = ipoint
