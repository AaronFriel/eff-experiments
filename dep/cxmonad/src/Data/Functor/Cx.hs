-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Cx
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

module Data.Functor.Cx
  ( CxFunctor(..)
  , CxPointed(..)
  , CxApplicative(..)
  ) where

import Data.Singletons.Prelude

infixl 4 <|$

infixl 4 <|*|>

class CxFunctor f where
  imap :: (a -> b) -> f j k a -> f j k b

  (<|$) :: b -> f j k a -> f j k b
  (<|$) = imap . const

  {-# MINIMAL (imap) #-}
  
class CxPointed f => CxApplicative f where
  ipure :: a -> f i i a
  ipure = ipoint 

  (<|*|>) :: f i j (a -> b) -> f j k a -> f i k b

  {-# MINIMAL (<|*|>) #-}

class CxFunctor f => CxPointed f where
  ipoint :: a -> f i i a
