{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds, PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}

{-# LANGUAGE TypeApplications #-}

-- Needed for NdetEff
{-# LANGUAGE UndecidableInstances #-}

-- {-# LANGUAGE TypeFamilies #-}
-- {-# LANGUAGE InstanceSigs #-}
-- {-# LANGUAGE OverlappingInstances #-}
-- {-# LANGUAGE ConstraintKinds #-}
-- {-# LANGUAGE AllowAmbiguousTypes #-}

{-# LANGUAGE Strict #-}

{-# OPTIONS_GHC -Wno-redundant-constraints #-}
-- The framework of extensible effects

module Data.Iota.Unified.Eff1 where

import Data.Iota.Unified.OpenUnion51
import Data.Iota.Unified.FTCQueue1

import GHC.Exts (inline)
import GHC.TypeLits (type (-))
import GHC.TypeLits.Witnesses
import Data.Proxy

import Control.Monad
import Control.Applicative
import Data.Singletons.TypeLits
