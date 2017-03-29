{- This module provides type-level finite maps.
The implementation is similar to that shown in the paper.
 "Embedding effect systems in Haskell" Orchard, Petricek 2014  -}

{-# LANGUAGE TypeOperators, PolyKinds, DataKinds, KindSignatures,
             TypeFamilies, UndecidableInstances, MultiParamTypeClasses,
             FlexibleInstances, GADTs, FlexibleContexts, ScopedTypeVariables,
             ConstraintKinds #-}
{-# LANGUAGE TypeInType #-}

module Data.Type.Test.BiMap where

import Data.Type.BiMap

