{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- For unsafeSizeof
{-# LANGUAGE MagicHash, UnboxedTuples #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}  

{-# OPTIONS_GHC -funbox-strict-fields #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors -Wno-missing-signatures -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Ddump-splices #-}


module Control.Monad.Graph
 -- ( Eff )
 where


import Data.Promotion.Prelude

import Data.Singletons
import Data.Singletons.Decide
import Data.Singletons.Prelude
import Data.Singletons.TH
import Data.Singletons.TypeLits
import Data.Type.Equality

import Data.Kind (Constraint, type (*))
import Data.Proxy (Proxy)
import GHC.TypeLits hiding (type (*))
import GHC.Prim (Proxy#, proxy#)
import           Unsafe.Coerce               (unsafeCoerce)

$(promote [d|
  data Path a = Pure | a :>>= (Path a) | Goto Nat -- | a :<*> b
    deriving (Eq)

  
  data Graph v = Graph {
      ixpaths      :: [(Nat, Path v)],
      effects      :: [v],
      current      :: (Nat, Path v)
    }
  
  emptyU = Graph [] []
  |])

type Effect  = (* -> *)
type EffectGraph = Graph Effect

$(promoteOnly [d|
  lookupIndex :: Nat -> Graph v -> Path v  
  lookupIndex k u = lookupIndex' k (treeMap u)

  lookupIndex'                    :: (Eq a) => a -> [(a, b)] -> b
  lookupIndex'    key ((x,y):xys) = if key == x then y else lookupIndex' key xys

  lookupValue :: Eq v => Path v -> Graph v -> Nat  
  lookupValue k u = lookupValue' k (treeMap u)

  lookupValue'                    :: (Eq b) => b -> [(a,b)] -> a
  lookupValue'  value ((x,y):xys) = if value == y then x else lookupValue' value xys
  |])


data Eff k (u :: Graph k) (v :: Graph k) b
  where
    V :: b -> MonadEff u v b
    E :: ctor a
      ->     (a -> MonadEff u v b)
      ->           MonadEff u v b
