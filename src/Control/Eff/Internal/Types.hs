{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE CPP                    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE UnboxedTuples          #-}

{-# LANGUAGE GADTs                  #-}

module Control.Eff.Internal.Types where

import Control.Lens.Lens
import Data.Kind         (Type)

type Handler = Type
type Effect  = Type

data EffTree a = Pure
              | Zero a
              | Do a
              | Fmapped (EffTree a)
              | EffTree a :<*> EffTree a
              | EffTree a :>>= EffQueue a
              | EffTree a :<|> EffTree a

data EffQueue a = TLeaf (EffTree a) | TNode (EffQueue a) (EffQueue a)

infixl 1 :>>=
infixl 4 :<*>

type family EffectResult effect :: Type

newtype Tagged (t :: Type) a = Tagged { untag :: a }

data DataType a = Nil
                | Getting a
                | Setting a
                | Mutating a

-- type family DefaultData l where
--     DefaultData 'Nothing  = ()
--     DefaultData ('Just s) = s

-- type family TaggedTuple l t d where
--     DefaultData 'Nothing  d = Tagged t d
--     DefaultData ('Just s) d = Tagged t d l

class HandlerBase handler where
    type family HandlerData handler :: DataType Type
    type instance HandlerData handler = Nil

    type HandlerOutput handler result :: Type
    type instance HandlerOutput handler result = result

    -- getLower :: HandlerData handler ('Just s) -> s
    -- default getLower :: (HandlerData handler ('Just s) ~ s) => s -> s
    -- getLower = id

    applyResult :: r -> (HandlerOutput handler) r
    default applyResult :: (HandlerOutput handler r ~ r) => r -> HandlerOutput handler r
    applyResult = id

type family HandlerLens s h where
    HandlerLens s  'Nothing  = s
    HandlerLens s ( 'Just t) = ALens' s t

class HandlerBase h => EffectHandler h e s where
    handle :: s -> e -> (EffectResult e, s)

#if __USE_UNBOXED_TUPLES__
    handle s ctor = case handle' @h @e @s s ctor of
        (# r, s' #) -> (r, s')

    handle' :: s -> e -> (# EffectResult e, s #)
    handle' s ctor = case handle @h @e @s s ctor of
        (r, s') -> (# r, s' #)

    -- {-# MINIMAL handle | handle' #-}
#endif
