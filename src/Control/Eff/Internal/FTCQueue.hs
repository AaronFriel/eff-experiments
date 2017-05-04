{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}

-- FViewL' terminates, but GHC can't prove that.
{-# LANGUAGE UndecidableInstances #-}

module Control.Eff.Internal.FTCQueue where

import Control.Eff.Internal.Types

import Data.Kind (Type)
import GHC.Types (SPEC (..))

-- type role FTCQueue representational phantom representational nominal
data FTCQueue m i a b where
        Leaf :: (a -> m i b) -> FTCQueue m ('TLeaf i) a b
        Node :: FTCQueue m i a x -> FTCQueue m j x b -> FTCQueue m ('TNode i j) a b

{-# INLINE tfmap #-}
tfmap :: (a -> m 'Pure b) -> FTCQueue m ('TLeaf 'Pure) a b
tfmap r = Leaf r

{-# INLINE tsingleton #-}
tsingleton :: (a -> m i b) -> FTCQueue m ('TLeaf i) a b
tsingleton r = Leaf r

-- snoc: clearly constant-time
{-# INLINE (|>) #-}
(|>) :: FTCQueue m i a x -> (x -> m j b) -> FTCQueue m ('TNode i ('TLeaf j)) a b
t |> r = Node t (Leaf r)

-- append: clearly constant-time
{-# INLINE (><) #-}
(><) :: FTCQueue m i a x -> FTCQueue m j x b -> FTCQueue m ('TNode i j) a b
t1 >< t2 = Node t1 t2

data ViewL m i a b where
    TOne :: (a -> m i b) -> ViewL m i a b
    (:<) :: (a -> m i x) -> (FTCQueue m j x b) -> ViewL m (i ':>>= j) a b

type family FViewL' i j where
    FViewL' ('TLeaf r)       tr = r ':>>= tr
    FViewL' ('TNode tl1 tl2) tr = FViewL' tl1 ('TNode tl2 tr)

type family FViewL i where
    FViewL ('TLeaf r)       = r
    FViewL ('TNode tl1 tl2) = FViewL' tl1 tl2

{-# INLINE tviewl #-}
tviewl :: FTCQueue m i a b -> ViewL m (FViewL i) a b
tviewl (Leaf r) = TOne r
tviewl (Node t1 t2) = go SPEC t1 t2
    where
      {-# INLINE go #-}
      go :: SPEC -> FTCQueue m i a x -> FTCQueue m j x b -> ViewL m (FViewL' i j) a b
      go !sPEC (Leaf r) tr       = r :< tr
      go !sPEC (Node tl1 tl2) tr = go sPEC tl1 (Node tl2 tr)
