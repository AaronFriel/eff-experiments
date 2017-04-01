{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

{-# LANGUAGE StrictData #-}
{-# LANGUAGE QuasiQuotes #-}

module Indexed where

import Data.Iota.Unified.Indexed5

-- This is the control flow graph, with nodes indexed by type-level natural numbers.
-- This graph forms a cycle with one node.
type TestMap = '[ '(1, Ctor Trace :>>= 1) ]
-- TestMap is a type of kind [(GHC.Types.Nat, Tree (* -> *))]

-- Increment over a "Trace" effect, emitting it, and iterating.
{-# INLINE stepTrace #-}
stepTrace :: MonadEff ('Universe TestMap r) (Ctor Trace :>>= 1)      a 
          -> MonadEff ('Universe TestMap r) (LookupIndex' 1 TestMap) a
stepTrace ((Eff u q) `Bind` k) = case u of
  Trace t -> unsafeCoerce $ k (q ())

-- Uses a Trace effect and a recursive let binding for an infinite loop.
infiniteTraceLoop :: MonadEff ('Universe TestMap r) (LookupIndex' 1 TestMap) Int
infiniteTraceLoop = 
  let t (n :: Int) = Eff (Trace $ show n) (const $ n + 1) `Bind` t in t 0

{-# INLINE loop #-}
loop :: MonadEff ('Universe TestMap r) ('Ctor Trace ':>>= 1) a -> IO Void
loop m = do
  case stepTrace m of
    m' -> loop (stepTrace m')

-- Runs forever, loops over "Int" domain [0, 1, ..., maxBound, minBound, ... -1]
testLoop = loop infiniteTraceLoop


benchCnt_Ix :: Int -> ((),Int)
benchCnt_Ix n = 
  let loop m 0 = return ()
      loop m n = do
        case stepTrace m of
          m' -> loop (stepTrace m')
          
-- run $ runState m n
--   where
--   m = do
--     x <- get
--     if x > 0 then put (x-1::Int) >> m else return ()
