{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

{-# LANGUAGE StrictData #-}
{-# LANGUAGE QuasiQuotes #-}

module Indexed where

import Data.Iota.Unified.Indexed
-- import Data.Iota.Strict.OpenUnion51
import Control.Monad
import Language.Haskell.IndexedDo (ido)

iota k n = if k > n then mzero else return k `mplus` iota (k+1) n

-- pyth1 :: MonadPlus m => Int -> m (Int, Int, Int)
-- pyth1 upbound = do
--   x <- iota 1 upbound
--   y <- iota 1 upbound
--   z <- iota 1 upbound
--   if x*x + y*y == z*z then return (x,y,z) else mzero
--
-- pyth20 =
--   [(3,4,5),(4,3,5),(5,12,13),(6,8,10),(8,6,10),(8,15,17),(9,12,15),(12,5,13),
--    (12,9,15),(12,16,20),(15,8,17),(16,12,20)]
--
--
--
-- pythr_Iota n = ((run . makeChoiceA $ pyth1 n) :: [(Int,Int,Int)])

be_make_list :: Int -> [Int]
be_make_list n = replicate n 1 ++ [0]

benchCnt_Iota :: Int -> ((),Int)
benchCnt_Iota n = run $ runState m n
  where
  m = do
    x <- get
    if x > 0 then put (x-1::Int) >> m else return ()
--
-- benchMul_Iota :: Int -> Int
-- benchMul_Iota n = either id id . run . runError $ m
--   where
--     m = foldM f 1 (be_make_list n)
--     f acc 0 = throwError (0::Int)
--     f acc x = return $! acc * x
--
-- benchS_Eff :: (Member (State Integer) r) =>
--                 Integer -> Eff r Integer
-- benchS_Eff n = foldM f 1 [n, n-1 .. 0]
--  where
--  f acc x | x `mod` 5 == 0 = do
--                             s <- get
--                             put $! (s+1::Integer)
--                             return $! max acc x
--  f acc x = return $! max acc x
--
-- mainS_Eff n = run $ runState (benchS_Eff n) (0::Integer)
--
-- mainRS_Eff n = run $
--   flip runReader (0::Int) $
--    runState (benchS_Eff n) (0::Integer)
--
-- mainRRS_Eff n = run $
--   flip runReader (0::Int) $
--   flip runReader (0::Integer) $
--    runState (benchS_Eff n) (0::Integer)
--
-- mainRRRS_Eff n = run $
--   flip runReader (0::Int) $
--   flip runReader (0::Integer) $
--   flip runReader True $
--    runState (benchS_Eff n) (0::Integer)
--
-- mainRRRRS_Eff n = run $
--   flip runReader (0::Int) $
--   flip runReader (0::Integer) $
--   flip runReader True $
--   flip runReader "0" $
--    runState (benchS_Eff n) (0::Integer)
--
-- mainSR_Eff n = run $
--   flip runState (0::Integer) $
--   flip runReader (0::Int) $
--    benchS_Eff n
--
-- mainSRR_Eff n = run $
--   flip runState (0::Integer) $
--   flip runReader (0::Int) $
--   flip runReader (0::Integer) $
--    benchS_Eff n
--
-- mainSRRR_Eff n = run $
--   flip runState (0::Integer) $
--   flip runReader (0::Int) $
--   flip runReader (0::Integer) $
--   flip runReader True $
--    benchS_Eff n
--
-- mainSRRRR_Eff n = run $
--   flip runState (0::Integer) $
--   flip runReader (0::Int) $
--   flip runReader (0::Integer) $
--   flip runReader True $
--   flip runReader "0" $
--    benchS_Eff n
