{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

-- {-# LANGUAGE StrictData #-}

module Iota where

import Data.Iota.Eff1
import Data.Iota.OpenUnion51
import Control.Monad

-- benchS_MTL re-written for the Eff monad
benchS_Eff :: (Member (State Integer) r) =>
                Integer -> Eff r Integer
benchS_Eff n = foldM f 1 [n, n-1 .. 0]
 where
 f acc x | x `mod` 5 == 0 = do
                            s <- get
                            put $! (s+1::Integer)
                            return $! max acc x
 f acc x = return $! max acc x

mainS_Eff n = run $ runState (benchS_Eff n) (0::Integer)

mainRS_Eff n = run $
  flip runReader (0::Int) $
   runState (benchS_Eff n) (0::Integer)

mainRRS_Eff n = run $
  flip runReader (0::Int) $
  flip runReader (0::Integer) $
   runState (benchS_Eff n) (0::Integer)

mainRRRS_Eff n = run $
  flip runReader (0::Int) $
  flip runReader (0::Integer) $
  flip runReader True $
   runState (benchS_Eff n) (0::Integer)

mainRRRRS_Eff n = run $
  flip runReader (0::Int) $
  flip runReader (0::Integer) $
  flip runReader True $
  flip runReader "0" $
   runState (benchS_Eff n) (0::Integer)

mainSR_Eff n = run $
  flip runState (0::Integer) $
  flip runReader (0::Int) $
   benchS_Eff n

mainSRR_Eff n = run $
  flip runState (0::Integer) $
  flip runReader (0::Int) $
  flip runReader (0::Integer) $
   benchS_Eff n

mainSRRR_Eff n = run $
  flip runState (0::Integer) $
  flip runReader (0::Int) $
  flip runReader (0::Integer) $
  flip runReader True $
   benchS_Eff n

mainSRRRR_Eff n = run $
  flip runState (0::Integer) $
  flip runReader (0::Int) $
  flip runReader (0::Integer) $
  flip runReader True $
  flip runReader "0" $
   benchS_Eff n
