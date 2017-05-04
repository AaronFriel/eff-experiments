{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE TypeApplications #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

-- Needed for poly-kinded "f :: k -> * -> *"
{-# LANGUAGE PolyKinds #-}

{-# LANGUAGE Strict #-}

module Control.Monad.Graph.Opt (t3) where

import Prelude hiding (
    -- Functor
    fmap, (<$), (<$>),
    -- Applicative
    pure, (<*>), (*>), (<*), 
    -- Monad
    return, (>>=), (=<<), (>>),

    fail
    )


import Control.Monad.Graph.Playground
import Control.Monad.Graph.Eff

fail s = error $ "Fail"

{-# INLINE t3 #-}
t3 = 
    let t3init = genTrace (genState @Int 42 $ genState @Float (0.1 + 0.2) $ genInit)
        t3alg  = Alg algTrace :&: (addAlgState @Int $ addAlgState @Float $ HNil) 
        z      = (42 :: Int)
    in run t3init t3alg $ do
        let do_once z = do
                x <- get @Int
                y <- get @Float
                _ <- trace ("x : " ++ show x)
                _ <- trace ("y : " ++ show y)
                _ <- put @Float (fromIntegral x * y + fromIntegral z)
                _ <- put @Int (x + round (log y) + z)
                return (x + round y + z)
            do_4 z = do_once z >>= do_once >>= do_once >>= do_once
            do_8 z = do_4 z >>= do_4
        z' <- do_8 z
        x <- get @Int
        y <- get @Float
        return (x, y)


