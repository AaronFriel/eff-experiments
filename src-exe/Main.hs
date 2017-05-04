{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE TypeApplications #-}


{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}


-- Needed for poly-kinded "f :: k -> * -> *"
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}

{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE BangPatterns #-}

{-# LANGUAGE StrictData #-}

module Main where


import Prelude hiding (
    -- Functor
    fmap, (<$), (<$>),
    -- Applicative
    pure, (<*>), (*>), (<*), 
    -- Monad
    return, (>>=), (=<<), (>>),

    fail
    )
import qualified Prelude as Prelude

main = print 1

-- import Control.Monad.Graph.Playground
-- import Control.Monad.Graph.Class
-- import Control.Monad.Graph.Eff
-- import Data.IORef

-- count1 = do
--         !x <- get @Int
--         () <- put @Int (x + 1)
--         return ()


-- -- sndToLast :: [a] -> Maybe a
-- -- sndToLast []   = Nothing
-- -- sndToLast [x1] = Nothing
-- -- sndToLast (x1:x2:xs) = case xs of
-- --     [] -> Just x1
-- --     _  -> sndToLast (x2:xs) 

-- count10 =
--         count1 >> count1 >> count1 >> count1 >> count1
--             >> count1 >> count1 >> count1 >> count1 >> count1

-- count100 =
--         count10 >> count10 >> count10 >> count10 >> count10
--             >> count10 >> count10 >> count10 >> count10 >> count10
    

-- headVec :: HVect (t ': ts) -> t
-- headVec (a :&: _) = a

-- sndUnboxed :: (# a, b #) -> b
-- sndUnboxed (# a, b #) = b


-- -- main :: IO ()
-- -- main =
-- --     let r = run (genState @Int 42 $ genInit) count100
-- --     in case headVec (snd r) of
-- --         (Tagged ref) -> (Prelude.>>=) (readIORef ref) print
-- t3 (z :: Int) = do
--     let do_once z = 
--             do
--                 !x <- get @Int
--                 !y <- get @Float
--                 let y' = log (fromIntegral x * y + fromIntegral z)
--                     x' = x + round (log y)
--                 do
--                     _ <- trace ("x : " ++ show x)
--                     _ <- trace ("y : " ++ show y)
--                     _ <- put @Float y'
--                     _ <- put @Int x'
--                     return (x' + round y' + z)
--         do_4 z = do_once z >>= do_once >>= do_once >>= do_once
--         do_16 z = do_4 z >>= do_4 >>= do_4 >>= do_4
--         do_64 z = do_16 z >>= do_16 >>= do_16 >>= do_16
--     z' <- do_64 z
--     x <- get @Int
--     y <- get @Float
--     return (x, y, z')

-- main = let t3r = run (genTrace $ genState @Int 42 $ genState @Float (0.1 + 0.2) $ genInit) $ t3 42
--     in print $ snd t3r `seq` fst t3r
