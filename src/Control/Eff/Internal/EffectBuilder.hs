{- |
Module      :  Control.Eff.Internal.EffectBuilder
Description :  Build effects with class.
Copyright   :  (c) Aaron Friel
License     :  BSD-3

Maintainer  :  Aaron Friel <mayreply@aaronfriel.com>
Stability   :  unstable
Portability :  portable
-}

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeInType       #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE UndecidableInstances    #-}

module Control.Eff.Internal.EffectBuilder where

import Control.Eff.Internal.Types

import Data.Kind (Type)
{-

Problem: An effect can do several things:

1. Mutate the output in some manner (e.g.: for Reader e, `a -> ([o], a)`)
2. Demand some state that it wishes to mutate (e.g.: for Reader e: an `e`).
3. Interact with the or (`<|>`) and plus (`<+>`) operators to make *choices*.

But all of the above are _optional_, which is frustrating, examples:

1. Reader does not mutate output.
2. IO does not require state.
3. Writer does not define choice.

-}

class Effectful e where
    type family Output e a :: Type
    type instance Output e a = a

    type family Data e :: [Type]
    type instance Data e = '[]

    type family MakesChoice e :: Bool
    type instance MakesChoice e = 'False

newtype Writer o = Tell o

data Reader (e :: Type) = Ask

data State s = Put s | Get

data Trace e = Trace String

data SumOfChoice = SumOfChoice

instance Effectful (Writer o) where
    type Output (Writer o) a = (a, [o])
    type Data (Writer o) = '[ [o] ]

instance Effectful (Reader e) where
    type Output (Reader e) a = a
    type Data (Reader e) = '[e]

instance Effectful (State s) where
    type Output (State s) a = (a, s)
    type Data (State s) = '[s]

instance Effectful e => Effectful (Trace e) where
    type Output (Trace e) a = Output e a
    type Data   (Trace e)   = Data e
    type MakesChoice (Trace e)   = MakesChoice e

instance Effectful SumOfChoice where
    type Output SumOfChoice a = [a]
    type MakesChoice SumOfChoice = 'True

type family a :|| b where
    'True :|| _     = 'True
    _     :|| 'True = 'True
    _     :|| _     = 'False

type family a :++ b where
    (:++)      '[]  ys = ys
    (:++) (x ': xs) ys = x ': (xs :++ ys)

type family Outputs es a where
    Outputs       '[] a = a
    Outputs (e ': es) a = Output e (Outputs es a)

type family TagAll e ts :: [Type] where
    TagAll e      '[]  = '[]
    TagAll e (t ': ts) = Tagged e t ': TagAll e ts

type family TaggedData es :: [Type] where
    TaggedData       '[] = '[]
    TaggedData (e ': es) = TagAll e (Data e) :++ (TaggedData es)

instance Effectful es => Effectful (e ': es :: [Type]) where
    type Output (e ': es) a    = Outputs (e ': es) a
    type Data (e ': es)        = TaggedData (e ': es)
    type MakesChoice (e ': es) = MakesChoice e :|| MakesChoice es


type family Reverse' xs a where
    Reverse'      '[]  a = a
    Reverse' (x ': xs) a = Reverse' xs (x ': a)

type family Reverse xs where
    Reverse xs = Reverse' xs '[]

-- Hypothetical list of effects:
type E1 = '[Writer [String], State Int, Trace (State Bool), State Double, Writer Int, SumOfChoice]

-- Results:
-- :kind! forall a. Output E1 a = ((((([a], [Int]), Double), Bool), Int), [[String]])
--                                     | |  |       |        |      |     \- Writer [String]
--                                     |/   |       |        |      \- State Int
--                                     |    |       |        \- Trace (State Bool)
--                                     |    |       \- State Double       
--                                     |    \- Writer Int
--                                     \- Sum of choice
-- :kind!             Data E1   = '[Tagged (Writer [String]) [[String]], Tagged (State Int) Int,
--                                  Tagged (Trace (State Bool)) Bool, Tagged (State Double) Double,
--                                  Tagged (Writer Int) [Int]]
-- :kind!      MakesChoice E1   = 'True

--                                                            SumOfChoice
--                                         _______________________||_______________________
--                                        /                                                 \
-- :kind! forall a. Output (Reverse E1) = [(((((a, [[String]]), Int), Bool), Double), [Int])]
--                                              |  |            |     |      |        |     
--                                              |  |            |     |      |        \- Writer Int
--                                              |  |            |     |      \- State Double
--                                              |  |            |     \- Trace (State Bool)
--                                              |  |            \- State Int
--                                              |  \- Writer [String]
--                                              \- a
-- :kind!             Data (Reverse E1) = '[Tagged (Writer Int) [Int], Tagged (State Double) Double,
--                                          Tagged (Trace (State Bool)) Bool, Tagged (State Int) Int,
--                                          Tagged (Writer [String]) [[String]]]
-- :kind!      MakesChoice (Reverse E1) = 'True
--
-- Neat.