-- Regular style monads encode all of the behavior in their actions and
-- the definitions of the Monad bind operator (>>=), and other operators.

--         /- Type of the state (used with get/put)
--         |    /- Return value of the computation
f :: State Int ()
f = do
    x <- get
    put (x * x)
    return ()

-- Here's the trick: "State" is actually just a function, wrapped up in a data type.
data State s a = State (s -> (a, s))
--                      ^ the hidden state parameter

-- Get returns the state parameter on both sides:
get :: State s s
get = State (\s -> (s, s))

-- Put replaces the state parameter with a new one, and ignores the old
put :: s -> State s ()
put new = State (\s -> ((), new))

-- Here's what runState looks like:
runState (State m) s = m s
-- it doesn't do hardly anything!

-- Here's where the magic happens:
instance Monad (State s) where
  return a = State (\s -> (a, s))
  (State m) >>= k = State (\s -> 
                    -- Apply s to the left hand side:
                    case m s of 
                        -- Then, using the output, apply it to the right hand side:
                        (a, s') -> case (k a) of
                            (State f) -> f s'
                            -- ^ but since "m a" is a "State (\s ..."
                            -- give it the new state 
                        )

instance Applicative (State s) where
    pure a = State (\s -> (a, s))
    (State f) <*> (State m) = State (\s -> case f s of
                                        (f', s') -> case (m s') of
                                            (a, s'') ->
                                                (f' a, s''))

instance Functor (State s) where
    fmap f (State m) = State (\s -> case m s of
                                (a, s') -> (f a, s'))