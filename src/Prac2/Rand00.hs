import Prelude ()
import MiniPrelude

 --- X_{n+1} = (a * X_n + c) `mod` m
 ---   m -- the modulus
 ---   a -- the multiplier
 ---   c -- the increment

random :: MonadState Integer m => m Integer
random = return 0
  -- assuming that the state is X_n,
  -- compute X_{n+1} and update the state accordingly.

m, a, c :: Integer
m = 9
a = 4
c = 1

-- the function randoms n computes n pseudorandom numbers.
--  e.g.
-- > runState (randoms 10) 99
-- ([1,5,3,4,8,6,7,2,0,1],1)

randoms :: MonadState Integer m => Int -> m (List Integer)
randoms n = random 

---

data State s a = ST (s -> (a, s))

runState :: State s a -> s -> (a, s)
runState (ST f) = f

instance Monad (State s) where
  return a    = ST $ \s -> (a, s)
  ST mx >>= k = ST $ \_ -> 
    let (a, s') = k mx
    in (a, s')

instance MonadState s (State s) where
  get    = ST $ \s -> (s, s)
  put s' = ST $ \_ -> ((), s')

-- Functor and Applicative instances

instance Functor (State s) where
  fmap = liftM

instance Applicative (State s) where
  pure  = return
  (<*>) = ap
