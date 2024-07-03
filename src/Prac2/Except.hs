import Prelude ()
import MiniPrelude hiding (catchE)

data Expr = Num Int | Add Expr Expr | Div Expr Expr
  deriving Show

data Except e a = Return a | Throw e
  deriving Show

catchE :: Except e a -> (e -> Except e a) -> Except e a
catchE (Throw e) f  = f e
catchE (Return a) _ = return a

data Err = DivByZero | Overflow | Underflow
 deriving Show

instance Monad (Except e) where
  return          = Return
  Return x  >>= f = f x
  Throw err >>= f = Throw err

eval :: Expr -> Except Err Int
eval e = catchE (eval' e) (\err -> 
    case err of
      DivByZero -> Throw err
      Overflow  -> return 32767
      Underflow -> return $ -32767
  )

eval' :: Expr -> Except Err Int
eval' (Num n)       = return n
eval' (Add lhs rhs) = (add) <$> (eval lhs) <*> (eval rhs) >>= id
eval' (Div lhs rhs) =
  case evaledRhs of
    Return 0  -> Throw DivByZero
    otherwise -> (div') <$> (eval lhs) <*> evaledRhs >>= id
  where evaledRhs = eval rhs
-- eval' = undefined -- use add and div' instead of (+) and div
                     -- call eval somewhere

tstExpr00, tstExpr01 :: Expr
tstExpr00 = (Num 65536 `Add` Num 32768) `Div`
                (Num 1 `Add` Num 65536)
tstExpr01 = (Num 32768 `Div` Num 0) `Add` Num 32768
  -- eval tstExpr00  ===> Return 1
  -- eval tstExpr01  ===> Throw DivByZero

-- "primitive" addition and division that raise
-- overflow and underflow errors.
-- add and div' are to be used in place of (+) and div.

overflow :: Int -> Bool
overflow n = n > 32767

underflow :: Int -> Bool
underflow n = n < -32768

flowcheck :: Int -> Except Err Int
flowcheck n | overflow n  = Throw Overflow
            | underflow n = Throw Underflow
            | otherwise   = return n

add :: Int -> Int -> Except Err Int
add x y = flowcheck (x + y)

div' :: Int -> Int -> Except Err Int
div' x y = flowcheck (x `div` y)

-- Functor and Applicative instances

instance Functor (Except e) where
  fmap = liftM

instance Applicative (Except e) where
  pure  = return
  (<*>) = ap
