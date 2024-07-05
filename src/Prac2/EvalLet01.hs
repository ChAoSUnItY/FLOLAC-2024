import Prelude ()
import MiniPrelude

data Expr = Num Int | Neg Expr | Add Expr Expr
          | Div Expr Expr
          | Var Name | Let Name Expr Expr
  deriving Show

data Except err a = Return a | Throw err
  deriving Show

data Err = DivByZero | VarNotFound Name
  deriving Show

type Name = String

type Env = [(Name, Int)]

-- What if we define
-- type Env = Name -> Maybe Int

-- The function
--   lookup :: Eq a => a -> [(a, b)] -> Maybe b
-- is defined in GHC.List and imported here.

-- eval :: -- what's its type?
eval :: Expr -> ReEx Env Err Int
eval (Num n) = return n
eval (Neg e) = negate <$> eval e
eval (Add lhs rhs) = (+) <$> eval lhs <*> eval rhs
eval (Div lhs rhs) =
  case evalRhs of
    Just 0    -> Throw DivByZero
    otherwise -> return $ (div) <$> eval lhs <*> evaledRhs
  where evaledRhs = eval rhs


tstExpr00 :: Expr
tstExpr00 = Let "x" (Num 3)
             (Add (Add (Var "x") (Let "x" (Num 4) (Var "x")))
                  (Neg (Var "x")))
--

data ReEx env err a = RE (env -> Except err a)

type EvalMonad = ReEx Env Err

runReEx :: ReEx env err a -> env -> Except err a
runReEx (RE f) = f

instance Monad (ReEx env err) where
  return = RE $ Return $ const
  (RE f) >>= mx = RE $ mx f

instance MonadReader env (ReEx env err) where
  ask = return
  local = undefined

instance MonadExcept err (ReEx env err) where
  throw = undefined
  catchE = undefined

-- Functor and Applicative instances

instance Functor (ReEx env err) where
  fmap = liftM

instance Applicative (ReEx env err) where
  pure  = return
  (<*>) = ap
