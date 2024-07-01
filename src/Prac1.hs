module Prac1 where

-- A practive on curried functions

-- (a) Define a function poly that poly a b c x = a * x ^ 2 + b * x + c. All the inputs and the
--     result are of type Float.

poly :: Float -> Float -> Float -> Float -> Float
poly a b c x = a * (x ** 2) + b * x + c

-- (b) Reuse poly to define a function poly1 such that poly1 x = x ^ 2 + 2 * x + 1 .

--  Note: Performing eta-reduction
poly1 :: Float -> Float
poly1 = poly 1 2 1

-- (c) Reuse poly to define a function poly2 such that poly2 a b c = a * 2 ^ 2 + b * x + c.

poly2 :: Float -> Float -> Float -> Float
poly2 a b c = poly a b c 2

-- Type in the definition of square in your working file.

-- (a) Define a function quad :: Int -> Int such that quad x computes x ^ 4

-- Note: Performing eta-reduction
quad :: Int -> Int
quad = (^) 4

-- (b) Type in this definition into your working file. Describe, in words, what this function 
--     does.

twice :: (a -> a) -> (a -> a)
twice f x = f (f x)

-- (c) Define quad using twice.

quad1 :: Int -> Int
quad1 = twice ((^) 2)

-- Replace the previous twice with this definition:
-- twice :: (a -> a) -> (a -> a)
-- twice f = f . f

twice1 :: (a -> a) -> (a -> a)
twice1 f = f . f

quad2 :: Int -> Int
quad2 = twice1 ((^) 2)

-- (a) Does quad still behave the same?
--     A: Yes.

-- (b) Explain in words what this operator (.) does.
--     A: operator (.) is similar to function composition in math, which is defined as f . f = f (f x)

-- Functions as arguments, and a quick practice on sectioning.

-- (a) Type in the following definition to your working file, without giving the type.
--     
--     forktimes f g x = f x * g x
--
--     Use :t in GHCi to find out the type of forktimes. You will end up getting a complex type 
--     which, for now, can be seen as equivalent to
--    
--     (t -> Int) -> (t -> Int) -> t -> Int
--
--     Can you explain this type?
--
--     A: forktimes is a function that accepts 2 function which accepts anytype named t and returns 
--        an Int, also accept another parameter with anytype also named t, then eventually returns
--        Int.

forktimes :: (t -> Int) -> (t -> Int) -> t -> Int
forktimes f g x = f x * g x

-- (b) Define a function that, given input x, use forktimes to compute x ^ 2 + 3 * x + 2. Hint:
--     x ^ 2 + 3 * x + 2 = (x + 1)* (x + 2)

-- Note: Performing eta-reduction
computation :: Int -> Int
computation = forktimes (+ 1) (+ 2)

-- (c) Type in the following definition into your work file: lift2 h f g x = h (f x) (g x). Find
--     out the type of lift2. Can you explain its type?
--     A: lift2 is a function that takes 3 functions that returns types differently from each other,
--        the first function type takes 2 parameters, which whose type is inferred from later parameters'
--        return types, later takes 2 previously mentioned functions then take 1 type inferred from
--        previously 2 functions' only parameter's type. Finally returns the result returned from first
--        function type.

lift2 :: (t1 -> t2 -> t3) -> (t4 -> t1) -> (t4 -> t2) -> t4 -> t3
lift2 h f g x = h (f x) (g x)

-- (d) Use lift2 to compute x ^ 2 + 3 * x + 2

computation1 :: Int -> Int
computation1 = lift2 (*) (+ 1) (+ 2)
