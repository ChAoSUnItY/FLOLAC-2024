-- NOTICE: THIS FILE IS NOT MEANT TO BE VERIFIED AND EXECUTED BY AGDA.

-- 1. Prove that length distrbutes into (++):
--    
--    length (xs ++ ys) = length xs + length ys

∀ xs ⇒ length (xs ++ ys) = length xs + length ys
case xs ≔ []
    length ([] ++ ys)
= { defn. of (++) }
    length ys
= { defn. of (+) }
    0 + length ys
= { defn. of length }
    length [] + legnth ys
∎

case xs ≔ (x : xs)
    length ((x : xs) ++ ys)
= { defn. of (++) }
    length (x : (xs ++ ys))
= { defn. of length }
    1 + length (xs ++ ys)
= { induction }
    1 + (length xs + length ys)
= { associative of (+) }
    (1 + length xs) + length ys
= { defn. of length }
    length (x : xs) + length ys
∎
