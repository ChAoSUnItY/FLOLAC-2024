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
= { by induction }
    1 + (length xs + length ys)
= { associative of (+) }
    (1 + length xs) + length ys
= { defn. of length }
    length (x : xs) + length ys
∎

-- 2. Prove: sum ∙ concat = sum ∙ map sum

∀ x ⇒ sum ∙ concat x = sum ∙ map sum x
-- Or expands by definition of (.), which results:
∀ x ⇒ sum (concat x) = sum (map sum x)
case x ≔ []
    sum (concat [])
= { defn. of concat }
    sum []
= { defn. of map }
    sum (map sum [])

case x := (xs : xss)
    sum (concat (xs : xss))
= { defn. of concat }
    sum (xs ++ concat xss)
=

-- 3. Prove: filter p ∙ map f = map f ∙ filter (p ∙ f)

∀ xs ⇒ filter p (map f xs) = map f (filter (p ∙ f) xs)

case xs ≔ []
    filter p (map f [])
= { defn. of map }
    filter p []
= { defn. of filter }
    []
= { defn. of map }
    map f []
= { defn. of filter }
    map f (filter (p ∙ f) [])
∎

case xs ≔ (x : xs)
    filter p (map f (x : xs))
= { defn. of map }
    filter p (f x : map f xs)
= { defn. of filter }
    if p (f x) then f x : filter p (map f xs) 
               else filter p (map f xs)
= { by induction }
    if p (f x) then f x : map f (filter (p ∙ f) xs)
               else map f (filter (p ∙ f) xs)
= { defn. of map }
    if p (f x) then map f (x : filter (p ∙ f) xs)
               else map f (filter (p ∙ f) xs)
= { extract common expression }
    map f (if p (f x) then x : filter (p ∙ f) xs
                      else filter (p ∙ f) xs)
= { defn. of filter }
    map f (filter (p ∙ f) (x : xs))

