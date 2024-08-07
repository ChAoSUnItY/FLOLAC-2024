module Prac1_provable where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; if_then_else_; true; false)
open import Data.List using (List; []; _∷_; _++_; sum; concat; map; take; drop)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Properties using (sum-++-commute)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+)
open import Function using (_∘_)
open import Level using (Level)

length : ∀ {A : Set} → List A → ℕ
length []       = zero
length (x ∷ xs) = suc (length xs)

-- Q1
length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys =
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    0 + length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎
length-++ (x ∷ xs) ys =
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨⟩
    length (x ∷ (xs ++ ys))
  ≡⟨⟩
    1 + length (xs ++ ys)
  ≡⟨ cong (1 +_) (length-++ xs ys) ⟩
    1 + length xs + length ys
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎

-- Q2
sum-concat : ∀ (xss : List (List ℕ)) → (sum ∘ concat) xss ≡ (sum ∘ (map sum)) xss
sum-concat [] = begin
    (sum ∘ concat) []
  ≡⟨⟩
    sum (concat [])
  ≡⟨⟩
    sum []
  ≡⟨⟩
    sum (map sum [])
  ≡⟨⟩
    (sum ∘ (map sum)) []
  ∎
sum-concat (x ∷ xs) = begin
    (sum ∘ concat) (x ∷ xs)
  ≡⟨⟩
    sum (concat (x ∷ xs))
  ≡⟨⟩
    sum (x ++ concat xs)
  ≡⟨ sum-++-commute x (concat xs) ⟩
    sum x + sum (concat xs)
  ≡⟨ cong (sum x +_) (sum-concat xs) ⟩
    sum x + sum (map sum xs)
  ≡⟨⟩
    sum (sum x ∷ map sum xs)
  ≡⟨⟩
    sum (map sum (x ∷ xs))
  ≡⟨⟩
    (sum ∘ (map sum)) (x ∷ xs)
  ∎

filterᵝ : ∀ {A : Set} → (A → Bool) → List A → List A
filterᵝ p []       = []
filterᵝ p (x ∷ xs) =
  if (p x) then (x ∷ (filterᵝ p xs))
           else (filterᵝ p xs)

-- Q3
filter-map : ∀ {A B : Set} (xs : List A) (f : A → B) (p : B → Bool) → 
  (filterᵝ p ∘ map f) xs ≡ (map f ∘ filterᵝ (p ∘ f)) xs
filter-map [] f p =
  begin
    (filterᵝ p ∘ map f) []
  ≡⟨⟩
    filterᵝ p (map f [])
  ≡⟨⟩
    filterᵝ p []
  ≡⟨⟩
    []
  ≡⟨⟩
    map f []
  ≡⟨⟩
    map f (filterᵝ (p ∘ f) [])
  ≡⟨⟩
    (map f ∘ filterᵝ (p ∘ f)) []
  ∎
-- Weird workaround, type checker doesn't agree with original detailed proof
-- See https://stackoverflow.com/questions/10320052/%E2%89%A1-reasoning-and-with-patterns
filter-map (x ∷ xs) f p with p (f x)
... | true  = cong (λ a → f x ∷ a) (filter-map xs f p)
... | false = filter-map xs f p

-- I am not sure how we can prove Q4 with Agda at this moment.

-- Q5
take-then-drop : ∀ {A : Set} → (n : ℕ) (xs : List A) → take n xs ++ drop n xs ≡ xs
take-then-drop zero [] =
  begin
    take zero [] ++ drop zero []
  ≡⟨⟩
    [] ++ []
  ≡⟨⟩
    []
  ∎
take-then-drop (suc n) [] =
  begin
    take (suc n) [] ++ drop (suc n) []
  ≡⟨⟩
    [] ++ []
  ≡⟨⟩
    []
  ∎
take-then-drop zero (x ∷ xs) =
  begin
    take zero (x ∷ xs) ++ drop zero (x ∷ xs)
  ≡⟨⟩
    [] ++ (x ∷ xs)
  ≡⟨⟩
    x ∷ xs
  ∎
take-then-drop (suc n) (x ∷ xs) =
  begin
    take (suc n) (x ∷ xs) ++ drop (suc n) (x ∷ xs)
  ≡⟨⟩
    (x ∷ take n xs) ++ drop n xs
  ≡⟨⟩
    x ∷ (take n xs ++ drop n xs)
  ≡⟨ cong (x ∷_) (take-then-drop n xs) ⟩
    x ∷ xs
  ∎
 
-- Q6
-- insert : {A : Set} → ℕ → A → List A → List A
-- insert i a [] = []
-- insert 0 a xs = a ∷ xs
-- insert i a (x ∷ xs) = x ∷ insert (i ∸ 1) a xs

-- fan′ : {A : Set} → ℕ → A → List A → List (List A)
-- fan′ zero a xs = (xs ++ (a ∷ [])) ∷ []
-- fan′ (suc i) a xs = insert (length xs ∸ (i + 1)) a xs ∷ fan′ i a xs

-- fan : {A : Set} → A → List A → List (List A)
-- fan a [] = []
-- fan a xs = fan′ (length xs) a xs

-- From solution sheet
fanᵝ : {A : Set} → A → List A → List (List A)
fanᵝ a [] = (a ∷ []) ∷ []
fanᵝ a (x ∷ xs) = (a ∷ x ∷ xs) ∷ map (_∷_ x) (fanᵝ a xs)

-- Q7
map-fusion : ∀ {A B C : Set} (g : A → B) (f : B → C) (xs : List A) → (map f ∘ map g) xs ≡ map (f ∘ g) xs
map-fusion g f [] = 
  begin
    (map f ∘ map g) [] 
  ≡⟨⟩
    map f (map g [])
  ≡⟨⟩
    map f []
  ≡⟨⟩
    []
  ≡⟨⟩
    map (f ∘ g) []
  ∎
map-fusion g f (x ∷ xs) = begin
    (map f ∘ map g) (x ∷ xs)
  ≡⟨⟩
    map f (map g (x ∷ xs))
  ≡⟨⟩
    map f (g x ∷ (map g xs))
  ≡⟨⟩
    f (g x) ∷ map f (map g xs)
  ≡⟨ cong (f (g x) ∷_) (map-fusion g f xs) ⟩
    f (g x) ∷ map (f ∘ g) xs
  ≡⟨⟩
    ((f ∘ g) x) ∷ map (f ∘ g) xs
  ≡⟨⟩
    map (f ∘ g) (x ∷ xs)
  ∎



map-fusion² : ∀ {A B C : Set} (g : A → B) (f : B → C) (xs : List A) → (map f) (map g xs) ≡ map (f ∘ g) xs
map-fusion² g f [] = refl
map-fusion² g f (x ∷ xs) = begin
    (map f) (map g (x ∷ xs))
  ≡⟨⟩
    map f (g x ∷ map g xs)
  ≡⟨⟩
    f (g x) ∷ (map f (map g xs))
  ≡⟨ cong (f (g x) ∷_) (map-fusion² g f xs) ⟩
    f (g x) ∷ (map (f ∘ g) xs)
  ≡⟨⟩
    (f ∘ g) x ∷ (map (f ∘ g) xs)
  ≡⟨⟩
    map (f ∘ g) (x ∷ xs)
  ∎

map-fan : ∀ {A B : Set} (f : A → B) (x : A) (xs : List A) → map (map f) (fanᵝ x xs) ≡ fanᵝ (f x) (map f xs)
map-fan f x [] = 
  begin
    map (map f) (fanᵝ x [])
  ≡⟨⟩
    map (map f) ((x ∷ []) ∷ [])
  ≡⟨⟩
    ((f x ∷ []) ∷ [])
  ≡⟨⟩
    fanᵝ (f x) []
  ≡⟨⟩
    fanᵝ (f x) (map f [])
  ∎
map-fan f x (y ∷ ys) = 
  begin
    map (map f) (fanᵝ x (y ∷ ys))
  ≡⟨ refl ⟩
    map (map f) ((x ∷ y ∷ ys) ∷ map (y ∷_) (fanᵝ x ys))
  ≡⟨ refl ⟩
    map f (x ∷ y ∷ ys) ∷ map (map f) (map (y ∷_) (fanᵝ x ys))
  ≡⟨ cong (map f (x ∷ y ∷ ys) ∷_)
          (map-fusion² (y ∷_) (map f) (fanᵝ x ys)) ⟩
    map f (x ∷ y ∷ ys) ∷ map ((map f) ∘ (y ∷_)) (fanᵝ x ys)
  ≡⟨ refl ⟩
    map f (x ∷ y ∷ ys) ∷ map ((f y ∷_) ∘ (map f)) (fanᵝ x ys)
  ≡⟨ cong (map f (x ∷ y ∷ ys) ∷_)
          (sym (map-fusion² (map f) (f y ∷_) (fanᵝ x ys))) ⟩
    map f (x ∷ y ∷ ys) ∷ map (f y ∷_) (map (map f) (fanᵝ x ys))
  ≡⟨ cong ((map f (x ∷ y ∷ ys) ∷_) ∘ map (f y ∷_)) (map-fan f x ys) ⟩
    map f (x ∷ y ∷ ys) ∷ map (f y ∷_) (fanᵝ (f x) (map f ys))
  ≡⟨ refl ⟩
    (f x ∷ f y ∷ map f ys) ∷ map (f y ∷_) (fanᵝ (f x) (map f ys))
  ≡⟨ refl ⟩
    fanᵝ (f x) (f y ∷ map f ys)
  ≡⟨ refl ⟩ 
    fanᵝ (f x) (map f (y ∷ ys))
  ∎ 


  -- begin
  -- --   map (map f) (fanᵝ x (y ∷ ys))
  -- -- ≡⟨ map (map f) (fanᵝ x (y ∷ ys)) ⟩
  -- --   map (map f) ((x ∷ y ∷ ys) ∷ map (_∷_ y) (fanᵝ x ys))
  -- -- ≡⟨⟩
  --   (f x ∷ f y ∷ map f ys) ∷ map (map f) (map (_∷_ y) (fan x ys))
  -- ≡⟨ cong (_∷_ (f x ∷ f y ∷ map f ys)) (
  --       begin
  --         map (map f) (map (_∷_ y) (fan x ys))
  --       ≡⟨ map-fusion² (_∷_ y) (map f) (fan x ys) ⟩
  --         map (λ z → f y ∷ map f z) (fan x ys)
  --       ≡⟨ {!   !} ⟩
  --         map (_∷_ (f y)) (fan (f x) (map f ys))
  --       ∎
  -- )⟩
  --   -- map f (x ∷ y ∷ ys) ∷ map (map f) (map (_∷_ y) (fanᵝ x ys))
  --   (f x ∷ f y ∷ map f ys) ∷ map (_∷_ (f y)) (fan (f x) (map f ys))
  -- ∎
