module Prac1_provable where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; inspect; [_])
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; sum; concat; map)
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

infix 1 if_then_else_

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then x else y = x
if false then x else y = y

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
-- Weird workaround, type checker doesn't agree with original detailed provement
-- See https://stackoverflow.com/questions/10320052/%E2%89%A1-reasoning-and-with-patterns
filter-map (x ∷ xs) f p with p (f x)
... | true  = cong (λ a → f x ∷ a) (filter-map xs f p)
... | false = filter-map xs f p

-- I am not sure how we can prove Q4 with Agda at this moment.
