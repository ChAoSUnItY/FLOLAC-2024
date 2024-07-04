module Prac1_provable where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.List using (List; []; _∷_; _++_; sum; concat; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Properties using (sum-++-commute)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+)
open import Function using (_∘_)
open import Level using (Level)

length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

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

sum-concat-++ : ∀ (xss : List (List ℕ)) → (sum ∘ concat) xss ≡ (sum ∘ (map sum)) xss
sum-concat-++ [] = begin
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
sum-concat-++ (x ∷ xs) = begin
    (sum ∘ concat) (x ∷ xs)
  ≡⟨⟩
    sum (concat (x ∷ xs))
  ≡⟨⟩
    sum (x ++ concat xs)
  ≡⟨ sum-++-commute x (concat xs) ⟩
    sum x + sum (concat xs)
  ≡⟨ cong (sum x +_) (sum-concat-++ xs) ⟩
    sum x + sum (map sum xs)
  ≡⟨⟩
    sum (sum x ∷ map sum xs)
  ≡⟨⟩
    sum (map sum (x ∷ xs))
  ≡⟨⟩
    (sum ∘ (map sum)) (x ∷ xs)
  ∎
