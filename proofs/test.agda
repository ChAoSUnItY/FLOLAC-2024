open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)

a = (_∷_ [])

-- Untyped: length ≔ λl. l (λ_. plus 1) 0

-- lengthσ ≔ λ(xs : list (A)). xs (λ(_). add c₁) c₀

-- lengthσ² ≔ λ(xs : list (A)).λ(X).λ(f : X → X).λ(x : X).xs (λ(_).(X f x)) (x)