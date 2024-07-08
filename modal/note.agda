# Axioms for ◆

T′ : P → ◆ P is valid
WTS : ∀ t . t ⊨ P → ◆ P
    ≡ t 

Ł′ : ◆◆ P → ◆ P is valid
WTS : ∀ t . t ⊨ ◆◆ P → ◆ P
    ≡ ∀ t . if Ł ⊨ ◆◆ P then t ⊨ ◆ P
    ≡ ∀ t . 
