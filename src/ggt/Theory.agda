open import GGT

module GGT.Theory
  {a b ℓ₁ ℓ₂}
  -- Throughout the following assume A is a (right) Action
  (A : Action a b ℓ₁ ℓ₂)
  where

open import Level
open import Relation.Unary
open import Algebra

open Action A renaming (setoid to S)
-- open import Relation.Binary.Reasoning.MultiSetoid -- combines S and S'
open import Relation.Binary.Reasoning.Setoid S
open Group G -- renaming (setoid to S')
open import GGT.Group.Structures

stabIsSubGroup : ∀ (o : Ω) → (Stab o) ≤ G
stabIsSubGroup o = record { ε∈ = actId o ;
                            is-∙-Closed = itis} where
  itis = λ x y px py → begin
                        (o · (x - y))  ≡⟨⟩
                        o · x ∙ (y ⁻¹) ≈⟨ actAssoc o x (y ⁻¹) ⟩
                        (o · x) · y ⁻¹ ≈⟨ ·-cong (y ⁻¹) px ⟩
                        o · y ⁻¹  ≈˘⟨ ·-cong (y ⁻¹) py ⟩
                        (o · y) · y ⁻¹ ≈˘⟨ actAssoc o y (y ⁻¹) ⟩
                        o · (y ∙ y ⁻¹) ≈⟨ G-ext (inverseʳ y) ⟩
                        o · ε ≈⟨ actId o ⟩
                        o ∎
