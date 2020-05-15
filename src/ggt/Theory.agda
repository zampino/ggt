open import GGT

module GGT.Theory
  {a b ℓ₁ ℓ₂}
  -- Throughout the following assume A is a (right) Action
  (A : Action a b ℓ₁ ℓ₂)
  where

open import Level
open import Relation.Unary hiding (_\\_)
open import Algebra

open Action A renaming (setoid to Ω')
-- open import Relation.Binary.Reasoning.MultiSetoid -- combines S and S'
open import Relation.Binary.Reasoning.Setoid Ω'
open Group G -- renaming (setoid to S')
open import GGT.Group.Structures {a} {ℓ₂} {ℓ₁}
open import GGT.Group.Bundles {a} {ℓ₂} {ℓ₁}

stabIsSubGroup : ∀ (o : Ω) → (stab o) ≤ G
stabIsSubGroup o = record { ε∈ = actId o ;
                            ∙-⁻¹-closed = itis ;
                            r = resp } where
  itis = λ {x} {y} px py → begin
                        (o · (x - y))  ≡⟨⟩
                        o · x ∙ (y ⁻¹) ≈⟨ actAssoc o x (y ⁻¹) ⟩
                        (o · x) · y ⁻¹ ≈⟨ ·-cong (y ⁻¹) px ⟩
                        o · y ⁻¹  ≈˘⟨ ·-cong (y ⁻¹) py ⟩
                        (o · y) · y ⁻¹ ≈˘⟨ actAssoc o y (y ⁻¹) ⟩
                        o · (y ∙ y ⁻¹) ≈⟨ G-ext (inverseʳ y) ⟩
                        o · ε ≈⟨ actId o ⟩
                        o ∎
  resp : ∀ {x y : Carrier} → x ≈ y → ((stab o) x) → ((stab o) y)
  resp {x} {y} x~y xfixeso = begin o · y ≈˘⟨ G-ext x~y ⟩
                               o · x ≈⟨ xfixeso ⟩
                               o ∎
Stab : Ω → SubGroup G
Stab o = record { P = stab o;
                  isSubGroup = stabIsSubGroup o}

open import Function.Bundles

orbitalCorr : {o : Ω} → Bijection (Stab o \\ G) Ω'
orbitalCorr = {!   !}
