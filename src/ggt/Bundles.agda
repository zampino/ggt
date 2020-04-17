module GGT.Bundles where

open import Level
open import Relation.Binary using (Rel)
open import Algebra.Core
open import Algebra.Bundles
open import GGT.Structures

-- do we need a left action definition?
-- parametrize over Op r/l?

record Action a b ℓ₁ ℓ₂ : Set (suc (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂))  where
  infixl 8 _·_
  open Group
  field
    G : Group a ℓ₁
    Ω : Set b
    ≋ : Rel Ω ℓ₂
    _·_ : Opᵣ (Carrier G) Ω
    isAction : IsAction (_≈_ G) ≋ _·_ (_∙_ G) (ε G) (_⁻¹ G) 
