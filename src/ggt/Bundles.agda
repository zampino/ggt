module GGT.Bundles where

open import Level
open import Relation.Unary
open import Relation.Binary using (Rel)
open import Algebra.Core
open import Algebra.Bundles
open import GGT.Structures

-- do we need a left action definition?
-- parametrize over Op r/l?

record Action a b ℓ₁ ℓ₂ : Set (suc (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂))  where
  infix 6 _·_
  infix 3 _≋_
  open Group
  field
    G : Group a ℓ₁
    Ω : Set b
    _≋_ : Rel Ω ℓ₂
    _·_ : Opᵣ (Carrier G) Ω
    isAction : IsAction (_≈_ G) _≋_ _·_ (_∙_ G) (ε G) (_⁻¹ G)

  open IsAction isAction public

  -- the (raw) pointwise stabilizer
  Stab : Ω → Pred (Carrier G) ℓ₂
  Stab o = λ (g : (Carrier G)) → o ≋ (o · g)

  -- TODO: orbital equivalence
  -- _orbit_    : Rel Ω ℓ₂
  -- o orbit o' = ∃ (g : G) → (o · g) ≋ o'
