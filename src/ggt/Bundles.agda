module GGT.Bundles where

open import Level
open import Relation.Unary
open import Relation.Binary -- using (Rel)
open import Algebra.Core
open import Algebra.Bundles
open import GGT.Structures
open import Data.Product

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
  stab : Ω → Pred (Carrier G) ℓ₂
  stab o = λ (g : Carrier G) → o · g ≋ o

  -- TODO: orbital equivalence
  -- ·G : Ω → Pred

  _ω_  : Rel Ω (a ⊔ ℓ₂)
  o ω o' = ∃[ g ] (o · g ≋ o')

  _·G : Ω → Pred Ω (a ⊔ ℓ₂)
  o ·G = o ω_

  Orbit : Ω → Set (a ⊔ b ⊔ ℓ₂)
  -- classOf ω o -- [ o ] mod ω
  Orbit o = Σ[ o' ∈ Ω ] (o ω o')
  -- Orbit o = ?
