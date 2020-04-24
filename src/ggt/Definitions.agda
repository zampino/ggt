open import Relation.Binary.Core using (Rel)

module GGT.Definitions
  {a b ℓ₁ ℓ₂}
  {G : Set a}      -- The underlying group carrier
  {Ω : Set b}      -- The underlying space
  (_≈_ : Rel G ℓ₁) -- The underlying group equality
  (_≋_ : Rel Ω ℓ₂) -- The underlying space equality
  where

open import Level
open import Algebra.Core
open import Relation.Unary
open import Algebra.Bundles using (Group)
open import Algebra.Definitions _≋_ using (Congruent₁)

ActAssoc : Opᵣ G Ω → Op₂ G → Set _
ActAssoc _·_ _∙_ = ∀ (o : Ω) (g : G) (h : G) → (o · (g ∙ h)) ≋ ((o · g) · h)

ActLeftIdentity : G → Opᵣ G Ω → Set _
ActLeftIdentity ε _·_ = ∀ (o : Ω) → (o · ε) ≋ o

·-≋-Congruence : Opᵣ G Ω → Set _
·-≋-Congruence _·_ = ∀ (g : G) → Congruent₁ (_· g)
-- ∀ (o1 o2 : Ω) (g : G) → o1 ≋ o2 → (o1 · g) ≋ (o2 · g)

≈-Ext : Opᵣ G Ω → Set _
≈-Ext _·_ = ∀ {g h : G} → ∀ {o : Ω} → g ≈ h → (o · g) ≋ (o · h)

-- generic group definitions
isSubgroup : {l : Level} →
             (G : Group a ℓ₁) → Pred (Group.Carrier G) l → Set _
isSubgroup G P = ∀ (x y : Carrier) → P x → P y → P (y ⁻¹ ∙ x) where open Group G
