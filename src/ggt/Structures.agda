open import Relation.Binary using (Rel; Setoid; IsEquivalence)

module GGT.Structures
  {a b ℓ₁ ℓ₂}
  {G : Set a}       -- The underlying set (group carrier
  {Ω : Set b}       -- The underlying set (space)
  (_≈_ : Rel G ℓ₁) -- The underlying group equality
  (_≋_ : Rel Ω ℓ₂) -- The underlying space equality
  where

open import Level using (_⊔_)
open import Algebra.Core
open import Algebra.Structures {a} {ℓ₁} {G} using (IsGroup)
open import GGT.Definitions

record IsAction
  (· : Opᵣ G Ω)
  (∙ : Op₂ G)
  (ε : G)
  (⁻¹ : Op₁ G)
  : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
  where

  field
    isEquivalence : IsEquivalence _≋_
    isGroup       : IsGroup _≈_ ∙ ε ⁻¹
    actAssoc      : ActAssoc _≋_ · ∙
    actId         : ActId _≋_ ε ·
    ·-cong        : ActCongruent _≋_ ·

  setoid : Setoid b ℓ₂
  setoid = record { isEquivalence = isEquivalence }
