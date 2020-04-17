open import Relation.Binary using (Rel; Setoid; IsEquivalence)

module GGT.Structures
  {a b ℓ₁ ℓ₂}
  {G : Set a}       -- The underlying set (group carrier
  {Ω : Set b}       -- The underlying set (space)
  (_≈₁_ : Rel G ℓ₁) -- The underlying group equality (explicit)
  (_≈₂_ : Rel Ω ℓ₂) -- The underlying space equality (explicit)
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
    isEquivalence : IsEquivalence _≈₂_
    isGroup       : IsGroup _≈₁_ ∙ ε ⁻¹
    actAssoc      : ActAssoc _≈₂_ · ∙
    actId         : ActId _≈₂_ ε ·

  -- TODO:
  -- ·-cong : congruence on Ω wrt ·
  -- setoid : Setoid on Ω-equivalence
