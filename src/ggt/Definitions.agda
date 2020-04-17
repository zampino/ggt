open import Relation.Binary.Core using (Rel)

module GGT.Definitions
  {a b ℓ}
  {G : Set a}     -- The underlying sets (space / group carrier)
  {Ω : Set b}
  (_≋_ : Rel Ω ℓ) -- The underlying equality
  where

open import Algebra.Core
open import Algebra.Definitions _≋_ using (Congruent₁)

ActAssoc : Opᵣ G Ω → Op₂ G → Set _
ActAssoc _·_ _∙_ = ∀ (o : Ω) (g : G) (h : G) → (o · (g ∙ h)) ≋ ((o · g) · h)

ActId : G → Opᵣ G Ω → Set _
ActId ε _·_ = ∀ (o : Ω) → (o · ε) ≋ o

ActCongruent : Opᵣ G Ω → Set _
ActCongruent _·_ = ∀ (g : G) → Congruent₁ (_· g)
-- ∀ (o1 o2 : Ω) (g : G) → o1 ≋ o2 → (o1 · g) ≋ (o2 · g)
