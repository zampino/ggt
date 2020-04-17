open import Relation.Binary.Core using (Rel)

module GGT.Definitions
  {a b ℓ}
  {G : Set a}     -- The underlying sets (space / group carrier)
  {Ω : Set b}
  (_≈_ : Rel Ω ℓ) -- The underlying equality
  where

open import Algebra.Core

ActAssoc : Opᵣ G Ω → Op₂ G → Set _
ActAssoc _·_ _∙_ = ∀ (o : Ω) (g : G) (h : G) → (o · (g ∙ h)) ≈ ((o · g) · h)

ActId : G → Opᵣ G Ω → Set _
ActId ε _·_ = ∀ (o : Ω) → (o · ε) ≈ o
