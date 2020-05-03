module GGT.Group.Structures
  {a b ℓ}
  where

open import Relation.Unary using (Pred)
open import Relation.Binary
open import Algebra.Bundles using (Group)
open import Level
open import GGT.Group.Definitions

record IsSubGroup (G : Group a ℓ) (P : Pred (Group.Carrier G) b) : Set (a ⊔ b ⊔ ℓ) where
  open Group G
  field
    ε∈ : (P ε)
    ∙-⁻¹-closed : IsOpInvClosed G P
    r : P Respects _≈_

  -- coset relation
  _∼_ : Rel Carrier b
  x ∼ y = P (x - y)

syntax IsSubGroup G P = P ≤ G
