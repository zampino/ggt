module GGT.Group.Structures
  {a ℓ}
  where

open import Relation.Unary using (Pred)
open import Algebra.Bundles using (Group)
open import Level
open import GGT.Group.Definitions

record IsSubgroup {l : Level} (G : Group a ℓ) (P : Pred (Group.Carrier G) l) : Set (a ⊔ suc l) where
  open Group G
  field
    ε∈ : (P ε)
    is-∙-Closed : IsOpInvClosed G P

syntax IsSubgroup G P = P ≤ G
