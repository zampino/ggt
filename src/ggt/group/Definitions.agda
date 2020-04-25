module GGT.Group.Definitions
  {a ℓ}
   where

open import Relation.Unary using (Pred)
open import Algebra.Bundles using (Group)
open import Level


IsSubgroup : {l : Level} → (G : Group a ℓ) → (Pred (Group.Carrier G) l) → Set (a ⊔ l)
IsSubgroup G P = ∀ (x y : Carrier) → P x → P y → P (x - y) where open Group G

syntax IsSubgroup G P = P ≤ G

-- xy-1 ∈ H => xy-1 = h => h'xy-1 = h'' => h'x = h''y -- right cosets
-- x ↦ ω · x = ω · yx-1 · x = ω · y
