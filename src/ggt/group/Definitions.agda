module GGT.Group.Definitions
  {a ℓ}
   where

open import Relation.Unary using (Pred)
open import Algebra.Bundles using (Group)
open import Level


IsOpInvClosed : {l : Level} → (G : Group a ℓ) → (Pred (Group.Carrier G) l) → Set (a ⊔ l)
IsOpInvClosed G P = ∀ (x y : Carrier) → P x → P y → P (x - y) where open Group G
