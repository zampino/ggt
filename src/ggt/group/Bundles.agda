module GGT.Group.Bundles
  {a b ℓ}
  where

open import Algebra.Bundles using (Group)
open import Relation.Unary
open import Relation.Binary
open import Level
open import GGT.Group.Structures

record SubGroup (G : Group a ℓ) : Set (a ⊔ suc b ⊔ ℓ) where
  open Group G public
  field
    P : Pred Carrier b
    isSubGroup : IsSubGroup G P

  open IsSubGroup isSubGroup public
  -- imports ~
  -- xy-1 ∈ H => xy-1 = h => h'xy-1 = h'' => h'x = h''y -- right cosets
  -- x ↦ ω · x = ω · yx-1 · x = ω · y

cosetʳRel : {G : Group a ℓ} → (SubGroup G) → Setoid a b

cosetʳRel {G} H = record { Carrier = Carrier;
                         _≈_ = _∼_;
                         isEquivalence = iseq} where
                  open SubGroup H
                  open import GGT.Group.Facts G
                  iseq = record {refl  = cosetRelRefl isSubGroup ;
                                 sym   = cosetRelSym isSubGroup ;
                                 trans = cosetRelTrans isSubGroup }

syntax cosetʳRel {G} H = H \\ G
