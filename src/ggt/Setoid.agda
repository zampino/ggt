open import Relation.Binary
open import Level
module GGT.Setoid
  {a ℓ}
  (S : Setoid a ℓ)
  (l : Level)
  where

open import Level
open Setoid S
open import Data.Product
open import Relation.Unary
open import Relation.Binary.Construct.On renaming (isEquivalence to isEq)

open import Function

subSetoid : (Pred Carrier l) → Setoid (a ⊔ l) ℓ
subSetoid P =
  record { Carrier = Σ Carrier P ;
           _≈_ = (_≈_ on proj₁) ;
           isEquivalence = isEq proj₁ isEquivalence }
