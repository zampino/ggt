open import Relation.Binary

module GGT.Setoid
  {a b l}
  (S : Setoid a l)
  where

open import Level
open Setoid S
open import Data.Product
open import Relation.Unary
open import Relation.Binary.Construct.On renaming (isEquivalence to isEq)

open import Function

subSetoid : (Pred Carrier b) → Setoid (a ⊔ b) l
subSetoid P =
  record { Carrier = Σ Carrier P ;
           _≈_ = (_≈_ on proj₁) ;
           isEquivalence = isEq proj₁ isEquivalence }
