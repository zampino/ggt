module Scratch.Data.List.Relation.Helpers where

open import Relation.Nullary
open import Relation.Nullary.Decidable

open import Relation.Unary
open import Relation.Binary hiding (Decidable)

open import Data.Product

open import Data.List.Base
open import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties
open import Data.List.Relation.Unary.AllPairs

module _ {a ℓ ℓ₁ ℓ₂} {A : Set a}
         {R : Rel A ℓ₁} {S : Rel A ℓ₂}
         {P : Pred A ℓ} (P? : Decidable P) where

  filter⁺⁺ : ∀ {xs} → (∀ {x y} → P x → P y → R x y → S x y) →
            AllPairs R xs → AllPairs S (filter P? xs)
  filter⁺⁺ {[]} _ _ = []
  filter⁺⁺ {x ∷ xs} Δ (h ∷ t) with (P? x)
  ... | yes p = let
                  hf : All (R x) (filter P? xs)
                  hf = filter⁺ P? h
                  ap : All P (filter P? xs)
                  ap = all-filter P? xs
                  w : All (P ∩ R x) (filter P? xs)
                  w = All.zip ( ap , hf )
                  y : P ∩ R x ⊆ S x
                  y = λ z → Δ p (proj₁ z) (proj₂ z)
                  z : All (S x) (filter P? xs)
                  z =  All.map y w
                in z ∷ filter⁺⁺ {xs} Δ t
  ... | no  ¬p = filter⁺⁺ {xs} Δ t
