open import GGT

module GGT.Theory
  {a b ℓ₁ ℓ₂}
  -- Throughout the following assume A is a (right) Action
  (A : Action a b ℓ₁ ℓ₂)
  where

open import Level
open import Relation.Unary hiding (_\\_)
open import Algebra
open import Data.Product

open Action A renaming (setoid to Ω')
open import Relation.Binary.Reasoning.MultiSetoid
-- open import Relation.Binary.Reasoning.Setoid Ω' would be enough
open import Relation.Binary.Core
open Group G renaming (setoid to S)
open import GGT.Group.Structures {a} {ℓ₂} {ℓ₁}
open import GGT.Group.Bundles {a} {ℓ₂} {ℓ₁}
open import Function.Bundles
open import Function.Base using (_on_)
open import Relation.Binary.Bundles

stabIsSubGroup : ∀ (o : Ω) → (stab o) ≤ G
stabIsSubGroup o = record { ε∈ = actId o ;
                            ∙-⁻¹-closed = itis ;
                            r = resp } where
  itis = λ {x} {y} px py → begin⟨ Ω' ⟩
                        (o · (x - y))  ≡⟨⟩
                        o · x ∙ (y ⁻¹) ≈⟨ actAssoc o x (y ⁻¹) ⟩
                        (o · x) · y ⁻¹ ≈⟨ ·-cong (y ⁻¹) px ⟩
                        o · y ⁻¹  ≈˘⟨ ·-cong (y ⁻¹) py ⟩
                        (o · y) · y ⁻¹ ≈˘⟨ actAssoc o y (y ⁻¹) ⟩
                        o · (y ∙ y ⁻¹) ≈⟨ G-ext (inverseʳ y) ⟩
                        o · ε ≈⟨ actId o ⟩
                        o ∎
  resp : ∀ {x y : Carrier} → x ≈ y → ((stab o) x) → ((stab o) y)
  resp {x} {y} x~y xfixeso = begin⟨ Ω' ⟩
                               o · y ≈˘⟨ G-ext x~y ⟩
                               o · x ≈⟨ xfixeso ⟩
                               o ∎

Stab : Ω → SubGroup G
Stab o = record { P = stab o;
                  isSubGroup = stabIsSubGroup o}

orbitalCorr : {o : Ω} → Bijection (Stab o \\ G) (Orbit o)
orbitalCorr {o} = record { f = f ;
                           cong = cc ;
                           bijective = inj ,′ surj } where
  open Setoid (Stab o \\ G) renaming (_≈_ to _≈₁_; Carrier to G')
  open Setoid (Orbit o)     renaming (_≈_ to _≈₂_)
  open Setoid S renaming (refl to r)

  f : G' → Σ Ω (o ·G)
  f x = (o · x , ( x , G-ext r))

  cc : f Preserves _≈₁_ ⟶ _≈₂_
  cc {g} {h} g≈₁h = begin⟨ Ω' ⟩  -- f h ≈₂ f g
                      o · g ≈˘⟨ actId (o · g) ⟩
                      (o · g) · ε ≈˘⟨ G-ext (inverseˡ h) ⟩
                      (o · g) · (h ⁻¹ ∙ h ) ≈˘⟨ actAssoc o g (h ⁻¹ ∙ h ) ⟩
                      o · (g  ∙ (h ⁻¹ ∙ h )) ≈˘⟨ G-ext (assoc _ _ _) ⟩
                      o · ((g  ∙ h ⁻¹) ∙ h ) ≈⟨ actAssoc _ _ h ⟩
                      (o · (g  ∙ h ⁻¹)) · h ≈⟨ ·-cong h g≈₁h ⟩
                      -- g≈₁h ⇒ P (g ∙ h ⁻¹) ⇒ (g ∙ h ⁻¹) ∈ Stab o
                      o · h ∎
  inj : _
  -- o · g = o · h ⇒ g ∙ h ⁻¹ ∈ Stab o
  inj {g} {h} fg≈₂fh = begin⟨ Ω' ⟩
                         o · g ∙ h ⁻¹ ≈⟨ actAssoc _ _ _ ⟩
                         (o · g) · h ⁻¹ ≈⟨ ·-cong _ fg≈₂fh ⟩
                         (o · h) · h ⁻¹ ≈˘⟨ actAssoc _ _ _ ⟩
                         o · (h ∙ h ⁻¹) ≈⟨ G-ext (inverseʳ h)⟩
                         o · ε ≈⟨ actId o ⟩
                         o ∎

  surj : _
  surj (_ , p) = p
