open import GGT

-- Throughout the following assume A is a (right) Action
module GGT.Theory
  {a b ℓ₁ ℓ₂}
  (A : Action a b ℓ₁ ℓ₂)
  where

open import Level
open import Relation.Unary hiding (_\\_; _⇒_)
open import Relation.Binary
open import Algebra
open import Data.Product

open Action A renaming (setoid to Ω')
open import Relation.Binary.Reasoning.MultiSetoid
-- open import Relation.Binary.Reasoning.Setoid Ω' would be enough

open Group G renaming (setoid to S)
open import GGT.Group.Structures {a} {ℓ₂} {ℓ₁}
open import GGT.Group.Bundles {a} {ℓ₂} {ℓ₁}
open import Function.Bundles
open import Function.Base using (_on_)

orbitalEq : IsEquivalence _ω_
orbitalEq = record { refl =  r ;
                     sym  =  s ;
                     trans = t } where
  open Setoid Ω' renaming (sym to σ)
  r : Reflexive _ω_
  r {o} = ε , actId o

  s : Symmetric _ω_
  s {x} {y} ( g , x·g≡y ) = (g ⁻¹ , y·g⁻¹≡x) where
    y·g⁻¹≡x = σ x≡y·g⁻¹ where
      x≡y·g⁻¹ = begin⟨ Ω' ⟩
                  x              ≈˘⟨ actId x ⟩
                  x · ε          ≈˘⟨ G-ext (inverseʳ _) ⟩
                  x · (g ∙ g ⁻¹) ≈⟨ actAssoc _ _ _ ⟩
                  x · g · g ⁻¹   ≈⟨ ·-cong (g ⁻¹) x·g≡y ⟩
                  y · g ⁻¹ ∎
  t : Transitive _ω_
  t {x} {y} {z} ( g , x·g≡y ) ( h , y·h≡z ) = ( g ∙ h , x·gh≡z ) where
    x·gh≡z : _
    x·gh≡z = begin⟨ Ω' ⟩
              x · (g ∙ h) ≈⟨ actAssoc _ _ _ ⟩
              x · g · h ≈⟨ ·-cong _ x·g≡y ⟩
              y · h ≈⟨ y·h≡z ⟩
              z ∎

ω≤≋ : _≋_ ⇒ _ω_
ω≤≋ {o} {o'} o≋o' = (ε , oε≋o' ) where
  oε≋o' = begin⟨ Ω' ⟩
            o · ε ≈⟨ actId o ⟩
            o ≈⟨ o≋o' ⟩
            o' ∎

stabIsSubGroup : ∀ (o : Ω) → (stab o) ≤ G
stabIsSubGroup o = record { ε∈ = actId o ;
                            ∙-⁻¹-closed = itis ;
                            r = resp } where
  itis = λ {x} {y} px py → begin⟨ Ω' ⟩
                        (o · (x - y))  ≡⟨⟩
                        o · x ∙ (y ⁻¹) ≈⟨ actAssoc o x (y ⁻¹) ⟩
                        o · x · y ⁻¹ ≈⟨ ·-cong (y ⁻¹) px ⟩
                        o · y ⁻¹  ≈˘⟨ ·-cong (y ⁻¹) py ⟩
                        o · y · y ⁻¹ ≈˘⟨ actAssoc o y (y ⁻¹) ⟩
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
                      o · g · ε ≈˘⟨ G-ext (inverseˡ h) ⟩
                      o · g · (h ⁻¹ ∙ h ) ≈˘⟨ actAssoc o g (h ⁻¹ ∙ h ) ⟩
                      o · (g  ∙ (h ⁻¹ ∙ h )) ≈˘⟨ G-ext (assoc _ _ _) ⟩
                      o · ((g  ∙ h ⁻¹) ∙ h ) ≈⟨ actAssoc _ _ h ⟩
                      o · (g  ∙ h ⁻¹) · h ≈⟨ ·-cong h g≈₁h ⟩
                      -- g≈₁h ⇒ P (g ∙ h ⁻¹) ⇒ (g ∙ h ⁻¹) ∈ Stab o
                      o · h ∎
  inj : _
  -- o · g = o · h ⇒ g ∙ h ⁻¹ ∈ Stab o
  inj {g} {h} fg≈₂fh = begin⟨ Ω' ⟩
                         o · g ∙ h ⁻¹ ≈⟨ actAssoc _ _ _ ⟩
                         o · g · h ⁻¹ ≈⟨ ·-cong _ fg≈₂fh ⟩
                         o · h · h ⁻¹ ≈˘⟨ actAssoc _ _ _ ⟩
                         o · (h ∙ h ⁻¹) ≈⟨ G-ext (inverseʳ h)⟩
                         o · ε ≈⟨ actId o ⟩
                         o ∎

  surj : _
  surj (_ , p) = p
