open import Algebra.Bundles using (Group)

module GGT.Group.Facts
  {a b ℓ}
  (G : Group a ℓ)
  where

open import Relation.Unary using (Pred)
open import Relation.Binary
open import GGT.Group.Structures
open import Algebra.Bundles using (Group)
open import Algebra.Properties.Group G
open Group G
open import Relation.Binary.Reasoning.Setoid setoid

⁻¹-anti-homo-- : ∀ (x y : Carrier) → (x - y)⁻¹ ≈ y - x
⁻¹-anti-homo-- x y = begin
                      (x - y)⁻¹ ≡⟨⟩
                      (x ∙ y ⁻¹)⁻¹ ≈⟨ ⁻¹-anti-homo-∙ _ _ ⟩
                      (y ⁻¹) ⁻¹ ∙ x ⁻¹ ≈⟨ ∙-congʳ (⁻¹-involutive _) ⟩
                      y ∙ x ⁻¹ ≡⟨⟩
                      y - x ∎

subgroup⁻¹-closed : {P : Pred Carrier b } →
                        IsSubGroup G P →
                        ∀ x → P x → P (x ⁻¹)
subgroup⁻¹-closed iss x px =
  -- e - x = x ⁻¹ →  P e - x → P x ⁻¹
  r (identityˡ (x ⁻¹)) (∙-⁻¹-closed ε∈ px)
  where open IsSubGroup iss

-- -----
-- (Right) Coset Relation is Equivalenc
cosetRelRefl : {P : Pred Carrier b } →
               (iss : IsSubGroup G P) → Reflexive (IsSubGroup._∼_ iss)
cosetRelRefl iss {x} = r (sym (inverseʳ x)) ε∈ where open IsSubGroup iss
-- (e = x - x) → P e → P x - x
cosetRelSym : {P : Pred Carrier b } →
              (iss : IsSubGroup G P) → Symmetric (IsSubGroup._∼_ iss)

cosetRelSym iss {x} {y} x∼y = r u≈y-x Pu where
-- P e → P (x - y) → P (y - x)
  open IsSubGroup iss
  u≈y-x = begin
            ε - (x - y) ≡⟨⟩
            ε ∙ (x - y)⁻¹ ≈⟨ identityˡ ((x - y)⁻¹) ⟩
            (x - y)⁻¹ ≈⟨ ⁻¹-anti-homo-- _ _ ⟩
            y - x ∎
  Pu = ∙-⁻¹-closed ε∈ x∼y

cosetRelTrans : {P : Pred Carrier b } →
                (iss : IsSubGroup G P) → Transitive (IsSubGroup._∼_ iss)
cosetRelTrans iss {x} {y} {z} x∼y y∼z =
  r x-y-[z-y]≈x-z Pu where
    open IsSubGroup iss
    -- P z - y
    z∼y = cosetRelSym iss y∼z
    x-y-[z-y]≈x-z = begin
                      (x - y) - (z - y) ≡⟨⟩
                      (x - y) ∙ (z - y) ⁻¹ ≈⟨ ∙-congˡ (⁻¹-anti-homo-- z y) ⟩
                      (x - y) ∙ (y - z) ≡⟨⟩
                      (x ∙ y ⁻¹) ∙ (y ∙ z ⁻¹)  ≈⟨ assoc x (y ⁻¹) (y ∙ z ⁻¹) ⟩
                      x ∙ (y ⁻¹ ∙ (y ∙ z ⁻¹))  ≈˘⟨ ∙-congˡ (assoc (y ⁻¹) y (z ⁻¹)) ⟩
                      x ∙ ((y ⁻¹ ∙ y) ∙ z ⁻¹)  ≈⟨ ∙-congˡ (∙-congʳ (inverseˡ _)) ⟩
                      x ∙ (ε ∙ z ⁻¹) ≈⟨ ∙-congˡ (identityˡ _) ⟩
                      x ∙ z ⁻¹ ≡⟨⟩
                      x - z ∎
    Pu = ∙-⁻¹-closed {x - y} {z - y} x∼y z∼y
