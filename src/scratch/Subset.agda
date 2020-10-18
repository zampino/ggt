module Scratch.Subset where
open import Level renaming (zero to lzero; suc to lsuc)

open import Relation.Unary using (Pred; Satisfiable) renaming (Decidable to Dec₁)
open import Relation.Binary renaming (Decidable to Dec₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_; refl; cong; sym; trans; subst₂)
open Eq.≡-Reasoning
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base as ℕ using (ℕ;_+_;_∸_;suc;zero; _<_)
open import Data.Bool using (not; Bool)
open import Data.Bool.Properties hiding (_≟_)
open import Data.Product
open import Data.Sum renaming ([_,_] to _⊞_)
open import Data.Vec hiding (allFin)
open import Data.Vec.Properties
open import Data.Fin.Properties using (∃-toSum)
open import Data.Fin hiding (fold; _+_; _<_)
  renaming (zero to fzero ; suc to fsuc)
  hiding (_≟_)

open import Relation.Nullary.Negation using (contradiction)

open import Data.Fin.Properties using (suc-injective)
open import Data.Fin.Subset
open import Data.Fin.Subset.Properties
open import Data.Maybe
open import Data.List.Base renaming (tabulate to tab ;
                                     foldr to fold;
                                     [] to <>;
                                     [_] to <_>;
                                     map to lmap;
                                     lookup to llookup)
                           hiding (tail; any)
open import Data.List.Properties
open import Data.List.Membership.Propositional
  renaming (_∈_ to _∈ℓ_)
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any as Any hiding (tail)
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.AllPairs as AllPairs
open import Data.List.Relation.Unary.AllPairs.Properties


open import Function.Base

open import Relation.Nullary

open import Data.Nat.Properties
  using (_≟_; m+n∸m≡n; +-∸-assoc; +-∸-comm; +-comm; +-identityʳ; 0∸n≡0; n≤0⇒n≡0; n≢0⇒n>0; +-0-commutativeMonoid)

open import Algebra.Core
import Algebra.Properties.BooleanAlgebra

_\\_ : ∀ {n} → Op₂ (Subset n)
S \\ T = S ∩ (∁ T)

s\\⊥≡s : ∀ {n : ℕ} → (S : Subset n) → (S \\ ⊥) ≡ S
s\\⊥≡s {n} S = begin
              S ∩ (∁ ⊥) ≡⟨ cong (S ∩_) ⊥≉⊤  ⟩
              S ∩ ⊤ ≡⟨ ∩-identityʳ _ ⟩
              S ∎ where open Algebra.Properties.BooleanAlgebra (∪-∩-booleanAlgebra n)

Disj : ∀ {n} → Subset n → Subset n → Set
Disj S T = S ∩ T ≡ ⊥

Disj-sym : ∀ {n} → Symmetric (Disj {n = n})
Disj-sym {n} {S} {T} S∩T≡⊥ = begin T ∩ S ≡⟨ ∩-comm T S ⟩ S ∩ T ≡⟨ S∩T≡⊥ ⟩ ⊥ ∎

∩-⊆-stable : ∀ {n} → ∀ {p q} → (r : Subset n) → p ⊆ q → (p ∩ r) ⊆ (q ∩ r)
∩-⊆-stable {_} {p} {q} r p⊆q x∈p∩r = let
                                     x∈p = proj₁ (x∈p∩q⁻ p r x∈p∩r)
                                     x∈r = proj₂ (x∈p∩q⁻ p r x∈p∩r)
                                     in x∈p∩q⁺ ( p⊆q x∈p , x∈r )

idʳ⇒⊆ : ∀ {n} → (S T : Subset n) → (S ∪ T) ≡ T → S ⊆ T
idʳ⇒⊆ {n} S T sut≡t = subst₂ _⊆_ refl sut≡t (p⊆p∪q T)

p∩∁p≡⊥ : ∀ {n} → (p : Subset n) → p ∩ ∁ p ≡ ⊥
p∩∁p≡⊥ [] = refl
p∩∁p≡⊥ (outside ∷ p) = cong (outside ∷_) (p∩∁p≡⊥ p)
p∩∁p≡⊥ (inside ∷ p) = cong (outside ∷_) (p∩∁p≡⊥ p)

p⊆q⇒p∩∁q≡⊥ : ∀ {n} → {S T : Subset n} → S ⊆ T → S ∩ (∁ T) ≡ ⊥
p⊆q⇒p∩∁q≡⊥ {_} {S} {T} s⊆t = let
                               a = p∩∁p≡⊥ _
                               b : S ∩ (∁ T) ⊆ T ∩ (∁ T)
                               b = ∩-⊆-stable (∁ T) s⊆t
                               c = subst₂ _⊆_ refl a b
                               in ⊆-antisym c (⊆-min _)

p⊆q⇒p∩q≡p : ∀ {n} → (S T : Subset n) → S ⊆ T → S ∩ T ≡ S
p⊆q⇒p∩q≡p S T s⊆t = sym (begin
                  S ≡˘⟨ ∩-identityʳ _ ⟩
                  S ∩ ⊤ ≡˘⟨ cong (_ ∩_) (p∪∁p≡⊤ _) ⟩
                  S ∩ (T ∪ (∁ T)) ≡⟨ ∩-distribˡ-∪ _ _ _ ⟩
                  (S ∩ T) ∪ (S ∩ (∁ T)) ≡⟨ cong ((S ∩ T) ∪_) (p⊆q⇒p∩∁q≡⊥ s⊆t)  ⟩
                  (S ∩ T) ∪ ⊥ ≡⟨ ∪-identityʳ _ ⟩
                  S ∩ T ∎)


disj⇒⊆∁ : ∀ {n} → {S T : Subset n} → Disj S T → S ⊆ (∁ T)
disj⇒⊆∁ {n} {S} {T} dst = let ct≡suct = begin
                                  ∁ T ≡˘⟨ ∪-identityˡ _ ⟩
                                  ⊥ ∪ (∁ T) ≡˘⟨ cong (_∪ (∁ T)) dst ⟩
                                  (S ∩ T) ∪ (∁ T) ≡⟨ ∪-distribʳ-∩ _ _ _ ⟩
                                  (S ∪ (∁ T)) ∩ (T ∪ (∁ T)) ≡⟨ cong ((S ∪ (∁ T)) ∩_) (p∪∁p≡⊤ T) ⟩
                                  (S ∪ (∁ T)) ∩ ⊤ ≡⟨ ∩-identityʳ _ ⟩
                                  S ∪ (∁ T) ∎
                  in idʳ⇒⊆ S (∁ T) (sym ct≡suct)

⊆∁⇒disj : ∀ {n} → {S T : Subset n} → S ⊆ (∁ T) → Disj S T
⊆∁⇒disj {n} {S} {T} s⊆∁t = begin
                         S ∩ T ≡˘⟨ cong (S ∩_) (¬-involutive T ) ⟩
                         S ∩ (∁ (∁ T)) ≡⟨ p⊆q⇒p∩∁q≡⊥ s⊆∁t ⟩
                         ⊥ ∎ where open Algebra.Properties.BooleanAlgebra (∪-∩-booleanAlgebra n)

p⊆r×q⊆r⇒p∪q⊆r : ∀ {n} → { p q r : Subset n} → (p ⊆ r) × (q ⊆ r) → (p ∪ q) ⊆ r
p⊆r×q⊆r⇒p∪q⊆r {n} {p} {q} {r} (p⊆r , q⊆r) x∈p∪q = let
                                                    y = x∈p∪q⁻ {n} p q x∈p∪q
                                                    in (p⊆r ⊞ q⊆r) y

pᵢ⊆q⇒⋃pᵢ⊆q : ∀ {n m} → (S : Subset n) → (ϕ : Fin m → Subset n) →
             (∀ i → (ϕ i) ⊆ S) → (⋃ (tab ϕ) ⊆ S)

pᵢ⊆q⇒⋃pᵢ⊆q {_} {zero} S _ _ = ⊆-min S
pᵢ⊆q⇒⋃pᵢ⊆q {n} {suc m} S ϕ Δ = let
                        y : ((ϕ fzero) ∪ (⋃(tab (ϕ ∘ fsuc)))) ⊆ S
                        y = p⊆r×q⊆r⇒p∪q⊆r ( Δ fzero , pᵢ⊆q⇒⋃pᵢ⊆q S (λ z → ϕ (fsuc z)) (λ i → Δ (fsuc i)) )
                        in subst₂ _⊆_ refl refl y

pᵢ⊆q⇒⋃pᵢ⊆q-list : ∀ {n} → ∀ S → ∀ (L : List (Subset n)) →
                  All (_⊆ S) L → (⋃ L) ⊆ S
pᵢ⊆q⇒⋃pᵢ⊆q-list S <> _ = ⊆-min S
pᵢ⊆q⇒⋃pᵢ⊆q-list S (x ∷ xs) (h ∷ t) = subst₂ _⊆_ refl refl (p⊆r×q⊆r⇒p∪q⊆r ( h , pᵢ⊆q⇒⋃pᵢ⊆q-list S xs t ))

-- obvious but exposes S for computation later
drop-outside : ∀ {n} → (S : Subset n) → ∣ outside ∷ S ∣ ≡ ∣ S ∣
drop-outside S = refl

drop-disj : ∀ {n} → {x y : Side} → {p q : Subset n} → Disj (x ∷ p) (y ∷ q) → Disj p q
drop-disj {zero} {_} {_} {[]} {[]} _ = refl
drop-disj d = cong Data.Vec.tail d

∣p⊍q∣≡∣p∣+∣q∣ : ∀ {n} → ∀ (p q : Subset n) → Disj p q → ∣ p ∪ q ∣ ≡ ∣ p ∣ + ∣ q ∣
∣p⊍q∣≡∣p∣+∣q∣ {zero} [] [] d = refl
∣p⊍q∣≡∣p∣+∣q∣ {suc n} (outside ∷ p) (outside ∷ q) d = begin
                                                        -- ∣ (outside ∷ p) ∪ (outside ∷ q) ∣ ≡⟨⟩
                                                        ∣ p ∪ q ∣ ≡⟨ ∣p⊍q∣≡∣p∣+∣q∣ {_} p q (drop-disj {n} {outside} {outside} d) ⟩
                                                        -- ∣ p ∣ + ∣ q ∣ ≡⟨⟩
                                                        ∣ (outside ∷ p) ∣ + ∣ (outside ∷ q) ∣ ∎

∣p⊍q∣≡∣p∣+∣q∣ {suc n} (inside ∷ p) (outside ∷ q) d = begin -- {!   !} -- begin
                                                        ∣ (inside ∷ p) ∪ (outside ∷ q) ∣ ≡⟨ refl ⟩ -- cong suc refl ⟩
                                                        -- suc ∣ (inside ∷ p) ∪ (outside ∷ q) ∣ ≡⟨ cong suc {!   !} ⟩ -- cong suc refl ⟩
                                                        suc ∣ p ∪ q ∣ ≡⟨ cong suc (∣p⊍q∣≡∣p∣+∣q∣ {_} p q (drop-disj {n} {inside} {outside} d)) ⟩
                                                        suc (∣ p ∣ + ∣ q ∣) ≡⟨⟩
                                                        (suc ∣ p ∣) + ∣ q ∣ ≡⟨⟩
                                                        ∣ (inside ∷ p) ∣ + ∣ (outside ∷ q) ∣ ∎
∣p⊍q∣≡∣p∣+∣q∣ {suc n} (outside ∷ p) (inside ∷ q) d = begin
                                                        ∣ (outside ∷ p) ∪ (inside ∷ q) ∣ ≡⟨ refl ⟩
                                                        suc ∣ p ∪ q ∣ ≡⟨ cong suc (∣p⊍q∣≡∣p∣+∣q∣ {_} p q (drop-disj {n} {outside} {inside} d)) ⟩
                                                        suc (∣ p ∣ + ∣ q ∣) ≡⟨ cong suc (+-comm ∣ p ∣ ∣ q ∣) ⟩
                                                        suc (∣ q ∣ + ∣ p ∣) ≡⟨ refl ⟩
                                                        (suc ∣ q ∣) + ∣ p ∣ ≡⟨⟩
                                                        ∣ (inside ∷ q) ∣ + ∣ (outside ∷ p) ∣ ≡⟨ +-comm ∣ (inside ∷ q) ∣ ∣ (outside ∷ p) ∣ ⟩
                                                        ∣ (outside ∷ p) ∣ + ∣ (inside ∷ q) ∣ ∎

-- why can't we use fold fusion here?
∣⋃ᵢpᵢ∣≡Σᵢ∣pᵢ∣ : ∀ {n m} → (ϕ : Fin m → Subset n) →
                (∀ i j → (i ≢ j) → Disj (ϕ i) (ϕ j)) →
                ∣ ⋃ (tab ϕ) ∣ ≡ fold _+_ 0 (tab (∣_∣ ∘ ϕ))
∣⋃ᵢpᵢ∣≡Σᵢ∣pᵢ∣ {n} {zero} ϕ _ = begin
                                 ∣ ⋃ {n} <> ∣ ≡⟨⟩
                                 -- ∣ fold (_∪_ {n}) ⊥ <> ∣ ≡⟨⟩
                                 ∣ ⊥ {n} ∣ ≡⟨ ∣⊥∣≡0 n ⟩
                                 0 ≡⟨⟩
                                 fold _+_ 0 <> ∎
∣⋃ᵢpᵢ∣≡Σᵢ∣pᵢ∣ {n} {suc m} ϕ Δ = begin
                                  ∣ ⋃ (tab ϕ) ∣ ≡⟨⟩
                                  ∣ (ϕ fzero) ∪ (⋃ (tab (ϕ ∘ fsuc))) ∣ ≡⟨ ∣p⊍q∣≡∣p∣+∣q∣ (ϕ fzero) (⋃ (tab (ϕ ∘ fsuc))) d ⟩
                                  ∣ (ϕ fzero) ∣ + ∣ ⋃ (tab (ϕ ∘ fsuc)) ∣ ≡⟨ cong (∣ (ϕ fzero) ∣ +_) (∣⋃ᵢpᵢ∣≡Σᵢ∣pᵢ∣ {_} {m} (ϕ ∘ fsuc) λ i j i≢j → Δ (fsuc i) (fsuc j) (i≢j ∘ suc-injective) ) ⟩
                                  ∣ (ϕ fzero) ∣ + (fold _+_ 0 (tab (∣_∣ ∘ (ϕ ∘ fsuc)))) ≡⟨⟩
                                  fold _+_ 0 (tab (∣_∣ ∘ ϕ)) ∎
                                  where
                                  a : ∀ (i : Fin m) → Disj (ϕ (fsuc i)) (ϕ fzero)
                                  a = λ i → Δ (fsuc i) fzero (λ ())
                                  b : ∀ (i : Fin m) → (ϕ (fsuc i) ⊆ ∁ (ϕ fzero))
                                  b = disj⇒⊆∁ ∘ a
                                  c : ⋃ (tab (ϕ ∘ fsuc)) ⊆ ∁ (ϕ fzero)
                                  c = pᵢ⊆q⇒⋃pᵢ⊆q (∁ (ϕ fzero)) (ϕ ∘ fsuc) b

                                  e : Disj (⋃ (tab (ϕ ∘ fsuc))) (ϕ fzero)
                                  e = ⊆∁⇒disj c

                                  d : Disj (ϕ fzero) (⋃ (tab (ϕ ∘ fsuc)))
                                  d = begin
                                        (ϕ fzero) ∩ (⋃ (tab (ϕ ∘ fsuc))) ≡⟨ ∩-comm _ _ ⟩
                                        (⋃ (tab (ϕ ∘ fsuc))) ∩ (ϕ fzero) ≡⟨ e ⟩
                                        ⊥ ∎

∣⋃ᵢpᵢ∣≡Σᵢ∣pᵢ∣-list : ∀ {n} (C : List (Subset n)) →
                     AllPairs Disj C →
                     ∣ ⋃ C ∣ ≡ fold _+_ 0 (lmap ∣_∣ C)
∣⋃ᵢpᵢ∣≡Σᵢ∣pᵢ∣-list {n} <> Δℓ = begin
                             ∣ ⋃ {n} <> ∣ ≡⟨⟩
                             -- ∣ fold (_∪_ {n}) ⊥ <> ∣ ≡⟨⟩
                             ∣ ⊥ {n} ∣ ≡⟨ ∣⊥∣≡0 n ⟩
                             0 ≡⟨⟩
                             fold _+_ 0 <> ∎
∣⋃ᵢpᵢ∣≡Σᵢ∣pᵢ∣-list {n} (s ∷ C) (h ∷ t) = begin
                                  ∣ ⋃ (s ∷ C) ∣ ≡⟨⟩
                                  ∣ s ∪ (⋃ C) ∣ ≡⟨ ∣p⊍q∣≡∣p∣+∣q∣ s (⋃ C) DisjsUC ⟩
                                  ∣ s ∣ + ∣ ⋃ C ∣ ≡⟨ cong (∣ s ∣ +_) (∣⋃ᵢpᵢ∣≡Σᵢ∣pᵢ∣-list {n} C t ) ⟩
                                  ∣ s ∣ + (fold _+_ 0 (lmap ∣_∣ C)) ≡⟨⟩
                                  fold _+_ 0 (lmap ∣_∣ (s ∷ C)) ∎
                                  where
                                  a : All (λ x → x ⊆ ∁ s) C
                                  a = All.map (disj⇒⊆∁ ∘ Disj-sym) h
                                  c : ⋃ C ⊆ ∁ s
                                  c = pᵢ⊆q⇒⋃pᵢ⊆q-list (∁ s) C a
                                  e : Disj (⋃ C) s
                                  e = ⊆∁⇒disj c
                                  DisjsUC : Disj s (⋃ C)
                                  DisjsUC = Disj-sym e

⋃-remove : ∀ {n} {L : List (Subset n)} →
           ∀ s → (s∈L : s ∈ℓ L) →
           (⋃ L) ≡ s ∪ ⋃ (L Any.─ s∈L)
⋃-remove {n} {<>} _ = λ ()
⋃-remove {n} {x ∷ xs} s (here px) = begin
                                      ⋃ (x ∷ xs) ≡⟨ refl ⟩
                                      x ∪ (⋃ xs) ≡˘⟨ cong (_∪ _) px ⟩
                                      s ∪ (⋃ xs) ≡⟨ cong (_ ∪_) refl ⟩
                                      s ∪ ⋃ ((x ∷ xs) Data.List.Base.─ fzero ) ≡⟨ cong (_ ∪_) refl ⟩
                                      s ∪ ⋃ ((x ∷ xs) Any.─ (here {P = P} px)) ∎
                                      where
                                      P : Pred (Subset n) lzero
                                      P = s ≡_

⋃-remove {n} {x ∷ xs} s (there s∈L) = begin
                                        x ∪ (⋃ xs) ≡⟨ cong (x ∪_) (⋃-remove {L = xs} s s∈L) ⟩
                                        x ∪ (s ∪ ⋃ (xs Any.─ s∈L)) ≡˘⟨ ∪-assoc _ _ _ ⟩ -- TODO: -- use solver
                                        (x ∪ s) ∪ ⋃ (xs Any.─ s∈L) ≡⟨ cong (_∪ _) (∪-comm x s) ⟩
                                        (s ∪ x) ∪ ⋃ (xs Any.─ s∈L) ≡⟨ ∪-assoc _ _ _ ⟩
                                        s ∪ (x ∪ ⋃ (xs Any.─ s∈L)) ≡⟨ refl ⟩
                                        s ∪ ⋃ ((x ∷ xs) Any.─ (there s∈L)) ∎

cover-⊤ : ∀ {n} → (L : List (Subset n)) →
          (∀ (x : Fin n) → Any (x ∈_) L ) →
          ⊤ {n} ≡ ⋃ L

cover-⊤ {n} L ∃lx∈l = ⊆-antisym ⊤⊆⋃L (⊆-max (⋃ L)) where
  ⊤⊆⋃L : ⊤ ⊆ (⋃ L)
  ⊤⊆⋃L {x} _ = let
                  (l , l∈ℓL , x∈l) = find {P = x ∈_} (∃lx∈l x)
                  l⊆l∪* = p⊆p∪q {p = l} (⋃ (L Any.─ l∈ℓL))
                  x∈l∪* = l⊆l∪* {x} x∈l
                in subst₂ _∈_ refl (sym (⋃-remove l l∈ℓL)) x∈l∪*

-- 👇 not essential

|s\\t| : ∀ {n : ℕ} → ∀ {S T : Subset n} → T ⊆ S → ∣ S \\ T ∣ ≡ ∣ S ∣ ∸ ∣ T ∣
|s\\t| {.0} {[]} {T} t⊆s = begin
                              ∣ [] \\ T ∣ ≡⟨ n≤0⇒n≡0 (∣p∩q∣≤∣p∣ [] (∁ T)) ⟩
                              0 ≡˘⟨ 0∸n≡0 ∣ T ∣ ⟩
                              ∣ [] ∣ ∸ ∣ T ∣
                              ∎
|s\\t| {.(suc _)} {inside ∷ S} {inside ∷ T} t⊆s = |s\\t| {_} {S} {T} (drop-∷-⊆ t⊆s)
|s\\t| {.(suc _)} {outside ∷ S} {outside ∷ T} t⊆s = |s\\t| {_} {S} {T} (drop-∷-⊆ t⊆s)
|s\\t| {.(suc _)} {outside ∷ S} {inside ∷ T} t⊆s = let z = (t⊆s here)
                                                       y = []=⇒lookup z
                                                       w = not-¬ y
                                                     in ⊥-elim (w refl)
|s\\t| {(suc n)} {inside ∷ S} {outside ∷ T} t⊆s = sym (begin
                                                        ∣ inside ∷ S ∣ ∸ ∣ outside ∷ T ∣ ≡⟨ refl ⟩
                                                        (suc ∣ S ∣) ∸ ∣ outside ∷ T ∣ ≡⟨ cong ((suc ∣ S ∣) ∸_) (drop-outside T) ⟩
                                                        (1 + ∣ S ∣) ∸ ∣ T ∣ ≡⟨ cong (_∸ ∣ T ∣) (Data.Nat.Properties.+-comm _ ∣ S ∣)⟩
                                                        (∣ S ∣ + 1) ∸ ∣ T ∣ ≡⟨ +-∸-comm  1 (p⊆q⇒∣p∣≤∣q∣ (drop-∷-⊆ {n} {_} {_} {T} {S} t⊆s)) ⟩
                                                        (∣ S ∣ ∸ ∣ T ∣) + 1 ≡⟨ Data.Nat.Properties.+-comm (∣ S ∣ ∸ ∣ T ∣) _ ⟩
                                                        (suc (∣ S ∣ ∸ ∣ T ∣)) ≡˘⟨ cong suc  (|s\\t| {n} {S} {T} (drop-∷-⊆ {n} t⊆s))⟩
                                                        (suc ∣ S \\ T ∣) ≡⟨ refl ⟩
                                                        ∣ (inside ∷ S) \\ (outside ∷ T) ∣ ∎)

fst : ∀ {n} → (s : Subset n) → Nonempty s → Fin n
fst {suc n} (x ∷ rest) ne with (∃-toSum ne)
... | inj₁ _ = fzero
... | inj₂ b = let w = drop-there (proj₂ b)
                   z = (proj₁ b , w)
               in fsuc (fst rest z)


record Partition (n : ℕ) : Set where
  field
    Carrier : Subset n
    size : ℕ
    -- try parts as Data.Vec.Functional
    -- or try parts as List (Subset n) for ease of updates
    parts : Fin size → Subset n
    -- nne : 0 ℕ.< m
    nnd : ∀ i → Nonempty (parts i)
    all-⊆ : ∀ i → (parts i) ⊆ Carrier
    disj : ∀ i j → i ≢ j → Disj (parts i) (parts j)
    cover : Carrier ≡ ⋃ (tab parts)

  traversal : Vec (Fin n) size
  traversal = Data.Vec.tabulate λ i → fst (parts i) (nnd i)

  _P∈ : (j : Fin n) → Dec ( j ∈ Carrier )
  j P∈ = (j ∈? Carrier)

  -- open import Data.Vec.Relation.Unary.Any {0ℓ} {Fin n}
  -- anyRel : {_≈_ : Rel (Fin n) 0ℓ } → Dec₂ _≈_ → (j : Fin n) → Dec (Any (j ≈_) traversal)
  -- anyRel _≈?_ j = any (j ≈?_) traversal

  -- do I need this for counting arguments?
  respects : Rel (Fin n) 0ℓ → Set _
  respects _≈_ = ∀ x y → x ≈ y → ∃ λ i → (x ∈ parts i) × (y ∈ parts i)

  -- proj i = index (proof anyRel ≈ j)
  -- ∀ i → tabulate (i ≈?_) ≡ proj i

⊥P : ∀ {n} → Partition n
⊥P {n} = record { Carrier = ⊥ {n} ;
                  size = 0 ;
                  parts = λ () ;
                  all-⊆ = λ () ;
                  nnd = λ () ;
                  disj = λ i () ;
                  cover = refl }

------ has holes
-- add : ∀ {n} {≈ : Rel (Fin n) 0ℓ } → Partition n → (Dec₂ ≈) → Fin n → Partition n
-- add P ≈ j with (j P∈) where open Partition P
-- ... | yes _ = P
-- ... | no j∉P with (anyRel ≈ j) where open Partition P
-- ... | yes p = {!   !}
-- ... | no ¬p = record { Carrier = Carrier ∪ ⁅ j ⁆ ;
--                        size = suc size ;
--                        parts = λ { fzero → ⁅ j ⁆ ;
--                                    (fsuc k) → parts k } ;
--                        nnd = {!   !} ;
--                        all-⊆ = {!   !} ;
--                        disj = {!   !} ;
--                        cover = {!   !}
--                        } where open Partition P


----junk👇--------------------------------------------------------
-- ↓ : ∀ {n m : ℕ} → ∀ {S : Subset n} → ( 0 < m ) →
--      (P : Partition S (suc m)) → Partition (S \\ Partition.p P fzero) m
-- ↓ {_} {m} {S} 0<m P = record { p = p∘fsuc;
--                                nne = 0<m ;
--                                nnd = λ i → Partition.nnd P (fsuc i) ;
--                                all-⊆ = all-⊆' ;
--                                disj = disj' ;
--                                cover = c } where
--                              open Partition P
--                              p∘fsuc : _
--                              p∘fsuc = p ∘ fsuc
--
--                              all-⊆' : ∀ (i : Fin m) → (p (fsuc i)) ⊆ (S \\ (p fzero))
--                              all-⊆' i x∈pfsuci = let
--                                           x : _
--                                           x = all-⊆ (fsuc i)
--                                           y : Disj (p (fsuc i)) (p fzero)
--                                           y = disj (fsuc i) fzero λ ()
--                                           -- x ∈ (S \\ p fzero)
--                                           r : _
--                                           r = disj⇒⊆∁ {_} {p (fsuc i)} {p fzero} y
--                                           s : _
--                                           s = Partition.all-⊆ P (fsuc i) x∈pfsuci
--                                           t : _
--                                           t = r x∈pfsuci
--                                          in x∈p∩q⁺ ( s , t )
--
--                              disj' : _
--                              disj' i j i≢j = disj (fsuc i) (fsuc j) (i≢j ∘ suc-injective)
--
--                              c : _
--                              c = let
--                                     a : _
--                                     a = cover
--                                     b : _
--                                     b = S ≡ (p fzero) ∪ (⋃ (tab p∘fsuc))
--                                     S₀ = (p fzero)
--                                     d = begin
--                                           S \\ S₀ ≡⟨ cong (_\\ S₀) (Partition.cover P) ⟩
--                                           (⋃ (S₀ ∷ (tab p∘fsuc))) \\ S₀ ≡⟨ cong (_\\ S₀) refl ⟩
--                                           (S₀ ∪ (⋃ (tab p∘fsuc))) \\ S₀    ≡⟨ refl ⟩
--                                           (S₀ ∪ (⋃ (tab p∘fsuc))) ∩ (∁ S₀) ≡⟨ ∩-distribʳ-∪ _ _ _ ⟩
--                                           (S₀ ∩ (∁ S₀)) ∪ ((⋃ (tab p∘fsuc)) ∩ (∁ S₀)) ≡⟨ cong (_∪ ((⋃ (tab p∘fsuc)) ∩ (∁ S₀))) (p∩∁p≡⊥ _) ⟩
--                                           ⊥ ∪ ((⋃ (tab p∘fsuc)) ∩ (∁ S₀)) ≡⟨ ∪-identityˡ _ ⟩
--                                           (⋃ (tab p∘fsuc)) ∩ (∁ S₀) ≡⟨ {!   !} ⟩
--                                           (⋃ (tab p∘fsuc)) -- ≡⟨ ? ⟩
--                                           ∎
--                                     t = {!   !}
--                                  in t
--
-- this seems pretty obvious but helps rule out case with a single set below
-- tab0 : ∀ {m : ℕ} → ∀ {B : Set} → {ϕ : Fin (suc m) → B} → (m ≡ ℕ.zero) → (tab ϕ) ≡ < ϕ fzero >
-- tab0 {zero} m≡0 = refl
--
-- would follow trivially from a kind of guarded (dependent)
-- fold fusion with h = ∣_∣ f = _∪_ and g = _+c_
-- cc : ∀ {n m : ℕ} → {S : Subset n} →
--      ∀ (P : Partition S m) → (card P) ≡ ∣ S ∣
-- cc {n} {m = suc m'} {S} P with m' ≟ 0
-- ... | yes m'≡0 = begin
--                   (card P) ≡⟨ refl ⟩
--                   fold _+c_ 0 (tab p) ≡⟨ cong (fold _+c_ 0) (tab0 {m'} {Subset n} {p} m'≡0) ⟩
--                   fold _+c_ 0 < p fzero > ≡⟨ refl ⟩
--                   (p fzero) +c 0  ≡⟨ refl ⟩
--                   -- (p fzero) +c (fold _+c_ 0 <>) ≡⟨ refl ⟩
--                   -- fold _+c_ 0 ((p fzero) ∷ <>) ≡⟨ refl ⟩
--                   ∣ (p fzero) ∣ + 0 ≡⟨ +-identityʳ _ ⟩
--                   ∣ (p fzero) ∣ ≡˘⟨ cong ∣_∣ (∪-identityʳ (p fzero)) ⟩
--                   ∣ (p fzero) ∪ ⊥ ∣ ≡˘⟨ refl ⟩
--                   ∣ ⋃ < (p fzero) > ∣ ≡˘⟨ cong ∣_∣ (cong ⋃ (tab0 {m'} {Subset n} {p} m'≡0)) ⟩
--                   ∣ ⋃ (tab p) ∣ ≡˘⟨ cong ∣_∣ cover ⟩
--                   ∣ S ∣ ∎ where
--                   open Partition P
--
-- ... | no ¬m'≡0 = begin
--               (card P) ≡⟨⟩
--               fold _+c_ 0 ((p fzero) ∷ tab (p ∘ fsuc))  ≡⟨⟩
--               (p fzero) +c (fold _+c_ 0 (tab (p ∘ fsuc))) ≡⟨⟩
--               ∣ (p fzero) ∣ + (fold _+c_ 0 (tab (p ∘ fsuc))) ≡˘⟨ cong (∣ (p fzero) ∣ +_) refl ⟩
--               ∣ (p fzero) ∣ + card (↓ r P) ≡⟨ cong (_ +_) (cc (↓ r P)) ⟩
--               ∣ (p fzero) ∣ + ∣ S \\ (p fzero) ∣ ≡⟨ cong (_ +_) (|s\\t| (all-⊆ fzero)) ⟩
--               ∣ (p fzero) ∣ + ( ∣ S ∣ ∸ ∣ (p fzero) ∣ ) ≡˘⟨ +-∸-assoc ∣ (p fzero) ∣ (p⊆q⇒∣p∣≤∣q∣ (all-⊆ fzero)) ⟩
--               (∣ (p fzero) ∣ + ∣ S ∣) ∸ ∣ (p fzero) ∣ ≡⟨ m+n∸m≡n ∣ (p fzero) ∣ ∣ S ∣ ⟩
--               ∣ S ∣ ∎ where
--              open Partition P
--              r = (n≢0⇒n>0 ¬m'≡0)
