module Scratch.FinDecEq1 where

open import Data.Bool.Base hiding (_≤_)
open import Data.Product
open import Data.Sum
open import Level renaming (suc to lsuc; _⊔_ to _⊔ℓ_)
                  hiding (zero)

open import Relation.Nullary
open import Relation.Nullary.Decidable

-- open import Relation.Unary renaming (Decidable to DecP)
--                            hiding (_∈_)
open import Relation.Binary

open import Function.Base
-- open import Function.Bijection hiding (_∘_)
-- open import Function.Equality hiding (≡-setoid; _∘_)

open import Data.Nat.Base hiding (_≤_)
open import Data.Fin renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties hiding (to-from)
-- see http://firsov.ee/finset/finset.pdf

open import Data.List.Base renaming (tabulate to tab;
                                     lookup to nth;
                                     map to lmap;
                                     filter to lfilter;
                                     allFin to allF)
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Setoid.Properties

open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

open import Scratch.Subset

-- record StronglyFiniteSetoid (n : ℕ) : Set (lsuc (c ⊔ℓ ℓ)) where
--   field
--     S : Setoid c ℓ
--     χ : Bijection (≡-setoid n) S
--
--   open Setoid S
--   open Bijection χ
--   open Π to renaming (_⟨$⟩_ to to')
--   open Π from renaming (_⟨$⟩_ to from')
--
--   ι : Fin n → Carrier
--   ι x = to' x
--
--   ρ : Carrier → Fin n
--   ρ y = from' y

  -- TODO: pullback of ω where ω ≤ _≈_ (see orbital relation)
  -- /Users/amantini/dev/agda/agda-stdlib/README/Data/Interleaving.agda
  -- if ω is decidable then the pullback is a FinDecEq

  -- partition FinDecEq n → Vec (Subset n)
  --
open import Data.Vec hiding (length)
                     renaming (lookup to vlookup)
open import Data.Vec.Properties
-- open import Data.Vec.Relation.Unary.Any
open import Data.Fin.Subset
open import Data.Fin.Subset.Properties

fsuc∈ : ∀ {n} → { p : Subset n} → {x : Fin n} → {s : Side} → (x ∈ p) → (fsuc x) ∈ (s ∷ p)
fsuc∈ here = there here
fsuc∈ (there x∈p) = there (fsuc∈ x∈p)

fst₊ : ∀ {n} → (s : Subset n) → Nonempty s → Σ (Fin n) (λ x → ( x ∈ s × (∀ {y} → (y ∈ s) → x ≤ y )))
fst₊ {suc n} (inside ∷ rest) ne = ( fzero , here , λ _ → z≤n )
fst₊ {suc n} (outside ∷ rest) ne with (∃-toSum ne)
... | inj₂ b = let w = drop-there (proj₂ b)
                   z = (proj₁ b , w)
                   ( a , bb , c ) = (fst₊ rest z)
               in (fsuc a , fsuc∈ bb , λ { (there y∈s) → s≤s (c y∈s) } )

fst₋ : ∀ {n} → (s : Subset n) → Nonempty s → Fin n
fst₋ s ne = proj₁ (fst₊ s ne)

fst₋unique : ∀ {n} → ∀ (s t : Subset n) → (ns : Nonempty s) → (nt : Nonempty t) →
             s ≡ t → (fst₋ s ns) ≡ (fst₋ t nt)

fst₋unique s t ns nt s≡t = let fs , fs∈s , fs≤ = (fst₊ s ns)
                               ft , ft∈t , ft≤ = (fst₊ t nt)
                               ft∈s : ft ∈ s
                               ft∈s = subst _ (sym s≡t) ft∈t
                               fs∈t : fs ∈ t
                               fs∈t = subst _ s≡t fs∈s
                           in ≤-antisym (fs≤ ft∈s) (ft≤ fs∈t)

open import Data.Unit hiding (_≟_)
-- TODO: see src/Data/List/Membership/Setoid.agda
--       see src/Relation/Nullary/Decidable.agda

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl  =  tt

record FinDecEq {a} (n : ℕ) : Set (lsuc a) where
  field
    _ω_ : Rel (Fin n) a
    isDecEq : IsDecEquivalence _ω_

  std : DecSetoid _ _
  std = record { Carrier = (Fin n) ;
                _≈_ = _ω_ ;
                isDecEquivalence = isDecEq }



  open DecSetoid std
    renaming (_≟_ to _ω?_ ;
              refl to r ;
              sym to s ;
              trans to t ;
              Carrier to F;
              setoid to std')
    public

  [_]ω : (Fin n) → Subset n
  [ o ]ω = tabulate (does ∘ (_ω? o))
  -- TODO: use src/Data/List/Membership/Setoid.agda
  --       and src/Data/Fin/Subset/Properties.agda


  ω⇒∈ : ∀ {x y} → x ω y → x ∈ [ y ]ω
  ω⇒∈ {x} {y} xωy = let lkp = begin vlookup [ y ]ω x ≡⟨ lookup∘tabulate _ x ⟩
                               does (x ω? y) ≡⟨ dec-true (x ω? y) xωy ⟩
                               true ∎
               in lookup⇒[]= x [ y ]ω lkp

  -- in particular classes are not empty
  o∈[o]ω : ∀ { o : Fin n } → o ∈ [ o ]ω
  o∈[o]ω = ω⇒∈ r

  -- and actually equal


  -- conversely
  ∈⇒ω : ∀ {x y} → x ∈ [ y ]ω → x ω y
  ∈⇒ω {x} {y} x∈[y] = let w = begin true ≡˘⟨ []=⇒lookup x∈[y] ⟩
                              vlookup [ y ]ω x ≡⟨ lookup∘tabulate _ x ⟩
                              does (x ω? y) ≡˘⟨ isYes≗does _ ⟩
                              isYes (x ω? y) ∎
                          r : True (x ω? y)
                          r = ≡→T (sym w)
                        in toWitness r

  ω⇒⊆ : ∀ {x y} → x ω y → [ x ]ω ⊆ [ y ]ω
  ω⇒⊆ {x} {y} xωy {s} s∈[x] = ω⇒∈ (t (∈⇒ω s∈[x]) xωy )

  ω⇒≡ : ∀ {x y} → x ω y → [ x ]ω ≡ [ y ]ω
  ω⇒≡ {x} {y} xωy = ⊆-antisym (ω⇒⊆ xωy) (ω⇒⊆ (s xωy))

  -- canonical choice - TODO
  c : F → F
  c f = fst₋ {n} [ f ]ω ( f , o∈[o]ω )

  --
  cx∈[x] : ∀ (x : Fin n) → (c x) ∈ [ x ]ω
  cx∈[x] x = proj₁ (proj₂ (fst₊ [ x ]ω ( x , o∈[o]ω )))

  xωcx : ∀ (x : F) → x ω (c x)
  xωcx x = s (∈⇒ω (cx∈[x] x))
  --
  c⇒ω : ∀ {x y} → c x ≡ c y → x ω y
  c⇒ω {x} {y} cx≡cy = let P = λ q → q ∈ [ y ]ω
                          w : (c x) ∈ [ y ]ω
                          w = subst P (sym cx≡cy) (cx∈[x] y)
                      in t (xωcx x) (∈⇒ω w)
  --
  ω⇒c : ∀ {x y} → x ω y → c x ≡ c y
  ω⇒c {x} {y} xωy = fst₋unique _ _ _ _ (ω⇒≡ xωy)

  c-idempt : (x : F) → c (c x) ≡ c x
  c-idempt x = ω⇒c {c x} {x} (s (xωcx x))

  ω-disj : ∀ {x y} → ¬ (x ω y) → Empty ([ x ]ω ∩ [ y ]ω)
  ω-disj {x} {y} ¬xωy f∈∩ = let f , [x]∩[y] = f∈∩
                                l , r = x∈p∩q⁻ _ _ [x]∩[y]
                                fωx : f ω x
                                fωx = ∈⇒ω l
                                fωy = ∈⇒ω r
                            in ¬xωy (t (s fωx) fωy)

  ω-Disj : ∀ {x y} → ¬ (x ω y) → Disj [ x ]ω [ y ]ω
  ω-Disj ¬xωy = Empty-unique (ω-disj ¬xωy)

  -- canonical representative
  cr : (i : F) → Set
  cr i = i ≡ (c i)

  -- c' : (i : F) → cr i × i ω (c i)

  cr? : ∀ (i : F) → Dec (cr i)
  cr? = λ i → i ≟ (c i)

  cr-disj : (x : F) → (cr x) →
            (y : F) → (cr y) →
            x ≢ y → ¬ (x ω y)

  cr-disj x crx y cry x≢y xωy = let x≡y = begin x ≡⟨ crx ⟩
                                                c x ≡⟨ ω⇒c xωy ⟩
                                                c y ≡˘⟨ cry ⟩
                                                y ∎
                                in x≢y x≡y

  transversal : Subset n
  transversal = tabulate (does ∘ cr?)

  Tr : List F
  Tr = (lfilter cr? (allF n))

  C : List (Subset n)
  C = mapOn [_]ω transversal
  C' : List (Subset n)
  C' = Data.List.Base.map [_]ω (Data.List.Base.filter cr? (Data.List.Base.allFin n))

  C-cover : ∀ (j : F) → (∃ λ k → cr k × j ω k)
  C-cover j = (c j) , sym (c-idempt j) , xωcx j

  -- Pⱼ(k) = cr k × j ω k
  -- any-×⇒filter : ∀ {p q A} {P : A → Set p} {Q : A → Set q} →
  --                (Q? : Decidable Q) →
  --             Any (P × Q) xs → Any P (filter Q? xs)

  -- P = j ω_
  -- xs = allFin n ≃ (lookup (tab id) i) = i
  -- ∈ is propositional membership
  -- k ∈ xs → P k → Any P xs + lookup
  -- ∈-lookup : ∀ xs i → (lookup xs i) ∈ xs
  -- j ω k → Any (j ω_) (allFin n)

  -- P = cr k
  --

  C-cover1 : ∀ (j : F) → (∃ λ k → cr k × j ∈ [ k ]ω)
  C-cover1 j = (c j) , (sym (c-idempt j) , ω⇒∈ (xωcx j))

  resp : cr Respects _ω_
  resp {x} {y} xωy crx = {!   !}

  Tr-cover2 : ∀ (j : F) → Any (j ω_) Tr -- j ∈ω Tr
  Tr-cover2 j = ?
  -- use Any.gmap
  -- Tr-cover3 : ∀ (j : F) → Any (λ s → j ∈ S) (lmap [_]ω Tr)

  ϕ : Fin (length C) → Subset n
  ϕ j = nth C j

  ϕ-cover : ∀ (x : F) → (∃ λ s → x ∈ (ϕ s))
  ϕ-cover j = ( {!   !} , {!   !} )

  -- sub-cover : ∀ {m n} → (ϕ : Fin m → Subset n) →
  --             ∀ (x : Fin n) → (∃ λ s → x ∈ ϕ s) →
  --             ⊤ ≡ ⋃ (tab ϕ)
  -- sub-cover ϕ x ( j , x∈ϕj ) = {!   !}
  -- syntax ⋃[ i < n ] (ϕ i)

  -- sub-cover : ∀ {n} (L : List (Subset n)) →
                 -- ∀ (x : Fin n) → Any (λ s → x ∈ s) L →
                 -- ⊤ ≡ ⋃ L
  -- disj-⋃ : ∀ {n} (L : List (Subset n)) →
  --          ∀

  -- ⋃[x]ω : F ≡ ⋃ (Data.List.Base.map [_]ω (reify transversal))
  -- ⋃[x]ω = ?
