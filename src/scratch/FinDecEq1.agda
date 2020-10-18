module Scratch.FinDecEq1 where

open import Data.Bool.Base hiding (_≤_)
open import Data.Product
open import Data.Sum
open import Level renaming (suc to lsuc; _⊔_ to _⊔ℓ_; zero to lzero)

open import Relation.Nullary
open import Relation.Nullary.Decidable

open import Relation.Unary using (Decidable)
open import Relation.Binary hiding (Decidable)

open import Function.Base
-- open import Function.Bijection hiding (_∘_)
-- open import Function.Equality hiding (≡-setoid; _∘_)

open import Data.Nat.Base hiding (_≤_)
open import Data.Fin renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties hiding (to-from)
-- see http://firsov.ee/finset/finset.pdf

open import Data.List.Base renaming (tabulate to tab;
                                     lookup to nth;
                                     filter to lfilter;
                                     allFin to allF)
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
-- open import Data.List.Membership.Propositional renaming (_∈_ to _∈ℓ_)
-- open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any as Any -- hiding (tail)
open import Data.List.Relation.Unary.Any.Properties hiding (tabulate⁺)
open import Data.List.Relation.Unary.All as All hiding (tabulate)
open import Data.List.Relation.Unary.AllPairs as AllPairs
open import Data.List.Relation.Unary.AllPairs.Properties renaming (map⁺ to ap-map⁺)


-- :-( can't use Vector because it doesn't have a filter
-- open import Data.Vec.Functional as Coll
-- open import Data.Vec.Functional.Relation.Unary.Any
--   renaming (here to here'; there to there')

open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

open import Scratch.Data.List.Relation.Helpers
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

open import Data.Vec hiding (length)
                     renaming (lookup to vlookup)
open import Data.Vec.Properties
-- open import Data.Vec.Relation.Unary.Any
open import Data.Fin.Subset
open import Data.Fin.Subset.Properties

lmap = Data.List.Base.map
syntax lmap (λ x → B) L = ⟦ B ∣ x ∈ℓ L ⟧

fsuc∈ : ∀ {n} → { p : Subset n} → {x : Fin n} → {s : Side} → (x ∈ p) → (fsuc x) ∈ (s Data.Vec.∷ p)
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

open import Data.Unit hiding (_≟_; ⊤)
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

  import Data.List.Membership.Propositional
  module MP = Data.List.Membership.Propositional {A = F}
  open MP renaming (_∈_ to _∈ℓ_)
  -- open import Data.List.Membership.Propositional renaming (_∈_ to _∈ℓ_)
  open import Data.List.Membership.Propositional.Properties


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
  -- _≟_
  cr? : Decidable cr
  cr? = λ i → i ≟ (c i)

  cr-disj : ∀ {x y} → (cr x) → (cr y) → x ≢ y → ¬ (x ω y)
  cr-disj {x} {y} crx cry x≢y xωy = let x≡y = begin x ≡⟨ crx ⟩
                                                c x ≡⟨ ω⇒c xωy ⟩
                                                c y ≡˘⟨ cry ⟩
                                                y ∎
                                    in x≢y x≡y

  Tr : List F
  Tr = (lfilter cr? (allF n))

  -- ∈-filter⁻ : ∀ {v xs} → v ∈ filter P? xs → v ∈ xs × P v

  -- C : List (Subset n)
  -- C = ⟦ [ x ]ω ∣ x ∈ℓ Tr ⟧

  --  ap x≢y allF
  --  ap ¬ x ω y Tr
  --  ap Disj (map [_] Tr)

  ap1 : AllPairs _≢_ (allF n)
  ap1 = tabulate⁺ id
  ap2 : AllPairs (λ x y → ¬ x ω y) Tr
  ap2 = filter⁺⁺ cr? cr-disj ap1

  ap3 : AllPairs Disj ⟦ [ x ]ω ∣ x ∈ℓ Tr ⟧
  ap3 = ap-map⁺ (AllPairs.map ω-Disj ap2)

  C-cover' : ∀ (x : F) → (∃ λ k → cr k × x ω k)
  C-cover' x = (c x) , sym (c-idempt x) , xωcx x

  C-cover : ∀ (x : F) → Any (x ∈_) ⟦ [ x ]ω ∣ x ∈ℓ Tr ⟧
  C-cover x = let (k , crk , xωk) = C-cover' x
                  k∈ℓallF : k ∈ℓ allF n
                  k∈ℓallF = ∈-allFin {n} k
                  k∈ℓTr : k ∈ℓ Tr
                  k∈ℓTr = ∈-filter⁺ cr? k∈ℓallF crk
                  a : Any (x ω_) Tr
                  a = lose k∈ℓTr xωk
                  b : Any ((x ∈_) ∘ [_]ω) Tr
                  b = Any.map ω⇒∈ a
              -- map⁺ : Any (P ∘ f) xs → Any P (List.map f xs)
              in map⁺ b


  --
  []ω-cover : ⊤ ≡ ⋃ ⟦ [ x ]ω ∣ x ∈ℓ Tr ⟧
  []ω-cover = cover-⊤ ⟦ [ x ]ω ∣ x ∈ℓ Tr ⟧ C-cover

  -- Cardinality : n ≡ Data.List.Base.sum ⟦ ∣ [ x ]ω ∣ ∣ x ∈ℓ Tr ⟧
  -- Cardinality =
  --   let c = ∣⋃ᵢpᵢ∣≡Σᵢ∣pᵢ∣ ⟦ [ x ]ω ∣ x ∈ℓ Tr ⟧ ap3
  --       in begin
  --           n ≡˘⟨ ∣⊤∣≡n n ⟩
  --           ∣ ⊤ {n} ∣ ≡⟨ cong ∣_∣ []ω-cover ⟩
  --           ∣ ⋃ ⟦ [ x ]ω ∣ x ∈ℓ Tr ⟧ ∣ ≡⟨ c ⟩
  --           -- cong List.sum (map-compose λ t → ∣ [ t ]ω ∣ ) refl
  --           Data.List.Base.sum (lmap ∣_∣ ⟦ [ x ]ω ∣ x ∈ℓ Tr ⟧) ≡˘⟨ ? ⟩
  --           Data.List.Base.sum ⟦ ∣ [ x ]ω ∣ ∣ x ∈ℓ Tr ⟧ ∎
