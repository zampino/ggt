module Scratch where
open import Level
open import Algebra
open import Relation.Binary

open import GGT
postulate
  a b ℓ₁ ℓ₂ : Level

actionToOp : ∀ {A : Action a b ℓ₁ ℓ₂} → Group.Carrier (Action.G A) → (Action.Ω A) → (Action.Ω A)
-- actionToOp {A} g o = o · g where open Action A
-- actionToOp {A} g = λ o → o · g where open Action A
actionToOp {A} g = _· g where open Action A

-- other tests

postulate
  l : Level
  H : Group l l

f : Group l l → Set l
f x = Group.Carrier x


open Group H
postulate
  h : Carrier

h∙_ : Carrier → Carrier
h∙ x = h ∙ x


aa : {A : Action a b ℓ₁ ℓ₂} → Group a ℓ₁
aa {A} = Action.G A

oo : {A : Action a b ℓ₁ ℓ₂} → Set b
oo {A} = Action.Ω A

-- postulate
--   A : Action a b ℓ₁ ℓ₂
--   x : Group.Carrier (Action.G A)
--
-- open Action A
--
-- _ : Ω → Ω
-- _ = _· x

-- μ : Group.Carrier (G A) → Ω A → Ω A
-- μ g o =  o · g

-- μ : Action.G a b ℓ → Action.Ω → Action.Ω
-- μ g = ?

postulate
  m : Level

_ : Set (Level.suc m)
_  = Set m

open import Data.Product

postulate
  A : Set a
  P : A → Set b
  σ : (a : A) → (P a)

w : A → Σ[ a ∈ A ] (P a)
w a = (a , σ a)

w' : A → Σ A (λ a → P a)
w' a = (a , σ a)

w'' : A → ∃[ a ] (P a)
w'' a = (a , σ a)

-- Setoid → Partition S
-- | S | = sum c | c |
