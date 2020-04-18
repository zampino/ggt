open import GGT

module GGT.Theory
  {a b ℓ₁ ℓ₂}
  -- Throughout the following assume A is a (right) Action
  (A : Action a b ℓ₁ ℓ₂)
  where

open import Level
open import Relation.Unary
open import Algebra

-- open import Relation.Binary.Reasoning.Setoid A.setoid
open Action A
open Group G

gcong : ∀ (o o' : Ω) (g : Carrier) → (o ≋ o') → (o · g) ≋ (o' · g)
gcong o o' g p = ·-cong g p

ginv  : ∀ (o p : Ω) (g : Carrier) → o · g ≋ p → o ≋ p · g ⁻¹
ginv o p g x = {!   !} -- where open Group G

-- stabilizerIsSubGroup : ∀ (o : Ω) → isSubgroup G (Stab o)
-- stabilizerIsSubGroup o = λ x y px py → {!    !}
