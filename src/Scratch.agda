module Scratch {a b} where
open import Level
open import Algebra
open import Relation.Binary
open import Data.Product
open import Data.Empty
open import Relation.Binary.PropositionalEquality

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

data M : Set (suc a) where
  m : (I : Set a) → (I → M) → M

_∈_ : M → M → Set _ -- (suc a)
s ∈ m I f = ∃[ i ] (s ≡ f i)

_∉_ : M → M → Set (suc a)
s ∉ t = s ∈ t → ⊥

-- this is not possible !
-- R : M
-- R = m (Σ M (λ a → a ∉ a)) proj₁
