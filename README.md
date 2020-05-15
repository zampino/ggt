# 🏗 Geometric Group Theory in Agda 🚧

This is a work-in-progress collection of formalised facts about groups and their actions.

## Action definitions

```agda
record Action a b ℓ₁ ℓ₂ : Set (suc (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂))  where
  infix 6 _·_
  infix 3 _≋_
  open Group hiding (setoid)
  field
    G : Group a ℓ₁
    Ω : Set b
    _≋_ : Rel Ω ℓ₂
    _·_ : Opᵣ (Carrier G) Ω
    isAction : IsAction (_≈_ G) _≋_ _·_ (_∙_ G) (ε G) (_⁻¹ G)

  open IsAction isAction public

  -- the (raw) pointwise stabilizer
  stab : Ω → Pred (Carrier G) ℓ₂
  stab o = λ (g : Carrier G) → o · g ≋ o

  -- Orbital relation
  _ω_  : Rel Ω (a ⊔ ℓ₂)
  o ω o' = ∃[ g ] (o · g ≋ o')
  -- TODO: ω is equivalence refining ≋

  _·G : Ω → Pred Ω (a ⊔ ℓ₂)
  o ·G = o ω_

  open import GGT.Setoid setoid (a ⊔ ℓ₂)
  Orbit : Ω → Setoid (b ⊔ (a ⊔ ℓ₂)) ℓ₂
  Orbit o = subSetoid (o ·G)
```

## Proven Facts

[Orbital Correspondence](https://github.com/zampino/ggt/blob/master/src/ggt/Theory.agda#L43) (right cosets of G modulo pointwise stabilisers correspond 1:1 to the orbits of the action)

```agda
stabIsSubGroup : ∀ (o : Ω) → (stab o) ≤ G
stabIsSubGroup o = record { ε∈ = actId o ;
                            ∙-⁻¹-closed = itis ;
                            r = resp } where ...

Stab : Ω → SubGroup G
Stab o = record { P = stab o;
                  isSubGroup = stabIsSubGroup o}

orbitalCorr : {o : Ω} → Bijection (Stab o \\ G) (Orbit o)
orbitalCorr {o} = record { f = f ;
                           cong = cc ;
                           bijective = inj ,′ surj } where ...
```

## Future Plans

- Primitivity
- Wreath Products
