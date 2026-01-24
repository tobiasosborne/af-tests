# Quotient Construction Learnings

Technical discoveries related to quotient modules and well-definedness.

---

## Quotient Module Construction in Mathlib

**Discovery:** Constructing the quotient A ⧸ N_φ requires upgrading from `AddSubgroup`
to `Submodule ℂ A`.

**Key Mathlib APIs:**
- `Submodule.mkQ` : the quotient map `A →ₗ[ℂ] A ⧸ N`
- `Submodule.liftQ` : lift a linear map through the quotient (requires `N ≤ ker f`)
- `Submodule.Quotient.mk` : the element-level quotient constructor
- `Submodule.Quotient.mk_add` : `mk (a + b) = mk a + mk b`
- `Submodule.Quotient.mk_surjective` : every element has a representative

**Extensionality Pattern:** When proving `f = g` for linear maps on quotients:
```lean
ext x  -- gives x : A (the underlying type)
-- Goal becomes: (f ∘ₗ mkQ) x = (g ∘ₗ mkQ) x
simp [mkQ_apply, ...]
```

**Lesson:** The `ext` tactic for quotient modules doesn't give you `x : A ⧸ N`;
it gives you `x : A` and a goal involving `mkQ x`. Structure your proofs accordingly.

---

## Well-Definedness for Binary Functions on Quotients

**Discovery:** Defining binary functions on `Submodule.Quotient` requires careful
handling of the quotient relation.

**Problem:** `Quotient.liftOn₂` requires proving that if `a₁ ≈ b₁` and `a₂ ≈ b₂`,
then `f a₁ a₂ = f b₁ b₂`. For submodule quotients:
- The relation `a ≈ b` is defined via `QuotientAddGroup.leftRel`
- `leftRel_apply.mp` gives `-a + b ∈ p` (not `a - b ∈ p`!)
- Need to convert: `-a + b = b - a` (by `neg_add_eq_sub`), then negate to get `a - b`

**Key Mathlib APIs:**
- `QuotientAddGroup.leftRel_apply : leftRel s x y ↔ -x + y ∈ s`
- `neg_add_eq_sub : -a + b = b - a`
- `Submodule.Quotient.mk_surjective p x` - note: takes submodule as first arg

**Pattern for obtain on quotients:**
```lean
obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal x
```

**Pattern for proving complex equalities:**
When showing `φ x = φ y` for a linear form φ:
```lean
have h1 : φ x - φ y = φ (x - y) := by rw [← φ.map_sub]
rw [← sub_eq_zero, h1, h_zero]  -- where h_zero : φ (x - y) = 0
```

**Lesson:** The left coset relation uses `-a + b ∈ p`, not `a - b ∈ p`. Always
check the exact form of quotient relations before using them.
