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

---

## Scalar Multiplication with StarAlgHom

**Discovery:** Proving `π(c • a) = c • π(a)` for a `StarAlgHom π : A →⋆ₐ[ℂ] B`
requires going through the algebra map, not `map_smul` directly.

**Problem:** `map_smul` on `StarAlgHom` doesn't unify directly with the goal
`π(c • a) = c • π(a)` because the smul operations are different types.

**Resolution:** Use the algebra structure:
```lean
-- c • a = (algebraMap ℂ A c) * a in any ℂ-algebra
rw [Algebra.smul_def, _root_.map_mul, ContinuousLinearMap.mul_apply]
-- π(algebraMap ℂ A c) = algebraMap ℂ B c by algebra hom property
rw [AlgHomClass.commutes]
-- algebraMap ℂ B c = c • 1, then simplify application
simp only [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply,
  ContinuousLinearMap.one_apply]
```

**Key insight:** In ℂ-algebras, `c • a = (algebraMap ℂ A c) * a` by `Algebra.smul_def`.
The algebra homomorphism property `AlgHomClass.commutes` then gives us what we need.

**Lesson:** When `map_smul` doesn't work for algebra homs, decompose the scalar
multiplication via `Algebra.smul_def` and use multiplicativity + `AlgHomClass.commutes`.

---

## Topology Diamond on Quotient Spaces

**Discovery:** The quotient `A ⧸ N_φ` has two topology instances that don't unify:
- `QuotientModule.Quotient.topologicalSpace` - the quotient topology
- `PseudoMetricSpace.toUniformSpace.toTopologicalSpace` - from the seminorm

**Problem:** When proving `Continuous f` for a `LinearIsometry f : gnsQuotient →ₗᵢ[ℂ] H`,
the `LinearIsometry.continuous` lemma gives continuity w.r.t. the metric topology,
but Lean expects continuity w.r.t. the quotient topology.

**Workaround:** Skip explicit continuity theorems. The `LinearIsometry` structure
itself provides what's needed - when continuity is required later, Lean will use
the metric topology from the normed space structure, which is the correct one.

**Lesson:** For quotients of seminormed spaces, prefer working with the
`LinearIsometry` structure directly rather than proving separate continuity lemmas.
The topologies are equal mathematically but Lean doesn't always see this.
