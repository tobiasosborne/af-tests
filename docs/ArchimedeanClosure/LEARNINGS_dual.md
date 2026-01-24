# Dual Characterization Learnings

## Span Intersection for Riesz Extension (AC-P6.2)

### Key Insight: Only Positive Scalars Matter

For Riesz extension, we define a separating functional ψ₀(λA) = -λε on span{A}.
We need ψ₀ ≥ 0 on M ∩ span{A}. The key observation:

1. **λ > 0 case**: If λA ∈ M, then A = (1/λ)(λA) ∈ M by cone property → A ∈ M̄.
   Contradiction. So this case never occurs.
2. **λ ≤ 0 case**: ψ₀(λA) = -λε ≥ 0 automatically (since -λ ≥ 0 and ε > 0).

### We Don't Need Full M ∩ span{A} = {0}

The FILE_PLAN specified proving M ∩ span{A} = {0}, but this is **stronger than needed**.
The λ < 0 case (negative multiples of A in M) doesn't cause problems for the
separating functional—it's automatically nonneg.

### What We Actually Proved

```lean
-- If A ∉ M̄ and c > 0, then c • A ∉ M
theorem positive_smul_not_in_M {A} (hA_not : A ∉ quadraticModuleClosure)
    {c : ℝ} (hc : 0 < c) : c • A ∉ QuadraticModule n

-- The separating functional is nonneg on M ∩ span{A}
theorem separating_nonneg_on_span_cap_M {A} (hA_not : A ∉ quadraticModuleClosure)
    {ε : ℝ} (hε : 0 < ε) {x} (hx_in_M : x ∈ QuadraticModule n)
    {coeff : ℝ} (hx_eq : x = coeff • A) : 0 ≤ -coeff * ε

-- Coefficients of M ∩ span{A} elements are ≤ 0
theorem span_cap_M_nonpos_coeff {A} (hA_not : A ∉ quadraticModuleClosure)
    {coeff : ℝ} (hcoeff_smul_in_M : coeff • A ∈ QuadraticModule n) : coeff ≤ 0
```

### Proof Pattern

The core argument is beautifully simple:
```lean
theorem positive_smul_not_in_M ... := by
  intro h_cA_in_M
  have h_A_in_M : A ∈ QuadraticModule n := by
    have h_eq : A = c⁻¹ • (c • A) := by rw [smul_smul, inv_mul_cancel₀ _, one_smul]
    rw [h_eq]
    exact QuadraticModule.smul_mem (le_of_lt (inv_pos.mpr hc)) h_cA_in_M
  exact hA_not (quadraticModule_subset_closure h_A_in_M)
```

---

## LinearPMap.mkSpanSingleton Pattern (AC-P6.3)

### Challenge
Need to define a linear map on `Submodule.span ℝ {A}` for some nonzero A.

### Solution
Use `LinearPMap.mkSpanSingleton`:
```lean
import Mathlib.LinearAlgebra.LinearPMap

noncomputable def myMap (hA : A ≠ 0) : Submodule.span ℝ {A} →ₗ[ℝ] ℝ :=
  (LinearPMap.mkSpanSingleton (K := ℝ) A targetValue hA).toFun
```

### Key Lemmas
- `LinearPMap.mkSpanSingleton_apply`: `f ⟨A, _⟩ = targetValue`
- `Submodule.mem_span_singleton`: `x ∈ span{A} ↔ ∃ c, c • A = x`

### Working with Submodule Subtypes
Elements `⟨c • A, _⟩ : Submodule.span ℝ {A}` equal `c • ⟨A, _⟩`:
```lean
have h : (⟨c • A, Submodule.mem_span_singleton.mpr ⟨c, rfl⟩⟩ : Submodule.span ℝ {A}) =
         c • ⟨A, Submodule.mem_span_singleton_self A⟩ := rfl
rw [h, LinearMap.map_smul]
-- Now: myMap (c • ⟨A, _⟩) = c • myMap ⟨A, _⟩ = c * targetValue
```

### Import
```lean
import Mathlib.LinearAlgebra.LinearPMap
```

---

## Riesz Extension Generating Condition Challenge (AC-P6.4)

### Mathlib's `riesz_extension` Theorem

```lean
riesz_extension :
  (s : ConvexCone ℝ E) (f : E →ₗ.[ℝ] ℝ) →
  (∀ (x : ↥f.domain), ↑x ∈ s → 0 ≤ ↑f x) →       -- f ≥ 0 on s ∩ domain
  (∀ (y : E), ∃ x ∈ f.domain, ↑x + y ∈ s) →      -- generating condition
  ∃ g, (∀ (x : ↥f.domain), g ↑x = ↑f x) ∧ ∀ x ∈ s, 0 ≤ g x
```

### The Challenge

For extending from `span{A}` (1-dimensional) with cone `M = QuadraticModule`:
- Condition 1 ✓: `separatingOnSpan_nonneg_on_M_cap_span` gives f ≥ 0 on M ∩ span{A}
- Condition 2 ✗: `∀ y, ∃ c, cA + y ∈ M` is **NOT** generally true

The generating condition requires every y can be "shifted" by some domain element into the cone.
For a 1-dimensional domain, this essentially asks whether M + span{A} = E, which is false.

### What We Have vs What We Need

**We proved** (`quadraticModule_selfAdjoint_generating`):
- M ∩ (A₀)_sa generates (A₀)_sa as differences: ∀ x, x = (1/4)m₁ - (1/4)m₂

**Mathlib needs**:
- `∀ y, ∃ x ∈ domain, x + y ∈ M`

These are related (both about "generating") but not identical.

### Alternative Approaches

1. **ProperCone separation** (RECOMMENDED):
   Use `ProperCone.hyperplane_separation_point` - see `LEARNINGS_extension.md`

2. **Custom Zorn's lemma proof**: Build extension step-by-step

3. **Inner product separation**: Requires `InnerProductSpace ℝ E` (not natural)

### Status

File `Dual/RieszApplication.lean` created with structure but core theorem sorry'd.
See `LEARNINGS_extension.md` for deep analysis of why standard approaches don't work
and the recommended path forward using topology infrastructure.

### Import
```lean
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation  -- for geometric_hahn_banach
```

---

## Symmetrization of Separation Functional (AC-P6.5)

### Context

The `riesz_extension_exists` theorem gives us:
```lean
∃ ψ : FreeStarAlgebra n →ₗ[ℝ] ℝ, (∀ m ∈ M, 0 ≤ ψ m) ∧ ψ A < 0
```

But `MPositiveState` requires symmetry: `φ(star a) = φ(a)`.

### Solution: Symmetrize the Functional

The symmetrization `φ(a) = (ψ(a) + ψ(star a))/2` gives us what we need.

### Key Technical Detail: star is ℝ-linear

On `FreeAlgebra ℝ (Fin n)`, the star operation is ℝ-linear:
- `star(a + b) = star a + star b` (from `star_add`)
- `star(c • a) = c • star a` for `c : ℝ`

The second property uses `FreeAlgebra.star_algebraMap`:
```lean
star (algebraMap ℝ _ c) = algebraMap ℝ _ c  -- star fixes ℝ-scalars
```

This lets us define:
```lean
noncomputable def starAsLinearMap : FreeStarAlgebra n →ₗ[ℝ] FreeStarAlgebra n where
  toFun := star
  map_add' := star_add
  map_smul' := fun c a => by
    rw [Algebra.smul_def, Algebra.smul_def, star_mul, FreeAlgebra.star_algebraMap]
    rw [Algebra.commutes]
    simp only [RingHom.id_apply]
```

### Elements of M are Self-Adjoint

Proved by induction on `QuadraticModuleSet`:
- Squares `star a * a` are self-adjoint: `star(star a * a) = star a * star(star a) = star a * a`
- Generator-weighted `star b * gⱼ * b` are self-adjoint (since gⱼ is self-adjoint)
- Preserved by addition: `IsSelfAdjoint.add`
- Preserved by ℝ-scaling: custom lemma `isSelfAdjoint_smul_of_isSelfAdjoint`

### ℝ-scaling preserves self-adjointness

For `c : ℝ` (no Star instance!) and self-adjoint m:
```lean
theorem isSelfAdjoint_smul_of_isSelfAdjoint {m} (hm : IsSelfAdjoint m) (c : ℝ) :
    IsSelfAdjoint (c • m) := by
  unfold IsSelfAdjoint at *
  rw [Algebra.smul_def, star_mul, FreeAlgebra.star_algebraMap, hm, Algebra.commutes]
```

Note: Can't use `IsSelfAdjoint.smul` because that requires `StarModule R A` and ℝ has no Star instance.

### Symmetrization Properties

1. **Symmetric**: `φ(star a) = φ(a)` by direct calculation
2. **Equals original on self-adjoints**: `φ(a) = ψ(a)` when `a` is self-adjoint
3. **Preserves nonnegativity on M**: Since M ⊆ self-adjoints
4. **Preserves negativity on A**: Since A is self-adjoint

### Import
```lean
import Mathlib.Tactic.Ring  -- for ring tactic in symmetrization proofs
```

---

## Normalization to MPositiveState (AC-P6.6)

### Context

From `symmetrize_separation` we have φ : A₀ →ₗ[ℝ] ℝ with:
- φ(star a) = φ(a) (symmetric)
- φ(m) ≥ 0 for m ∈ M
- φ(A) < 0

To construct an `MPositiveState`, we need φ(1) = 1. Solution: normalize by φ(1).

### Proving φ(1) > 0

**Key insight**: φ(1) ≤ 0 leads to contradiction via Cauchy-Schwarz.

**Cauchy-Schwarz for general symmetric M-nonneg functional:**
```lean
φ(a)² ≤ φ(star a * a) * φ(1)
```

Proof: Expand `φ(star(a + t·1) * (a + t·1)) ≥ 0` as quadratic in t, apply discriminant bound.

**Case φ(1) = 0:**
From Cauchy-Schwarz: φ(a)² ≤ 0 for all a, so φ(a) = 0. But φ(A) < 0. Contradiction.

**Case φ(1) < 0:**
By Archimedean: N·1 - star(A)*A ∈ M for some N.
Then: N·φ(1) ≥ φ(star A * A) ≥ 0
Since φ(1) < 0 and N ≥ 0: N·φ(1) ≤ 0
Combined: N·φ(1) = 0 and φ(star A * A) = 0
If φ(1) < 0, this requires N = 0.
By Cauchy-Schwarz: φ(A)² ≤ φ(star A * A) * φ(1) = 0
So φ(A) = 0. But φ(A) < 0. Contradiction.

### Key Lemmas in Normalization.lean

```lean
theorem phi_one_pos : 0 < φ 1

noncomputable def normalizedMPositiveState : MPositiveState n

theorem exists_MPositiveState_negative :
    ∃ φ : MPositiveState n, φ A < 0
```

### Expansion Algebra for Quadratic Form

To expand `(star a + t • 1) * (a + t • 1)`:
```lean
simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_add]
rw [sq, smul_smul]
abel
```

Key: `smul_add` is needed to distribute `t • (star a + t • 1)`.

### Non-commutative Ring Considerations

`ring` tactic doesn't work in FreeAlgebra (non-commutative). Use `abel` for additive
computations and manual rewriting for multiplicative structure.
