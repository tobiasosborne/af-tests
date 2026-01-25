# Miscellaneous Learnings

## QuadraticModule Definition Strategy

### Challenge
Defining M requires nonnegative ℝ-scaling, but `FreeAlgebra ℝ (Fin n)` has native ℝ-module.

### Solution
Defined `QuadraticModuleSet` as an `inductive` set with three constructors:
1. `generator_mem` - base generators (squares + generator-weighted squares)
2. `add_mem` - closure under addition
3. `smul_mem` - closure under `c • _` for `0 ≤ c : ℝ`

### Why Not ConvexCone?
Could use `ConvexCone.hull ℝ (generators)` but requires:
- More complex imports
- Instance resolution complexity
- Less direct membership proofs

The inductive definition is simpler.

---

## Section Organization for Variable Scope

### Challenge
When some definitions need `[IsArchimedean n]` and others don't, the auto variable
inclusion triggers linter warnings.

### Solution
Use `section ... end` blocks:

```lean
variable {n : ℕ}

section Embedding
-- No IsArchimedean needed here
def toProductFun (φ : MPositiveState n) : FreeStarAlgebra n → ℝ := fun a => φ a
end Embedding

section Bounded
variable [IsArchimedean n]
-- IsArchimedean needed here
theorem apply_mem_closedBall (φ : MPositiveState n) (a : FreeStarAlgebra n) : ... := ...
end Bounded
```

The `variable` inside `section Bounded` only applies within that section.

---

## FunLike Extensionality

### Challenge
When defining a structure with `FunLike` instance (like `MPositiveState`), `ext`
may not work due to no `@[ext]` attribute.

### Solution 1: Use DFunLike directly
```lean
theorem toProductFun_injective : Function.Injective (toProductFun (n := n)) := by
  intro φ ψ h
  apply DFunLike.coe_injective'
  exact h
```

### Solution 2: Register ext lemma
```lean
@[ext]
theorem ext {φ ψ : MPositiveState n} (h : ∀ a, φ a = ψ a) : φ = ψ :=
  DFunLike.coe_injective' (funext h)
```

---

## Import Notes

### For Star Algebra
```lean
import Mathlib.Algebra.Star.Free          -- FreeAlgebra star instance
import Mathlib.Algebra.Star.SelfAdjoint   -- IsSelfAdjoint
```

### For Bounds
```lean
import Mathlib.Analysis.SpecialFunctions.Pow.Real  -- Real.sqrt, sq_sqrt
```

### For Compactness
```lean
import Mathlib.Topology.Compactness.Compact       -- isCompact_univ_pi
import Mathlib.Topology.MetricSpace.ProperSpace   -- ProperSpace
```

### For Commute Lemmas
```lean
import Mathlib.Algebra.Ring.Commute  -- Commute.mul_self_sub_mul_self_eq
```

(May be transitively imported via other Algebra imports)

---

## MPositiveStateProps: What We Kept

After moving `map_star` to axiom, remaining useful lemmas:
- `apply_self_adjoint_add`: `φ(a + star a) = 2 * φ(a)`
- `apply_self_adjoint_sub`: `φ(a - star a) = 0`
- `apply_isSelfAdjoint`: `φ(star a) = φ(a)` when a is self-adjoint
- `apply_decomposition`: `φ(a) = (1/2) * φ(a + star a)`

These are trivial consequences of `map_star` but convenient to have named.

---

## StarAlgHom: map_star' vs map_star

### Observation
`StarAlgHom` uses `map_star'` (with prime), not `map_star`, to access the star-preserving property.

```lean
-- WRONG: π.toStarAlgHom.map_star a
-- RIGHT: π.toStarAlgHom.map_star' a
```

This is because `map_star` would conflict with the `StarHomClass` instance method.
The prime convention avoids namespace collision.

### Import
```lean
import Mathlib.Algebra.Star.StarAlgHom
```

---

## RCLike.re vs Complex.re

### Challenge
When working with inner products over ℂ, `inner_self_nonneg` gives:
```lean
inner_self_nonneg : 0 ≤ RCLike.re ⟪x, x⟫_ℂ
```
But goals often have `.re` (Complex field accessor):
```lean
⊢ 0 ≤ (⟪v, v⟫_ℂ).re
```
These are definitionally equal, but Lean's pattern matching doesn't unify them.

### Solution
Use `RCLike.re_eq_complex_re` to convert:
```lean
have h : 0 ≤ RCLike.re ⟪v, v⟫_ℂ := inner_self_nonneg
simp only [RCLike.re_eq_complex_re] at h
exact h
```

### Import
```lean
import Mathlib.Analysis.Complex.Basic  -- RCLike.re_eq_complex_re
```

---

## inner_smul_real_right Type Annotation

### Challenge
`inner_smul_real_right` fails to pattern match without explicit types:
```lean
-- Fails: inner_smul_real_right ξ (π.toStarAlgHom a ξ) c
```

### Solution
Provide explicit type annotation on the inner product:
```lean
have h : (⟪ξ, (c : ℂ) • (π.toStarAlgHom a ξ)⟫_ℂ : ℂ) = c • ⟪ξ, (π.toStarAlgHom a ξ)⟫_ℂ :=
  inner_smul_real_right ξ _ c
```

The `(_ : ℂ)` annotation helps Lean resolve the coercion.

---

## ContinuousLinearMap.IsPositive Structure

### Definition
`IsPositive T` for `T : E →L[ℂ] E` requires TWO conditions:
1. `(↑T).IsSymmetric` - the underlying LinearMap is symmetric
2. `∀ v, 0 ≤ T.reApplyInnerSelf v` - nonnegative on all vectors

### Key Lemmas
```lean
ContinuousLinearMap.isPositive_def : T.IsPositive ↔ (↑T).IsSymmetric ∧ ∀ x, 0 ≤ T.reApplyInnerSelf x
ContinuousLinearMap.star_eq_adjoint : star A = ContinuousLinearMap.adjoint A
ContinuousLinearMap.isSelfAdjoint_iff' : IsSelfAdjoint A ↔ adjoint A = A
IsPositive.inner_nonneg_right : T.IsPositive → 0 ≤ ⟪v, T v⟫_ℂ
```

### Pattern: Proving IsPositive from Vector States
To show π(A) is positive when φ(A) ≥ 0 for all M-positive states φ:
1. Show π(A) is symmetric (from A being self-adjoint and π being a *-homomorphism)
2. For any unit vector v, the vector state φ_v is M-positive
3. φ_v(A) = Re⟨v, π(A)v⟩ ≥ 0 by hypothesis on states
4. Since π(A) is symmetric, ⟨v, π(A)v⟩ is real, so ⟨v, π(A)v⟩ ≥ 0

---

## GNS Construction for FreeStarAlgebra

### Key Insight: Archimedean Property Guarantees Boundedness

**Discovery (Schmudgen 2020, Cimpric 2009):** For general *-algebras (not C*-algebras),
the GNS construction may produce unbounded operators. However, when the quadratic
module is Archimedean, **all M-positive representations act by bounded operators**.

This is why our formalization strategy works: we don't face domain issues or
unbounded operator complications because the Archimedean property is assumed.

### Construction Overview (7 files, ~320 LOC)

```
AfTests/ArchimedeanClosure/GNS/
├── NullSpace.lean   (~50 LOC) - N_φ = {a : φ(a*a) = 0}, left ideal
├── Quotient.lean    (~50 LOC) - A/N_φ with ⟨[a],[b]⟩ = φ(a*b)
├── Completion.lean  (~40 LOC) - Hilbert space H_φ, cyclic vector Ω
├── PreRep.lean      (~40 LOC) - Left multiplication: a • [b] = [ab]
├── Bounded.lean     (~50 LOC) - ‖a • x‖ ≤ √N_a · ‖x‖ (uses Archimedean!)
├── Extension.lean   (~50 LOC) - Extend to completion, *-algebra hom
└── Constrained.lean (~40 LOC) - π(gⱼ) ≥ 0 from M-positivity
```

### Difference from C*-algebra GNS (AfTests/GNS/)

| Aspect | C*-Algebra GNS | FreeStarAlgebra GNS |
|--------|----------------|---------------------|
| **Boundedness** | Uses C*-norm: ‖π(a)‖ ≤ ‖a‖ | Uses Archimedean: ‖π(a)‖ ≤ √N_a |
| **State type** | `A →L[ℂ] ℂ` (continuous) | `A →ₗ[ℝ] ℝ` (just linear) |
| **Scalar field** | ℂ throughout | ℝ for algebra, ℂ for Hilbert space |
| **Constrained** | N/A | Must prove π(gⱼ) ≥ 0 |

### Key Proof: Generators Map to Positive Operators

**Theorem:** For GNS representation π_φ of M-positive state φ, each π_φ(gⱼ) is positive.

**Proof:**
1. For [b] in quotient: ⟨[b], π_φ(gⱼ)[b]⟩ = φ(b* · gⱼ · b)
2. But b* · gⱼ · b ∈ M by definition of quadratic module
3. So φ(b* · gⱼ · b) ≥ 0 by M-positivity of φ
4. Extend to completion by density

### References

- **Schmudgen (2020)**: "An Invitation to Unbounded Representations of *-Algebras on Hilbert Space"
  - Chapter 10: Archimedean quadratic modules → bounded representations

- **Cimpric (2009)**: "A representation theorem for Archimedean quadratic modules on *-rings"
  - arxiv:0807.5020
  - Generalizes Jacobi's representation theorem

### Mathlib Tools to Use

```lean
import Mathlib.Analysis.InnerProductSpace.Defs       -- PreInnerProductSpace.Core
import Mathlib.Analysis.InnerProductSpace.Completion -- UniformSpace.Completion.innerProductSpace
import Mathlib.Analysis.InnerProductSpace.Positive   -- ContinuousLinearMap.IsPositive
import Mathlib.Algebra.Star.StarAlgHom              -- StarAlgHom
```

---

## Vector Normalization for IsPositive Proofs

### Challenge
To prove `T.IsPositive`, we need `0 ≤ T.reApplyInnerSelf x` for all `x`.
But vector states only give us information about unit vectors.

### Solution: Normalize and Scale
```lean
by_cases hx : x = 0
· simp [hx, ContinuousLinearMap.reApplyInnerSelf_apply]
· -- For nonzero x, normalize to unit vector
  set u := (‖x‖⁻¹ : ℂ) • x with hu_def
  have hu_norm : ‖u‖ = 1 := norm_smul_inv_norm hx
  -- Use vector state on u, then scale back
  have hx_eq : x = (‖x‖ : ℂ) • u := by
    rw [hu_def, smul_smul, mul_inv_cancel₀ ...]
  -- Result: Re⟨x, Tx⟩ = ‖x‖² * Re⟨u, Tu⟩ ≥ 0
```

### Key Lemmas
- `norm_smul_inv_norm : x ≠ 0 → ‖(‖x‖⁻¹ : 𝕜) • x‖ = 1`
- `inner_smul_left/right` for distributing scalars
- `Complex.conj_ofReal` for conjugate of real cast

### Complex Number Manipulation
For `((↑r : ℂ)^2).re = r^2`:
```lean
have hcast : (↑‖x‖ : ℂ)^2 = (‖x‖^2 : ℝ) := by norm_cast
have hre : (↑‖x‖ ^ 2 : ℂ).re = ‖x‖^2 := by rw [hcast]; exact Complex.ofReal_re _
```

---

## IsSelfAdjoint.map for StarAlgHom

### Pattern
When A is self-adjoint in domain and π is a *-homomorphism:
```lean
have hπA_sa : IsSelfAdjoint (π A) := hA.map π.toStarAlgHom
```

This uses `IsSelfAdjoint.map` from `Mathlib.Algebra.Star.SelfAdjoint`.

### Converting to adjoint equation
```lean
rw [← ContinuousLinearMap.isSelfAdjoint_iff'] at hπA_sa
-- Now: hπA_sa : ContinuousLinearMap.adjoint (π A) = π A
```
