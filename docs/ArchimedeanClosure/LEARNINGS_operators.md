# Operator and Type Learnings

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
