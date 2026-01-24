# Phase 1: States on C*-Algebras

## Overview

A **state** on a C*-algebra `A` is a positive linear functional `φ : A → ℂ` with `φ(1) = 1`.

## Files

| File | LOC Target | Status | Key Content |
|------|------------|--------|-------------|
| `State/Basic.lean` | 60-80 | Proven | State structure, FunLike instance |
| `State/Positivity.lean` | 80-100 | Structure Done | map_star, self-adjoint → real |
| `State/CauchySchwarz.lean` | ~90 | Structure Done | \|φ(b\*a)\|² ≤ φ(a\*a)·φ(b\*b) |

## State Definition (Actual)

```lean
structure State (A : Type*) [CStarAlgebra A] where
  toContinuousLinearMap : A →L[ℂ] ℂ
  map_star_mul_self_nonneg : ∀ a, 0 ≤ (toContinuousLinearMap (star a * a)).re
  map_star_mul_self_real : ∀ a, (toContinuousLinearMap (star a * a)).im = 0
  map_one : toContinuousLinearMap 1 = 1
```

**Note:** Both `nonneg` AND `real` conditions needed. See LEARNINGS.md.

## Key Lemmas

### Basic.lean
- `State.continuous` - Inherited from CLM
- `State.apply_star_mul_self_nonneg` - Re(φ(a*a)) ≥ 0
- `State.apply_star_mul_self_im` - Im(φ(a*a)) = 0
- `State.apply_one` - φ(1) = 1

### Positivity.lean
- `State.map_star` - φ(a*) = conj(φ(a))
- `State.apply_real_of_isSelfAdjoint` - Im(φ(a)) = 0 when a* = a
- `State.sesqForm` - ⟨x, y⟩ = φ(y*x) form

### CauchySchwarz.lean
- `State.inner_mul_le_norm_mul_norm` - |φ(b*a)|² ≤ φ(a*a)·φ(b*b)

## Proof Strategies

### map_star (via polarization)
1. Define sesqForm ⟨x, y⟩ = φ(y*x)
2. Show diagonal ⟨z, z⟩ = φ(z*z) is real (by State axiom)
3. Polarization identity expresses off-diagonal in terms of diagonal
4. Since diagonal terms are real, form is conjugate-symmetric
5. Setting y = 1 gives map_star

### Cauchy-Schwarz
1. For t ∈ ℝ, consider φ((a + tb)*(a + tb)) ≥ 0
2. Expand: φ(a*a) + 2t·Re(φ(b*a)) + t²·φ(b*b) ≥ 0
3. Quadratic discriminant ≤ 0 gives the bound
4. Repeat with it for imaginary part

## Dependencies

```
Basic.lean
    │
    ▼
Positivity.lean
    │
    ▼
CauchySchwarz.lean
```
