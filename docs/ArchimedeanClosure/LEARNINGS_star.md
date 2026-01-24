# Star Structure Learnings

## FreeAlgebra Star Structure Discovery

### Finding
Mathlib's `FreeAlgebra.instStarRing` (in `Mathlib.Algebra.Star.Free`) provides:
- `star (ι x) = ι x` — generators are self-adjoint ✓
- `star (algebraMap r) = algebraMap r` — scalars are FIXED, not conjugated ✗

### Implication
This does NOT give a ℂ-*-algebra in the physics/functional analysis sense where we need:
- `star (c • a) = conj(c) • star(a)` (conjugate-linearity)

The mathlib star structure satisfies `StarRing` but NOT `StarModule ℂ`.

### Key Mathlib Lemmas
- `FreeAlgebra.star_ι` : `star (ι x) = ι x`
- `FreeAlgebra.star_algebraMap` : `star (algebraMap r) = algebraMap r`
- Import: `Mathlib.Algebra.Star.Free`

---

## NonEmptiness BLOCKED Over ℂ

### The Problem
For `FreeAlgebra ℂ X`, consider `a = algebraMap I` (imaginary unit):
```
star a = algebraMap I        (star fixes scalars)
star a * a = algebraMap (I * I) = algebraMap (-1)
```

Since `star a * a ∈ M` always, we have `algebraMap (-1) ∈ M`.

### Scalar Extraction Failure
Using `FreeAlgebra.algebraMapInv`:
```
scalarExtraction (algebraMap (-1)) = -1
```
This has **negative real part**, violating M-positivity!

### Counter-Example Summary
| Element | In M? | Scalar Extraction | M-Positive? |
|---------|-------|-------------------|-------------|
| `star(algebraMap I) * algebraMap I` | ✓ | `-1` | ✗ |

---

## Resolution: Work Over ℝ

### Decision
`FreeStarAlgebra n` = `FreeAlgebra ℝ (Fin n)`, NOT `FreeAlgebra ℂ`.

### Why This Fixes Scalar Extraction
Over ℝ, for any scalar `c : ℝ`:
```
star (algebraMap c) * algebraMap c = algebraMap (c²)
```
Since `c² ≥ 0` for all real `c`, scalar extraction maps every `star a * a` to a
nonnegative real, as required for M-positivity.

### Key Proof
```lean
scalarExtraction(star a * a) = scalarExtraction(star a) * scalarExtraction(a)
                              = scalarExtraction(a) * scalarExtraction(a)
                              = scalarExtraction(a)²
```
And `x² ≥ 0` for all `x : ℝ`. This is a 3-line proof!

---

## Refactoring Summary (RF-1 through RF-6)

### RF-1: FreeStarAlgebra Uses ℝ
Changed `FreeAlgebra ℂ (Fin n)` to `FreeAlgebra ℝ (Fin n)`.

### RF-2: QuadraticModule Uses Native ℝ-Scaling
Changed `(c : ℂ) • m` to `c • m` - native via `Module ℝ (FreeAlgebra ℝ X)`.

### RF-3: Archimedean Updated
Changed `((N : ℝ) : ℂ) • 1` to `(N : ℝ) • 1`.

### RF-4: MPositiveState Redesigned
```lean
-- OLD (ℂ-linear, problematic)
structure MPositiveState (n : ℕ) where
  toFun : FreeStarAlgebra n →ₗ[ℂ] ℂ
  map_m_nonneg : ∀ m ∈ QuadraticModule n, 0 ≤ (toFun m).re
  map_m_real : ∀ m ∈ QuadraticModule n, (toFun m).im = 0

-- NEW (ℝ-linear, cleaner)
structure MPositiveState (n : ℕ) where
  toFun : FreeStarAlgebra n →ₗ[ℝ] ℝ
  map_star : ∀ a, toFun (star a) = toFun a
  map_m_nonneg : ∀ m ∈ QuadraticModule n, 0 ≤ toFun m
```

### RF-5: MPositiveStateProps Simplified
Removed unnecessary theorems (codomain is ℝ, all values real automatically).

### RF-6: NonEmptiness Proven
Scalar extraction now works because `x² ≥ 0` for `x : ℝ`.

---

## Technical Note: star_smul for ℝ-Algebras

For `FreeAlgebra ℝ X`, we have `star (c • a) = c • star a` for `c : ℝ`:
```lean
star (c • a) = star (algebraMap c * a)     -- Algebra.smul_def
            = star a * star (algebraMap c) -- star_mul
            = star a * algebraMap c        -- FreeAlgebra.star_algebraMap
            = algebraMap c * star a        -- Algebra.commutes
            = c • star a                   -- Algebra.smul_def
```

This could be used to define `Module ℝ (selfAdjoint (FreeAlgebra ℝ X))` if needed.
