# Archimedean Closure Learnings

## 2026-01-24: FreeAlgebra Star Structure Discovery

### Finding
Mathlib's `FreeAlgebra.instStarRing` (in `Mathlib.Algebra.Star.Free`) provides:
- `star (ι x) = ι x` — generators are self-adjoint ✓
- `star (algebraMap r) = algebraMap r` — scalars are FIXED, not conjugated ✗

### Implication
This does NOT give a ℂ-*-algebra in the physics/functional analysis sense where we need:
- `star (c • a) = conj(c) • star(a)` (conjugate-linearity)

The mathlib star structure satisfies `StarRing` but NOT `StarModule ℂ`.

### Workaround Options
1. **Work over ℝ**: Use `FreeAlgebra ℝ (Fin n)`, extend to ℂ-valued functionals
2. **Quotient**: Take quotient enforcing conjugate-linear star relations
3. **Abstract**: Define structure axiomatically with universal property

### Decision for This Project
For Phase 1, we'll use `FreeAlgebra ℂ (Fin n)` as-is with the existing star structure.
The quadratic module M consists of elements like `star a * a` where star behavior on
the algebra level is what matters. The conjugation issue affects how we define states
(Phase 2) - we may need states to be ℝ-linear on self-adjoints rather than ℂ-linear.

### Key Mathlib Lemmas
- `FreeAlgebra.star_ι` : `star (ι x) = ι x`
- `FreeAlgebra.star_algebraMap` : `star (algebraMap r) = algebraMap r`
- Import: `Mathlib.Algebra.Star.Free`

---

## 2026-01-24: QuadraticModule Definition Strategy

### Challenge
Defining the quadratic module M requires nonnegative ℝ-scaling, but `FreeAlgebra ℂ (Fin n)`
does not have a natural `SMul ℝ` instance. The ℝ-module structure would require
`RestrictScalars` or custom setup.

### Solution
Use ℂ-scaling with real coefficients: `(c : ℂ) • m` where `c : ℝ`.
Since nonnegative reals embed into ℂ, this captures exactly the cone structure we need.

### Implementation
Defined `QuadraticModuleSet` as an `inductive` set with three constructors:
1. `generator_mem` - base generators (squares + generator-weighted squares)
2. `add_mem` - closure under addition
3. `smul_mem` - closure under `(c : ℂ) • _` for `0 ≤ c : ℝ`

This avoids the complexity of `ConvexCone` machinery while capturing the exact set we need.

### Alternative Considered
Could use `ConvexCone.hull ℝ (generators)` but this requires:
- Defining ℝ-module structure via `RestrictScalars`
- More complex imports and instance resolution
- Less direct control over the carrier

The inductive definition is simpler and gives us direct membership proofs.

---

## 2026-01-24: Classical.choose vs Nat.find

### Challenge
The FILE_PLAN suggested using `Nat.find` to get the minimal Archimedean bound:
```lean
noncomputable def archimedeanBound [IsArchimedean n] (a : FreeStarAlgebra n) : ℕ :=
  Nat.find (IsArchimedean.bound a)
```

This fails because `Nat.find` requires `DecidablePred`, but membership in
`QuadraticModule n` is not decidable (it's an inductive set).

### Solution
Use `Classical.choose` instead:
```lean
noncomputable def archimedeanBound [IsArchimedean n] (a : FreeStarAlgebra n) : ℕ :=
  Classical.choose (IsArchimedean.bound a)

theorem archimedeanBound_spec [IsArchimedean n] (a : FreeStarAlgebra n) :
    ... ∈ QuadraticModule n :=
  Classical.choose_spec (IsArchimedean.bound a)
```

### Trade-off
- `Nat.find` gives the *minimal* witness (useful for bounds reasoning)
- `Classical.choose` gives *some* witness (sufficient for our purposes)

For the Archimedean closure proof, we only need existence of a bound, not minimality.
If minimality becomes important later, we can add decidability or use a different approach.

---

## 2026-01-24: MPositiveState Definition (Phase 2 Start)

### Approach
Defined `MPositiveState` using ℂ-linear functionals (`FreeStarAlgebra n →ₗ[ℂ] ℂ`)
with separate properties for M-positivity:
- `map_m_nonneg`: `0 ≤ (toFun m).re` for m ∈ M
- `map_m_real`: `(toFun m).im = 0` for m ∈ M

### Why This Works
Despite the star structure not satisfying `StarModule ℂ`, the M-positivity definition
only requires checking values on M elements. Since M consists of "squares" (star a * a)
and generator-weighted squares, these are morally self-adjoint, so demanding they map
to real values is natural.

### Deferred Question
The conjugate-symmetry property `φ(star a) = conj(φ(a))` is NOT part of the basic
structure definition. This will need to be:
1. Proven as a consequence (in MPositiveStateProps.lean), OR
2. Added as an explicit hypothesis

This is intentional - keep the base definition minimal, add properties as theorems.

---

## 2026-01-24: MPositiveStateProps Sorries Analysis

### Two Open Sorries
`MPositiveStateProps.lean` has 2 sorries that require careful proofs:

1. **`apply_real_of_isSelfAdjoint`**: Show `(φ a).im = 0` when `star a = a`
2. **`map_star`**: Show `φ(star a) = conj(φ(a))` for all `a`

### Proof Strategy for `apply_real_of_isSelfAdjoint`
For self-adjoint `a`, use the polarization identity:
```
a = 1/4 * (1+a)*(1+a) - 1/4 * (1-a)*(1-a)
```
Since `(1±a)` is still self-adjoint when `a` is, and `star(1+a)*(1+a) ∈ M`,
we get `φ(a)` as a real linear combination of real values.

**Prerequisites:**
- Prove `star(1+a) = 1 + a` when `a` is self-adjoint
- Show the identity `a = 1/4 * star(1+a)*(1+a) - 1/4 * star(1-a)*(1-a)` holds
- Use `map_m_real` to conclude

### Proof Strategy for `map_star`
Standard argument from positivity uses polarization:
1. From `φ(star(a+λb) * (a+λb)) ≥ 0` for all `λ ∈ ℂ`
2. Expand and extract: `φ(star(a)*b) + λ*φ(star(b)*a) + conj(λ)*φ(star(a)*b) + |λ|²*φ(star(b)*b)`
3. Analyze the positive semidefinite quadratic form
4. Derive `φ(star(b)*a) = conj(φ(star(a)*b))`
5. Set `b = 1`: `φ(star(a)) = conj(φ(a))`

**Challenge:** The FreeAlgebra star structure may complicate step 1-2.
The expansion `star(a + λb) = star(a) + λ*star(b)` (NOT `conj(λ)*star(b)`)
due to the scalar-fixing star.

### Recommendation
Consider whether to:
1. Add `map_star` as an axiom in `MPositiveState` structure, OR
2. Restrict to proofs that only use `apply_m_real` on M elements, OR
3. Work through the polarization proof carefully accounting for the star structure

---

## 2026-01-24: NonEmptiness BLOCKED - Star Structure Breaks Scalar Extraction

### Critical Finding
The standard "scalar extraction gives M-positive state" approach **FAILS** due to
the star structure not conjugating scalars.

### The Problem
For `FreeAlgebra ℂ X`, the star structure satisfies:
- `star (algebraMap c) = algebraMap c` (scalars are FIXED)

Consider `a = algebraMap I` (the imaginary unit embedded in the algebra):
```
star a = algebraMap I        (since star fixes scalars)
star a * a = algebraMap (I * I) = algebraMap (-1)
```

Since `star a * a` is always in the quadratic module M, we have `algebraMap (-1) ∈ M`.

### Scalar Extraction Failure
The scalar extraction functional is `FreeAlgebra.algebraMapInv`, which:
- Maps generators to 0
- Extracts the scalar coefficient: `algebraMapInv (algebraMap c) = c`

Applying this to our M-element:
```
scalarExtraction (algebraMap (-1)) = -1
```

This has **negative real part**, violating M-positivity requirement!

### Mathlib Functions Used
- `FreeAlgebra.algebraMapInv : FreeAlgebra R X →ₐ[R] R`
- `FreeAlgebra.algebraMap_leftInverse : algebraMapInv ∘ algebraMap = id`
- `FreeAlgebra.star_algebraMap : star (algebraMap c) = algebraMap c`

### Counter-Example Summary
| Element | In M? | Scalar Extraction | Real Part | M-Positive? |
|---------|-------|-------------------|-----------|-------------|
| `star(algebraMap I) * algebraMap I` | ✓ | `-1` | `-1` | ✗ |

### Implications
This is a fundamental obstacle. The scalar extraction approach used in many
functional analysis proofs assumes `star(c·1) = conj(c)·1`, giving `|c|² ≥ 0`.
Our star structure gives `c² ∈ ℂ`, which can have negative real part.

### Resolution Paths
1. **Work over ℝ**: Use `FreeAlgebra ℝ (Fin n)`, then ℂ-valued states separately
2. **Quotient algebra**: Take quotient by relations `star(c·1) = conj(c)·1`
3. **Restrict M**: Exclude "pathological" squares from M definition
4. **Axiomatize**: Add `MPositiveStateSet_nonempty` as hypothesis
5. **Different base state**: Use Hahn-Banach/Riesz with non-scalar-extraction base

### Current Status
File `State/NonEmptiness.lean` created with:
- ✓ `scalarExtraction` defined using `FreeAlgebra.algebraMapInv`
- ✓ `scalarExtraction_one`, `scalarExtraction_generator` proven
- ✗ `scalarExtraction_star_mul_self_nonneg` BLOCKED (counter-example exists)
- ✗ `MPositiveStateSet_nonempty` as sorry pending resolution

---

## 2026-01-24: RF-1 Complete - FreeStarAlgebra Now Uses ℝ

### Change Made
Refactored `FreeStarAlgebra n` from `FreeAlgebra ℂ (Fin n)` to `FreeAlgebra ℝ (Fin n)`.

### Why This Fixes Scalar Extraction
Over ℝ, for any scalar `c : ℝ`:
```
star (algebraMap c) * algebraMap c = algebraMap (c * c) = algebraMap (c²)
```
Since `c² ≥ 0` for all real `c`, scalar extraction maps every `star a * a` to a
nonnegative real, as required for M-positivity.

### Technical Details
- `FreeAlgebra.star_ι` still works: `star (ι j) = ι j` (generators self-adjoint)
- Proof of `isSelfAdjoint_generator` changed to use `unfold` + `exact`
- Import changed from `Mathlib.Data.Complex.Basic` to `Mathlib.Data.Real.Basic`

### Downstream Impact
All files importing `FreeStarAlgebra` need refactoring (RF-2 through RF-6):
- `QuadraticModule.lean` - change ℂ → ℝ in smul
- `MPositiveState.lean` - redesign for ℝ-linear functionals
- `NonEmptiness.lean` - scalar extraction should now work
