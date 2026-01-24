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
