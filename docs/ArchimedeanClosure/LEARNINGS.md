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

---

## 2026-01-24: RF-2 Complete - QuadraticModule Uses Native ℝ-Scaling

### Change Made
Changed `(c : ℂ) • m` to `c • m` in `QuadraticModuleSet.smul_mem`.

### Why This Is Simpler
Over the ℝ-algebra, ℝ-scaling is native via the `Module ℝ (FreeAlgebra ℝ X)` instance.
No cast to ℂ needed - this was a workaround for the ℂ-algebra that's no longer needed.

---

## 2026-01-24: RF-3 Complete - Archimedean Updated

### Change Made
Changed `((N : ℝ) : ℂ) • 1` to `(N : ℝ) • 1` in `IsArchimedean` and `archimedeanBound_spec`.

---

## 2026-01-24: RF-4 Complete - MPositiveState Redesigned for ℝ-Linear Structure

### Change Made
Replaced ℂ-linear `MPositiveState` with ℝ-linear design:
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

### Key Design Decisions

1. **Codomain is ℝ, not ℂ**: No need for `map_m_real` - automatic.

2. **Explicit `map_star` condition**: The symmetry `φ(star a) = φ(a)` was previously
   deferred to MPositiveStateProps. Making it part of the structure is:
   - Mathematically cleaner (captures "state on *-algebra" directly)
   - Easier to work with (available immediately on any MPositiveState)
   - Matches the physics literature (states are symmetric functionals)

3. **No `selfAdjoint` subtype**: Considered using `selfAdjoint (FreeStarAlgebra n) →ₗ[ℝ] ℝ`
   but this requires manually instantiating `Module ℝ` on the subtype since:
   - `FreeAlgebra ℝ X` does NOT have `StarModule ℝ` (the automatic SMul instance)
   - Need to prove `star (c • a) = c • star a` manually using `FreeAlgebra.star_algebraMap`
   Using full algebra + `map_star` condition is simpler.

### Technical Note: star_smul for ℝ-Algebras
For `FreeAlgebra ℝ X`, we have `star (c • a) = c • star a` for `c : ℝ` because:
```lean
star (c • a) = star (algebraMap c * a)     -- Algebra.smul_def
            = star a * star (algebraMap c) -- star_mul
            = star a * algebraMap c        -- FreeAlgebra.star_algebraMap
            = algebraMap c * star a        -- Algebra.commutes
            = c • star a                   -- Algebra.smul_def
```
This could be used to define `Module ℝ (selfAdjoint (FreeAlgebra ℝ X))` if needed later.

---

## 2026-01-24: RF-5 Complete - MPositiveStateProps Simplified

### Change Made
Rewrote MPositiveStateProps for the ℝ-linear structure. Key simplifications:

1. **Removed `apply_real_of_isSelfAdjoint`**: Unnecessary - codomain is ℝ, all values real
2. **Removed `map_star` theorem**: Now an axiom in MPositiveState structure
3. **Removed `apply_star_mul_self_real`**: Unnecessary - codomain is ℝ
4. **Simplified `apply_add_star_real`** → `apply_self_adjoint_add`: φ(a + star a) = 2 * φ(a)

### Sorries Eliminated
- `apply_real_of_isSelfAdjoint` (was `sorry`) - removed entirely
- `map_star` (was `sorry`) - now an axiom, not a theorem

### New Lemmas
- `apply_self_adjoint_add`: φ(a + star a) = 2 * φ(a)
- `apply_self_adjoint_sub`: φ(a - star a) = 0
- `apply_isSelfAdjoint`: φ(star a) = φ(a) when a is self-adjoint
- `apply_decomposition`: φ(a) = (1/2) * φ(a + star a)

### Key Insight
Moving `map_star` from theorem to axiom was the right call - it eliminates complex
polarization proofs and makes the structure cleaner. Properties that were hard to
prove over ℂ become trivial over ℝ.

---

## 2026-01-24: RF-6 Complete - NonEmptiness Proven Over ℝ

### The Fix That Worked
With FreeStarAlgebra over ℝ (not ℂ), scalar extraction gives an M-positive state!

### Key Proof Insight
The crucial observation is that `scalarExtraction` is an **algebra homomorphism**.
This means:
```
scalarExtraction(star a * a) = scalarExtraction(star a) * scalarExtraction(a)
                              = scalarExtraction(a) * scalarExtraction(a)   [by scalarExtraction_star]
                              = scalarExtraction(a)²
```
And `x² ≥ 0` for all `x : ℝ`. This is a 3-line proof!

### Why This Was BLOCKED Over ℂ
Over ℂ, the same reasoning gives:
```
scalarExtraction(star a * a) = scalarExtraction(a)²
```
But for `a = algebraMap I` (imaginary unit), `scalarExtraction(a) = I`, so
`scalarExtraction(a)² = I² = -1`, which is **not** nonnegative!

### Theorems Proven
1. `scalarExtraction_star`: φ(star a) = φ(a) (by induction, star reverses/fixes)
2. `scalarExtraction_star_mul_self_nonneg`: φ(star a * a) ≥ 0 (algebra hom + sq ≥ 0)
3. `scalarExtraction_star_mul_generator_mul_self_nonneg`: φ(star a * g_j * a) = 0
4. `scalarExtraction_m_nonneg`: φ(m) ≥ 0 for all m ∈ M (induction on M)
5. `scalarState`: Constructs the canonical M-positive state
6. `MPositiveStateSet_nonempty`: S_M ≠ ∅

### Technical Note: Generator-Weighted Squares
For `star a * g_j * a`, scalar extraction gives 0 (not just ≥ 0) because:
- `scalarExtraction` is an algebra hom
- `scalarExtraction(g_j) = 0` for all generators
- So `scalarExtraction(... * g_j * ...) = ... * 0 * ... = 0`

This is actually cleaner than the pure squares case!

### Files Modified
- `AfTests/ArchimedeanClosure/State/NonEmptiness.lean` (149 LOC, 0 sorries)

---

## 2026-01-24: AC-P3.1 Complete - Cauchy-Schwarz for M-Positive States

### The Result
Proved the Cauchy-Schwarz inequality: φ(star b * a)² ≤ φ(star a * a) · φ(star b * b)

### Key Lemmas
1. `star_smul_real`: star(c • a) = c • star a for c : ℝ (manual proof via algebra structure)
2. `sesqForm_symm`: φ(star a * b) = φ(star b * a) (from map_star)
3. `quadratic_nonneg`: The quadratic discriminant setup
4. `cauchy_schwarz`: Main theorem via discriminant bound
5. `apply_sq_le`: Corollary φ(a)² ≤ φ(star a * a)

### Technical Note: star_smul for ℝ
FreeAlgebra doesn't have a StarModule instance, so we prove star_smul manually:
```lean
star (c • a) = star (algebraMap c * a)     -- Algebra.smul_def
            = star a * star (algebraMap c) -- star_mul
            = star a * algebraMap c        -- FreeAlgebra.star_algebraMap
            = algebraMap c * star a        -- Algebra.commutes
            = c • star a                   -- Algebra.smul_def
```

### Non-Commutative Expansion Challenge
`ring` tactic doesn't work for non-commutative algebras. Used explicit simp with:
- `add_mul`, `mul_add` - distribution
- `smul_mul_assoc`, `mul_smul_comm` - scalar-mul interaction
- `smul_add`, `smul_smul` - scalar distribution
- `abel` - final additive regrouping

### Files Created
- `AfTests/ArchimedeanClosure/Boundedness/CauchySchwarzM.lean` (104 LOC, 0 sorries)

---

## 2026-01-24: AC-P3.2 Complete - Archimedean Bound for States

### The Result
Proved: φ(star a * a) ≤ Nₐ, φ(a)² ≤ Nₐ, and |φ(a)| ≤ √Nₐ

### Key Proof Technique
The central argument is simple:
1. Archimedean property: N·1 - star a * a ∈ M
2. M-positivity: φ(N·1 - star a * a) ≥ 0
3. Linearity: N·φ(1) - φ(star a * a) ≥ 0
4. Normalization: N - φ(star a * a) ≥ 0 (since φ(1) = 1)

### Technical Note: FunLike Coercion vs LinearMap
When working with `MPositiveState` (which has `FunLike` instance), the coercion `φ a`
is syntactically different from `φ.toFun a`. This affects simp lemmas:
- `map_neg φ.toFun` works for `φ.toFun (-x) = -(φ.toFun x)`
- But `map_neg φ` does NOT work because the coercion is different

Solution: Use `congr 1` + `exact φ.toFun.map_neg _` instead of simp.

### Import Note
Required `Mathlib.Analysis.SpecialFunctions.Pow.Real` for `Real.sqrt` and related
lemmas like `Real.sq_sqrt` and `Real.sqrt_nonneg`.

### Files Created
- `AfTests/ArchimedeanClosure/Boundedness/ArchimedeanBound.lean` (73 LOC, 0 sorries)

---

## 2026-01-24: AC-P3.3 Structure Done - Generating Cone Lemma

### Status
Structure complete with 1 sorry for the algebraic identity.

### The Identity Challenge
The lemma `selfAdjoint_decomp` states: x = ¼(1+x)² - ¼(1-x)² for self-adjoint x.

Mathematically trivial:
- (1+x)² = 1 + 2x + x²
- (1-x)² = 1 - 2x + x²
- Difference = 4x, so ¼ of difference = x

### Why It's Hard in Lean
The issue is scalar multiplication type inference:
1. `1/4` in statement normalizes to `(4 : ℝ)⁻¹` after simp
2. `norm_num` doesn't recognize `4⁻¹ + 4⁻¹ + 4⁻¹ + 4⁻¹ = 1` without explicit type
3. `add_smul` has type inference issues when used in calc chains
4. Non-commutative algebra means `ring` tactic doesn't work

Attempted approaches:
- Direct calc chain with explicit `(4 : ℝ)⁻¹` annotations - type mismatch
- Using `set c := ...` to name the constant - still inference issues
- Working with `1/4` directly - division normalization causes problems

### Workaround
Left `sorry` on `selfAdjoint_decomp`. All downstream theorems use it correctly:
- `decomp_terms_in_M` - proven (star a * a ∈ M for any a)
- `decomp_term_selfAdjoint_add/sub` - proven
- `quadraticModule_selfAdjoint_generating` - uses decomp correctly

### Files Created
- `AfTests/ArchimedeanClosure/Boundedness/GeneratingCone.lean` (112 LOC, 1 sorry)

---

## 2026-01-24: SOLUTION FOUND - selfAdjoint_decomp via Commute Lemmas

### The Problem Recap
The identity `x = ¼(1+x)² - ¼(1-x)²` for self-adjoint x failed due to:
1. `ring` tactic doesn't work on non-commutative `FreeAlgebra`
2. Scalar `(1/4 : ℝ)` has type inference issues with `smul`
3. Direct expansion approaches hit additive grouping problems

### The Key Insight: Commute Lemmas

Mathlib provides `Commute.mul_self_sub_mul_self_eq` for non-commutative rings:
```lean
theorem mul_self_sub_mul_self_eq {a b : R} (h : Commute a b) :
    a * a - b * b = (a + b) * (a - b)
```

**Critical observation**: `(1+x)` and `(1-x)` commute in any ring because:
- `1` commutes with everything (`Commute.one_left`, `Commute.one_right`)
- `x` commutes with itself (`Commute.refl`)
- Commutativity distributes over `+` and `-` (`Commute.add_left/right`, `Commute.sub_left/right`)

### Building the Commute Hypothesis

```lean
have hcomm : Commute (1 + x) (1 - x) := by
  apply Commute.add_left
  · exact (Commute.one_left _).sub_right (Commute.one_left x)
  · exact (Commute.one_right x).sub_right (Commute.refl x)
```

Breakdown:
1. `Commute (1 + x) (1 - x)` splits into `Commute 1 (1-x)` and `Commute x (1-x)` via `add_left`
2. `Commute 1 (1-x)` splits into `Commute 1 1` and `Commute 1 x` via `sub_right`
3. `Commute x (1-x)` splits into `Commute x 1` and `Commute x x` via `sub_right`
4. All base cases are covered by `one_left`, `one_right`, `refl`

### The abel + nsmul Pattern

For simplifying `(1+x) + (1-x) = 2`:
```lean
have sum_eq : (1 : FreeStarAlgebra n) + x + (1 - x) = 2 := by
  have h : (1 : FreeStarAlgebra n) + x + (1 - x) = (2 : ℕ) • (1 : FreeStarAlgebra n) := by abel
  rw [h, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
```

**Why this works**:
- `abel` normalizes additive expressions and produces `(2 : ℕ) • 1` (natural number smul)
- `nsmul_eq_mul` converts `(n : ℕ) • a = (n : R) * a` in a ring
- `Nat.cast_ofNat` handles the `(2 : ℕ)` to `(2 : FreeStarAlgebra n)` cast
- `mul_one` finishes

For `(1+x) - (1-x) = 2 * x`:
```lean
have diff_eq : (1 : FreeStarAlgebra n) + x - (1 - x) = 2 * x := by
  have h : (1 : FreeStarAlgebra n) + x - (1 - x) = (2 : ℕ) • x := by abel
  rw [h, nsmul_eq_mul, Nat.cast_ofNat]
```

### Scalar Multiplication Cancellation

For `x = (1/4) • (2 * (2 * x))`:
```lean
-- Step 1: Associate multiplications
simp only [← mul_assoc]
-- Now: x = (1/4) • (2 * 2 * x)

-- Step 2: Simplify 2 * 2 = 4
have h_four : (2 : FreeStarAlgebra n) * 2 = 4 := by norm_num
rw [h_four]
-- Now: x = (1/4) • (4 * x)

-- Step 3: Convert ring multiplication to scalar multiplication
have h_scalar : (4 : FreeStarAlgebra n) * x = (4 : ℝ) • x := by
  rw [Algebra.smul_def]; rfl
rw [h_scalar]
-- Now: x = (1/4) • (4 • x)

-- Step 4: Combine scalars and simplify
rw [smul_smul]
-- Now: x = ((1/4) * 4) • x
norm_num
-- (1/4) * 4 = 1, so 1 • x = x ✓
```

**Key lemmas**:
- `Algebra.smul_def`: `c • a = algebraMap c * a` (converts ring mult to smul)
- `smul_smul`: `a • (b • x) = (a * b) • x`
- `norm_num`: Handles `(1/4) * 4 = 1`

### Complete Proof (Tested & Verified)

```lean
theorem selfAdjoint_decomp {x : FreeStarAlgebra n} (hx : IsSelfAdjoint x) :
    x = (1/4 : ℝ) • (star (1 + x) * (1 + x)) -
        (1/4 : ℝ) • (star (1 - x) * (1 - x)) := by
  -- Step 1: Use self-adjointness to simplify star terms
  have h1 : star (1 + x) = 1 + x := (isSelfAdjoint_one_add hx).star_eq
  have h2 : star (1 - x) = 1 - x := (isSelfAdjoint_one_sub hx).star_eq
  rw [h1, h2]
  -- Step 2: Factor out (1/4) scalar
  rw [← smul_sub]
  -- Step 3: Build Commute hypothesis and apply difference of squares
  have hcomm : Commute (1 + x) (1 - x) := by
    apply Commute.add_left
    · exact (Commute.one_left _).sub_right (Commute.one_left x)
    · exact (Commute.one_right x).sub_right (Commute.refl x)
  rw [hcomm.mul_self_sub_mul_self_eq]
  -- Step 4: Simplify (1+x) + (1-x) = 2 and (1+x) - (1-x) = 2*x
  have sum_eq : (1 : FreeStarAlgebra n) + x + (1 - x) = 2 := by
    have h : (1 : FreeStarAlgebra n) + x + (1 - x) = (2 : ℕ) • (1 : FreeStarAlgebra n) := by abel
    rw [h, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  have diff_eq : (1 : FreeStarAlgebra n) + x - (1 - x) = 2 * x := by
    have h : (1 : FreeStarAlgebra n) + x - (1 - x) = (2 : ℕ) • x := by abel
    rw [h, nsmul_eq_mul, Nat.cast_ofNat]
  rw [sum_eq, diff_eq]
  -- Step 5: Simplify (1/4) • (2 * (2 * x)) = x
  simp only [← mul_assoc]
  have h_four : (2 : FreeStarAlgebra n) * 2 = 4 := by norm_num
  rw [h_four]
  have h_scalar : (4 : FreeStarAlgebra n) * x = (4 : ℝ) • x := by
    rw [Algebra.smul_def]; rfl
  rw [h_scalar, smul_smul]
  norm_num
```

### Required Import

```lean
import Mathlib.Algebra.Ring.Commute  -- For Commute lemmas
```

This may already be transitively imported via other Algebra imports.

### Mathlib Lemmas Used (Summary)

| Lemma | Location | Purpose |
|-------|----------|---------|
| `Commute.one_left` | `Mathlib.Algebra.Group.Commute.Defs` | 1 commutes left |
| `Commute.one_right` | `Mathlib.Algebra.Group.Commute.Defs` | 1 commutes right |
| `Commute.refl` | `Mathlib.Algebra.Group.Commute.Defs` | Self-commutativity |
| `Commute.add_left` | `Mathlib.Algebra.Ring.Commute` | Sum commutes |
| `Commute.sub_right` | `Mathlib.Algebra.Ring.Commute` | Difference commutes |
| `Commute.mul_self_sub_mul_self_eq` | `Mathlib.Algebra.Ring.Commute` | Diff of squares |
| `smul_sub` | `Mathlib.Algebra.Module.Defs` | `a•p - a•q = a•(p-q)` |
| `smul_smul` | `Mathlib.Algebra.Module.Defs` | `a•(b•x) = (a*b)•x` |
| `nsmul_eq_mul` | `Mathlib.Algebra.Ring.Defs` | `(n:ℕ)•x = n*x` |
| `Algebra.smul_def` | `Mathlib.Algebra.Algebra.Basic` | `c•a = algebraMap c * a` |

### Why Previous Approaches Failed

1. **Direct `ring`**: Non-commutative algebra, `ring` assumes commutativity
2. **Manual expansion with `simp [add_mul, mul_add]`**: Works for expansion but scalars messy
3. **Calc chains with `(4 : ℝ)⁻¹`**: Type inference couldn't unify scalar types
4. **Using `add_smul` directly**: Type class resolution for Module instance problematic

### Lessons Learned

1. **Commute lemmas are powerful** for non-commutative identities when elements do commute
2. **`abel` + `nsmul_eq_mul` pattern** handles additive simplification in non-comm algebras
3. **`Algebra.smul_def` + `smul_smul`** cleanly handles scalar multiplication
4. **`norm_num`** works on the scalar level even when `ring` fails on the algebra

---

## 2026-01-24: Non-Commutative Algebra Proof Patterns (Reference)

### Pattern 1: Expansion in Non-Commutative Algebras

When `ring` doesn't work, use:
```lean
simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
abel
```

**Used in**: `CauchySchwarzM.lean:65`

### Pattern 2: Additive Simplification

When you need `x + y + ... = n • z` in a non-commutative ring:
```lean
have h : expr = (n : ℕ) • z := by abel
rw [h, nsmul_eq_mul, Nat.cast_ofNat, ...]
```

### Pattern 3: Scalar Multiplication Cancellation

When you need `(a : ℝ) • ((b : R) * x) = (a * b) • x`:
```lean
have h : (b : R) * x = (b : ℝ) • x := by rw [Algebra.smul_def]; rfl
rw [h, smul_smul]
```

### Pattern 4: Commutativity in Non-Commutative Rings

Build `Commute a b` hypotheses using:
- `Commute.one_left`, `Commute.one_right` (unit commutes)
- `Commute.refl` (self-commutation)
- `Commute.add_left`, `Commute.add_right` (distribute over +)
- `Commute.sub_left`, `Commute.sub_right` (distribute over -)
- `Commute.neg_left`, `Commute.neg_right` (negation)

Then use `Commute.mul_self_sub_mul_self_eq`, `Commute.add_sq`, etc.
