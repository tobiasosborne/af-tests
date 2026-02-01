# Sorry Elimination Plan: SpectralTheorem.lean

This document provides detailed elimination plans for the 5 sorries in `/home/tobiasosborne/Projects/af-tests/AfTests/Jordan/SpectralTheorem.lean`.

**File Overview:**
- Lines: 183
- Sorries: 5
- Dependencies: Eigenspace.lean, Primitive.lean, FormallyReal/Spectrum.lean

---

## Sorry 1: `spectral_decomposition_exists` (line 59)

### Current State
- **Goal:**
  ```lean
  ∃ sd : SpectralDecomp a, ∀ i, IsPrimitive (sd.csoi.idem i)
  ```
- **Context:**
  - `J : Type*` with `[JordanAlgebra J]`, `[FinDimJordanAlgebra J]`, `[JordanTrace J]`, `[FormallyRealJordan J]`
  - `a : J` arbitrary element
- **What it asserts:** Every element in a finite-dimensional formally real Jordan algebra has a spectral decomposition with primitive idempotents.

### Dependencies
- **Requires:**
  1. `eigenvalueSet_finite` (proven in Eigenspace.lean) - spectrum is finite
  2. `csoi_refine_primitive` (sorry in Primitive.lean) - refine any CSOI to primitive
  3. Eigenspace decomposition spans J (not yet proven)
  4. Construction of spectral projections from eigenspaces
- **Blocks:**
  - `spectral_decomposition_finset` (line 71)
  - `spectrum_eq_eigenvalueSet` (line 80)
  - Downstream spectral theory

### Elimination Strategy

#### Step 1 (30-40 LOC): Establish eigenspace-based decomposition
```lean
-- Use eigenvalueSet_finite to get a finite set of eigenvalues
obtain ⟨S, hS_finite⟩ := eigenvalueSet_finite a
-- Show eigenspaces are nonzero submodules
-- This requires proving eigenvalues have nontrivial eigenspaces
```

**Challenge:** The step from eigenspaces to orthogonal projections requires:
- Eigenspaces are orthogonal w.r.t. trace (proven: `eigenspace_orthogonal`)
- Eigenspaces span J (NOT YET PROVEN - requires spectral theory for L_a)
- Each eigenspace contains an idempotent projection

#### Step 2 (40-50 LOC): Construct CSOI from eigenspace projections
```lean
-- For each eigenvalue λ, construct projection e_λ onto eigenspace
-- Show these form a CSOI:
--   1. Each e_λ is idempotent
--   2. e_λ ∘ e_μ = 0 for λ ≠ μ
--   3. ∑ e_λ = 1
```

**Challenge:** This step is the crux of the spectral theorem. It requires either:
- Axiomatizing the projection operators
- Using trace inner product and orthogonal projection theory
- Importing matrix spectral theorem for concrete case

#### Step 3 (20-30 LOC): Apply primitive refinement
```lean
-- Once we have a CSOI, apply csoi_refine_primitive
obtain ⟨m, p, hm_ge, hprim⟩ := csoi_refine_primitive initial_csoi
-- Construct SpectralDecomp from refined primitive CSOI
```

### Risk Assessment
- **Difficulty:** HARD
- **Reason:** This is the main theorem of the file. It requires:
  1. Filling `csoi_refine_primitive` in Primitive.lean first
  2. Constructing spectral projections (deep result requiring ~100 LOC)
  3. Potentially axiomatizing spectral projections for abstract case

### Recommended Approach
**Option A (Abstract):** Add axiom to FormallyRealJordan requiring spectral decomposition exists.
**Option B (Concrete):** Prove for Hermitian matrices using mathlib's `Matrix.IsHermitian.spectral_theorem`, then lift.
**Option C (Full proof):** Implement Koecher-Vinberg theorem (~500 LOC) - see SPECTRAL_IMPLEMENTATION_PLAN.md.

---

## Sorry 2: `spectral_decomposition_finset` (line 71)

### Current State
- **Goal:**
  ```lean
  ∃ S e, (∀ r ∈ S, IsIdempotent (e r)) ∧
         (∀ r s, r ∈ S → s ∈ S → r ≠ s → AreOrthogonal (e r) (e s)) ∧
         ∑ r ∈ S, e r = jone ∧
         a = ∑ r ∈ S, r • e r
  ```
- **Context:**
  - Same as Sorry 1, plus
  - `sd : SpectralDecomp a` obtained from `spectral_decomposition_exists`
  - `h : ∀ i, IsPrimitive (sd.csoi.idem i)` from sorry 1

### Dependencies
- **Requires:**
  - `spectral_decomposition_exists` (Sorry 1)
  - Conversion from `Fin n`-indexed to `Finset`-indexed sums
- **Blocks:**
  - Alternative form of spectral theorem for users who prefer Finset API

### Elimination Strategy

#### Step 1 (20-30 LOC): Extract data from SpectralDecomp
```lean
-- Given sd : SpectralDecomp a with n idempotents and eigenvalues
-- Create S : Finset ℝ as the image of sd.eigenvalues
let S := Finset.univ.image sd.eigenvalues
-- Create e : ℝ → J that maps each eigenvalue to corresponding idempotent
```

#### Step 2 (20-30 LOC): Handle potential duplicate eigenvalues
```lean
-- If eigenvalues repeat, need to combine idempotents
-- For distinct eigenvalues: straightforward mapping
-- For repeated eigenvalues: sum the corresponding idempotents
```

**Challenge:** The SpectralDecomp structure allows repeated eigenvalues. Need to:
- Group idempotents by eigenvalue value
- Sum idempotents with same eigenvalue
- Show combined idempotent is still idempotent

#### Step 3 (15-20 LOC): Verify properties
```lean
-- Idempotent: sum of orthogonal idempotents is idempotent
-- Orthogonality: inherited from sd.csoi.orthog
-- Completeness: ∑ e = ∑ sd.csoi.idem = jone
-- Decomposition: a = ∑ λᵢ eᵢ (rearrange sum)
```

### Risk Assessment
- **Difficulty:** MEDIUM
- **Reason:** Mostly bookkeeping once Sorry 1 is filled. The eigenvalue grouping adds complexity but is straightforward with `Finset.sum_bij`.

### Recommended Approach
Use `Finset.sum_bij` or `Finset.sum_equiv` to convert between `Fin n` and `Finset ℝ` indices.

---

## Sorry 3: `spectrum_eq_eigenvalueSet` (line 80)

### Current State
- **Goal:**
  ```lean
  jordanSpectrum a sd = spectrum a
  ```
  where:
  - `jordanSpectrum a sd = Set.range sd.eigenvalues`
  - `spectrum a = eigenvalueSet a = {μ | IsEigenvalue a μ}`
- **Context:**
  - `sd : SpectralDecomp a`

### Dependencies
- **Requires:**
  1. Understanding that `sd.eigenvalues` gives eigenvalues of L_a
  2. Each eigenvalue in decomposition corresponds to a genuine eigenvalue
  3. All eigenvalues appear in decomposition (uses spanning property)
- **Blocks:**
  - `spectral_decomp_eigenvalues_eq_spectrum` (uses this directly)

### Elimination Strategy

#### Step 1 (15-20 LOC): Show ⊆ direction
```lean
-- For r ∈ jordanSpectrum a sd, show r ∈ spectrum a
intro r ⟨i, hi⟩
-- r = sd.eigenvalues i, need to show IsEigenvalue a r
-- Use: sd.csoi.idem i is a non-zero eigenvector with eigenvalue r
rw [mem_spectrum_iff, isEigenvalue_iff_exists_eigenvector]
use sd.csoi.idem i
constructor
· -- sd.csoi.idem i ≠ 0 (from idempotent + sum = 1)
  sorry
· -- jmul a (sd.csoi.idem i) = r • (sd.csoi.idem i)
  -- From decomposition: a ∘ eᵢ = (∑ λⱼ eⱼ) ∘ eᵢ = λᵢ eᵢ
  sorry
```

**Key insight:** For the second part, use:
- `a = ∑ j, sd.eigenvalues j • sd.csoi.idem j` (decomposition)
- `jmul (sd.csoi.idem j) (sd.csoi.idem i) = 0` for j ≠ i (orthogonality)
- `jmul (sd.csoi.idem i) (sd.csoi.idem i) = sd.csoi.idem i` (idempotent)

#### Step 2 (20-25 LOC): Show ⊇ direction
```lean
-- For r ∈ spectrum a, show r ∈ jordanSpectrum a sd
-- This requires that every eigenvalue of L_a appears in the decomposition
-- Uses: eigenspaces span J, decomposition is complete
```

**Challenge:** This direction requires knowing that the spectral decomposition captures ALL eigenvalues, not just some. This is the uniqueness part of spectral theorem.

### Risk Assessment
- **Difficulty:** MEDIUM-HARD
- **Reason:** The ⊆ direction is straightforward algebra. The ⊇ direction requires completeness of the decomposition (eigenspaces span), which is a non-trivial part of spectral theory.

### Recommended Approach
- Prove ⊆ first (purely algebraic)
- For ⊇, use that a complete CSOI gives an orthogonal decomposition of J, and any eigenvector must lie in one of the eigenspaces

---

## Sorry 4: `spectrum_sq` cases (lines 159, 162)

### Current State
- **Goal (line 159, mp direction):**
  ```lean
  r ∈ spectrum (jsq a) → r ∈ (· ^ 2) '' spectrum a
  ```
  i.e., eigenvalue of a² is the square of an eigenvalue of a.

- **Goal (line 162, mpr direction):**
  ```lean
  s ∈ spectrum a → (s ^ 2) ∈ spectrum (jsq a)
  ```
  i.e., square of eigenvalue of a is an eigenvalue of a².

### Dependencies
- **Requires:**
  1. `spectral_sq` (proven!) - a² has spectral decomposition with squared eigenvalues
  2. Connection between spectral decomposition eigenvalues and spectrum
  3. `spectrum_eq_eigenvalueSet` (Sorry 3)
- **Blocks:**
  - `spectrum_sq_nonneg` (uses this)

### Elimination Strategy for Both Cases

#### Step 1 (15-20 LOC): mpr direction (easier)
```lean
-- Given s ∈ spectrum a, show s² ∈ spectrum (jsq a)
-- s is an eigenvalue of a, so ∃ v ≠ 0, a ∘ v = s • v
rw [mem_spectrum_iff, isEigenvalue_iff_exists_eigenvector] at hs
obtain ⟨v, hv_ne, hv_eq⟩ := hs
-- Show v is eigenvector of a² with eigenvalue s²
use v, hv_ne
-- (a²) ∘ v = a ∘ (a ∘ v) = a ∘ (s • v) = s • (a ∘ v) = s • (s • v) = s² • v
calc jsq a ∘ v = jmul (jmul a a) v := rfl
  _ = jmul a (jmul a v) := by rw [jordan_identity_specific_form]  -- need this lemma
  _ = jmul a (s • v) := by rw [hv_eq]
  _ = s • jmul a v := by rw [smul_jmul]
  _ = s • (s • v) := by rw [hv_eq]
  _ = s² • v := by rw [smul_smul, sq]
```

**Challenge:** The step `jmul (jmul a a) v = jmul a (jmul a v)` is NOT immediate from Jordan identity. Need:
- Jordan identity: `(a² ∘ b) ∘ a = a² ∘ (b ∘ a)`
- For eigenvector: `a² ∘ v = a ∘ (a ∘ v)` requires `[L_a, L_{a²}] = 0` (proven as `L_L_jsq_comm`)

#### Step 2 (25-30 LOC): mp direction (harder)
```lean
-- Given r ∈ spectrum (jsq a), show ∃ s ∈ spectrum a, r = s²
-- Use spectral decomposition: if a = ∑ λᵢ eᵢ, then a² = ∑ λᵢ² eᵢ
-- r is eigenvalue of a², so r = λⱼ² for some j
-- λⱼ is eigenvalue of a, so s := λⱼ works
obtain ⟨sd_a, _⟩ := spectral_decomposition_exists a
obtain ⟨sd_sq, hsd_sq⟩ := spectral_sq a sd_a
-- r ∈ spectrum (jsq a) = Set.range sd_sq.eigenvalues
-- By spectral_sq, sd_sq.eigenvalues i = (sd_a.eigenvalues i)²
```

**Challenge:** Need to relate `spectrum (jsq a)` to the eigenvalues in `sd_sq`, which requires Sorry 3.

### Risk Assessment
- **Difficulty:** MEDIUM
- **Reason:** The mpr direction is mostly algebraic. The mp direction requires connecting spectrum to spectral decomposition eigenvalues (needs Sorry 3).

### Recommended Approach
1. Add helper lemma: `L_a_sq_apply : jmul (jsq a) v = jmul a (jmul a v)` (uses `L_L_jsq_comm`)
2. Prove mpr direction first
3. For mp direction, use spectral decomposition after Sorry 3 is filled

---

## Sorry 5: `sq_eigenvalues_nonneg` (line 173)

### Current State
- **Goal:**
  ```lean
  0 ≤ sd.eigenvalues i
  ```
- **Context:**
  - `sd : SpectralDecomp (jsq a)` - spectral decomposition of a²
  - `i : Fin sd.n`

### Dependencies
- **Requires:**
  1. `spectral_sq` (proven!) - eigenvalues of a² are squares of eigenvalues of a
  2. `spectrum_sq` (Sorry 4) - spectrum a² = {s² | s ∈ spectrum a}
  3. `spectrum_eq_eigenvalueSet` (Sorry 3)
- **Blocks:**
  - Positivity of squares in formally real Jordan algebras
  - Key for ordered Jordan algebra structure

### Elimination Strategy

#### Step 1 (10-15 LOC): Use spectral_sq
```lean
-- By spectral_sq, every eigenvalue of a² is a square of an eigenvalue of a
-- sd.eigenvalues i ∈ spectrum (jsq a) = {s² | s ∈ spectrum a}
have h_in_range : sd.eigenvalues i ∈ Set.range sd.eigenvalues := ⟨i, rfl⟩
-- Need: Set.range sd.eigenvalues ⊆ spectrum (jsq a)
-- This follows from spectrum_eq_eigenvalueSet (Sorry 3)
```

#### Step 2 (10-15 LOC): Apply sq_nonneg
```lean
-- Once we know sd.eigenvalues i = s² for some s ∈ ℝ:
rw [spectrum_sq] at h
obtain ⟨s, _, rfl⟩ := h
exact sq_nonneg s
```

### Risk Assessment
- **Difficulty:** EASY (once dependencies are filled)
- **Reason:** This is essentially a corollary of `spectrum_sq` (Sorry 4) plus the fact that squares of reals are non-negative.

### Recommended Approach
Fill Sorries 3 and 4 first, then this follows immediately.

---

## Dependency Graph

```
spectral_decomposition_exists (Sorry 1) [HARD]
        │
        ├──→ spectral_decomposition_finset (Sorry 2) [MEDIUM]
        │
        └──→ spectrum_eq_eigenvalueSet (Sorry 3) [MEDIUM-HARD]
                    │
                    └──→ spectrum_sq (Sorry 4) [MEDIUM]
                              │
                              └──→ sq_eigenvalues_nonneg (Sorry 5) [EASY]
```

## External Dependencies (in Primitive.lean)

The key blocker for Sorry 1 is `csoi_refine_primitive` in Primitive.lean, which in turn depends on:
- `primitive_peirce_one_dim_one` (1 sorry) - needs `lagrange_idempotent_in_peirce_one` completion
- `exists_primitive_decomp` (1 sorry) - induction on dimension
- `orthogonal_primitive_structure` (1 sorry) - H-O 2.9.4(iv)

## Recommended Session Sequence

| Session | Target | LOC | Focus |
|---------|--------|-----|-------|
| 87 | Fix `lagrange_idempotent_in_peirce_one` h_coeff_e | 20 | Complete algebraic computation in Primitive.lean |
| 88 | `primitive_peirce_one_dim_one` | 30 | Fill quadratic extraction sorry |
| 89 | `exists_primitive_decomp` | 40 | Induction proof |
| 90 | `csoi_refine_primitive` | 25 | Apply exists_primitive_decomp |
| 91 | `spectrum_eq_eigenvalueSet` (Sorry 3) | 40 | Both directions |
| 92 | `spectrum_sq` (Sorry 4) | 35 | Both mp and mpr cases |
| 93 | `sq_eigenvalues_nonneg` (Sorry 5) | 15 | Corollary |
| 94+ | `spectral_decomposition_exists` (Sorry 1) | 100+ | Main theorem |

---

## Summary Table

| Sorry | Theorem | Line | Difficulty | Key Blocker |
|-------|---------|------|------------|-------------|
| 1 | `spectral_decomposition_exists` | 59 | HARD | Spectral projection construction |
| 2 | `spectral_decomposition_finset` | 71 | MEDIUM | Sorry 1 + Finset conversion |
| 3 | `spectrum_eq_eigenvalueSet` | 80 | MEDIUM-HARD | Eigenspace spanning |
| 4 | `spectrum_sq` | 159, 162 | MEDIUM | `L_a_sq_apply` + Sorry 3 |
| 5 | `sq_eigenvalues_nonneg` | 173 | EASY | Sorries 3, 4 |

Total estimated LOC: 200-300 for sorries in this file, plus ~100 LOC in Primitive.lean dependencies.
