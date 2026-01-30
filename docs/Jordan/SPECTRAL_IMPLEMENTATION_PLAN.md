# Jordan Spectral Theorem Implementation Plan

**Goal:** Prove the spectral theorem for finite-dimensional formally real Jordan algebras.

**Target:** Eliminate sorries in `FormallyReal/Def.lean` and `FormallyReal/Spectrum.lean`.

---

## Phase 1: Finite-Dimensional Infrastructure (80 LOC)

### File: `AfTests/Jordan/FiniteDimensional.lean`

```lean
-- Step 1.1: Finite-dimensional Jordan algebra class (15 LOC)
class FinDimJordanAlgebra (J : Type*) [JordanAlgebra J] where
  finDim : FiniteDimensional ℝ J

-- Step 1.2: Rank function (10 LOC)
def jordanRank [FinDimJordanAlgebra J] : ℕ := Module.finrank ℝ J

-- Step 1.3: Basis existence (15 LOC)
theorem exists_basis [FinDimJordanAlgebra J] :
    ∃ (n : ℕ) (b : Fin n → J), LinearIndependent ℝ b ∧ Submodule.span ℝ (Set.range b) = ⊤

-- Step 1.4: Induction principle (20 LOC)
theorem finiteDim_induction [FinDimJordanAlgebra J] {P : J → Prop}
    (h0 : P 0) (hind : ∀ a e, IsIdempotent e → P a → P (a + e)) :
    ∀ a, P a

-- Step 1.5: Idempotent count bound (20 LOC)
theorem csoi_card_le_rank [FinDimJordanAlgebra J] (c : CSOI J n) :
    n ≤ jordanRank J
```

---

## Phase 2: Trace Bilinear Form (100 LOC)

### File: `AfTests/Jordan/Trace.lean`

```lean
-- Step 2.1: Abstract trace on Jordan algebras (25 LOC)
class JordanTrace (J : Type*) [JordanAlgebra J] where
  trace : J → ℝ
  trace_add : ∀ a b, trace (a + b) = trace a + trace b
  trace_smul : ∀ r a, trace (r • a) = r * trace a
  trace_jmul_comm : ∀ a b, trace (jmul a b) = trace (jmul b a)
  trace_jone_pos : 0 < trace jone

-- Step 2.2: Trace inner product (20 LOC)
def traceInner [JordanTrace J] (a b : J) : ℝ := trace (jmul a b)

theorem traceInner_symm [JordanTrace J] (a b : J) :
    traceInner a b = traceInner b a := trace_jmul_comm a b

-- Step 2.3: Non-degeneracy in formally real case (25 LOC)
theorem traceInner_self_pos [JordanTrace J] [FormallyRealJordan J] {a : J} (ha : a ≠ 0) :
    0 < traceInner a a

theorem traceInner_nondegenerate [JordanTrace J] [FormallyRealJordan J] :
    ∀ a, (∀ b, traceInner a b = 0) → a = 0

-- Step 2.4: Inner product space structure (30 LOC)
noncomputable instance jordanInnerProductSpace [JordanTrace J] [FormallyRealJordan J] :
    InnerProductSpace ℝ J where
  inner a b := traceInner a b
  norm_sq_eq_inner a := sorry  -- follows from positivity
  conj_symm a b := by simp [traceInner_symm]
  add_left a b c := by simp [traceInner, jmul_add, trace_add]
  smul_left r a b := by simp [traceInner, jmul_smul, trace_smul]
```

---

## Phase 3: Primitive Idempotents (90 LOC)

### File: `AfTests/Jordan/Primitive.lean`

```lean
-- Step 3.1: Primitive idempotent definition (15 LOC)
def IsPrimitive (e : J) : Prop :=
  IsIdempotent e ∧ e ≠ 0 ∧ ∀ f, IsIdempotent f → jmul e f = f → f = 0 ∨ f = e

-- Step 3.2: Primitivity characterization (25 LOC)
theorem isPrimitive_iff_minimal [FinDimJordanAlgebra J] {e : J} (he : IsIdempotent e) :
    IsPrimitive e ↔ ∀ f, IsIdempotent f → AreOrthogonal e f → jmul e f = 0 → f = 0

-- Step 3.3: Every idempotent decomposes into primitives (30 LOC)
theorem exists_primitive_decomp [FinDimJordanAlgebra J] [FormallyRealJordan J]
    {e : J} (he : IsIdempotent e) (hne : e ≠ 0) :
    ∃ (k : ℕ) (p : Fin k → J), (∀ i, IsPrimitive (p i)) ∧
      PairwiseOrthogonal p ∧ e = ∑ i, p i

-- Step 3.4: CSOI refines to primitive CSOI (20 LOC)
theorem csoi_refine_primitive [FinDimJordanAlgebra J] [FormallyRealJordan J]
    (c : CSOI J n) :
    ∃ (m : ℕ) (p : CSOI J m), m ≥ n ∧ ∀ i, IsPrimitive (p.idem i)
```

---

## Phase 4: Peirce Decomposition (120 LOC)

### File: `AfTests/Jordan/Peirce.lean`

```lean
-- Step 4.1: Peirce spaces for idempotent e (30 LOC)
def PeirceSpace (e : J) (λ : ℝ) : Submodule ℝ J :=
  { carrier := {a | jmul e a = λ • a}
    add_mem' := fun ha hb => by simp [jmul_add, ha, hb, smul_add]
    zero_mem' := by simp [jmul_zero]
    smul_mem' := fun r a ha => by simp [smul_jmul, ha, smul_comm] }

-- Step 4.2: Peirce eigenvalues are 0, 1/2, 1 (35 LOC)
theorem peirce_eigenvalues [FormallyRealJordan J] (e : J) (he : IsIdempotent e) (a : J) :
    a ∈ PeirceSpace e 0 ∨ a ∈ PeirceSpace e (1/2) ∨ a ∈ PeirceSpace e 1 ∨
    ∃ (a₀ a₁₂ a₁ : J), a₀ ∈ PeirceSpace e 0 ∧ a₁₂ ∈ PeirceSpace e (1/2) ∧
      a₁ ∈ PeirceSpace e 1 ∧ a = a₀ + a₁₂ + a₁

-- Step 4.3: Peirce decomposition is direct sum (25 LOC)
theorem peirce_direct_sum [FormallyRealJordan J] (e : J) (he : IsIdempotent e) :
    IsInternal (fun λ : Fin 3 => PeirceSpace e (![0, 1/2, 1] λ))

-- Step 4.4: Peirce multiplication rules (30 LOC)
theorem peirce_mult_rules [FormallyRealJordan J] (e : J) (he : IsIdempotent e) :
    -- P_0 * P_0 ⊆ P_0, P_1 * P_1 ⊆ P_1
    (∀ a b, a ∈ PeirceSpace e 0 → b ∈ PeirceSpace e 0 → jmul a b ∈ PeirceSpace e 0) ∧
    (∀ a b, a ∈ PeirceSpace e 1 → b ∈ PeirceSpace e 1 → jmul a b ∈ PeirceSpace e 1) ∧
    -- P_0 * P_1 = 0
    (∀ a b, a ∈ PeirceSpace e 0 → b ∈ PeirceSpace e 1 → jmul a b = 0) ∧
    -- P_1/2 * P_1/2 ⊆ P_0 + P_1
    (∀ a b, a ∈ PeirceSpace e (1/2) → b ∈ PeirceSpace e (1/2) →
      jmul a b ∈ PeirceSpace e 0 ⊔ PeirceSpace e 1)
```

---

## Phase 5: Eigenspaces & Spectral Projections (100 LOC)

### File: `AfTests/Jordan/Eigenspace.lean`

```lean
-- Step 5.1: Eigenspace of L_a (20 LOC)
def eigenspace (a : J) (λ : ℝ) : Submodule ℝ J :=
  LinearMap.ker (L a - λ • LinearMap.id)

-- Step 5.2: Eigenvalue definition (15 LOC)
def IsEigenvalue (a : J) (λ : ℝ) : Prop :=
  eigenspace a λ ≠ ⊥

def spectrum (a : J) : Set ℝ := {λ | IsEigenvalue a λ}

-- Step 5.3: Eigenspaces are orthogonal (25 LOC)
theorem eigenspace_orthogonal [JordanTrace J] [FormallyRealJordan J]
    (a : J) {λ μ : ℝ} (hne : λ ≠ μ) :
    ∀ v ∈ eigenspace a λ, ∀ w ∈ eigenspace a μ, traceInner v w = 0

-- Step 5.4: Spectral projections exist (20 LOC)
theorem exists_spectral_projection [FinDimJordanAlgebra J] [JordanTrace J] [FormallyRealJordan J]
    (a : J) (λ : ℝ) (hλ : IsEigenvalue a λ) :
    ∃ e : J, IsIdempotent e ∧ ∀ v, v ∈ eigenspace a λ ↔ jmul e v = v

-- Step 5.5: Finite spectrum (20 LOC)
theorem spectrum_finite [FinDimJordanAlgebra J] [FormallyRealJordan J] (a : J) :
    Set.Finite (spectrum a)
```

---

## Phase 6: Spectral Theorem (90 LOC)

### File: `AfTests/Jordan/SpectralTheorem.lean`

```lean
-- Step 6.1: Spectral decomposition existence (30 LOC)
theorem spectral_decomposition_exists [FinDimJordanAlgebra J] [JordanTrace J] [FormallyRealJordan J]
    (a : J) : ∃ sd : SpectralDecomp a, ∀ i, IsPrimitive (sd.csoi.idem i) := by
  -- Use finite spectrum + spectral projections
  -- Each eigenvalue λ gives idempotent e_λ
  -- Refine to primitive CSOI
  sorry

-- Step 6.2: Uniqueness (20 LOC)
theorem spectral_decomposition_unique [FinDimJordanAlgebra J] [JordanTrace J] [FormallyRealJordan J]
    (a : J) (sd₁ sd₂ : SpectralDecomp a) :
    Set.range sd₁.eigenvalues = Set.range sd₂.eigenvalues

-- Step 6.3: Square has squared eigenvalues (20 LOC)
theorem spectral_sq_eigenvalues [FinDimJordanAlgebra J] [JordanTrace J] [FormallyRealJordan J]
    {a : J} (sd : SpectralDecomp a) :
    ∃ sd_sq : SpectralDecomp (jsq a),
      sd_sq.csoi = sd.csoi ∧
      ∀ i, sd_sq.eigenvalues i = (sd.eigenvalues i) ^ 2

-- Step 6.4: Main theorem for sorries (20 LOC)
theorem sq_eigenvalues_nonneg [FinDimJordanAlgebra J] [JordanTrace J] [FormallyRealJordan J]
    {a : J} (sd : SpectralDecomp (jsq a)) :
    ∀ i, 0 ≤ sd.eigenvalues i := by
  -- eigenvalues of a² are squares of eigenvalues of a
  -- squares are non-negative
  intro i
  obtain ⟨sd_a, h_csoi, h_eig⟩ := spectral_sq_eigenvalues (sorry : SpectralDecomp a)
  -- sd.eigenvalues i = (sd_a.eigenvalues j)² for some j
  exact sq_nonneg _
```

---

## Phase 7: Sorry Elimination (40 LOC)

### File: `AfTests/Jordan/FormallyReal/Spectral.lean`

```lean
-- Step 7.1: Connect to existing SpectralDecomp (20 LOC)
theorem spectral_sq_eigenvalues_nonneg_impl [FinDimJordanAlgebra J] [JordanTrace J]
    [FormallyRealJordan J] {a : J} (sd : SpectralDecomp (jsq a)) :
    ∀ i, 0 ≤ sd.eigenvalues i :=
  sq_eigenvalues_nonneg sd

-- Step 7.2: Prove of_sq_eq_zero using spectral theorem (20 LOC)
theorem of_sq_eq_zero_spectral [FinDimJordanAlgebra J] [JordanTrace J]
    (h : ∀ a : J, jsq a = 0 → a = 0) : FormallyRealJordan J where
  sum_sq_eq_zero n a hsum := by
    -- Use spectral theorem: each jsq(a_i) has non-negative eigenvalues
    -- Sum = 0 means all eigenvalues = 0
    -- Hence each a_i = 0
    sorry
```

---

## Dependency Graph

```
Phase 1: FiniteDimensional.lean
    ↓
Phase 2: Trace.lean (uses Phase 1)
    ↓
Phase 3: Primitive.lean (uses Phase 1, 2)
    ↓
Phase 4: Peirce.lean (uses Phase 3)
    ↓
Phase 5: Eigenspace.lean (uses Phase 2, 4)
    ↓
Phase 6: SpectralTheorem.lean (uses Phase 5)
    ↓
Phase 7: FormallyReal/Spectral.lean (uses Phase 6)
```

---

## Estimated LOC by Phase

| Phase | File | LOC |
|-------|------|-----|
| 1 | FiniteDimensional.lean | 80 |
| 2 | Trace.lean | 100 |
| 3 | Primitive.lean | 90 |
| 4 | Peirce.lean | 120 |
| 5 | Eigenspace.lean | 100 |
| 6 | SpectralTheorem.lean | 90 |
| 7 | FormallyReal/Spectral.lean | 40 |
| **Total** | | **620** |

---

## Critical Mathlib Dependencies

```lean
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.DirectSum.Decomposition
```

---

## Risk Assessment

| Step | Risk | Mitigation |
|------|------|------------|
| 2.4 InnerProductSpace | Medium | May need custom structure instead |
| 4.2 Peirce eigenvalues | High | Classic result, needs careful proof |
| 5.4 Spectral projections | High | Key construction, follows Peirce theory |
| 6.1 Spectral decomposition | High | Main theorem, builds on all previous |

---

## Implementation Order

1. **Start with Phase 2** (Trace) - foundational bilinear form
2. **Then Phase 1** (FiniteDimensional) - simple infrastructure
3. **Phase 3** (Primitive) - uses both
4. **Phase 4** (Peirce) - the key technical work
5. **Phase 5** (Eigenspace) - builds on Peirce
6. **Phase 6-7** (Spectral) - final assembly

---

## Next Session Tasks

Create beads issues for each phase:
```bash
bd create --title="Jordan Phase 1: FiniteDimensional.lean" --type=task --priority=2
bd create --title="Jordan Phase 2: Trace.lean" --type=task --priority=2
bd create --title="Jordan Phase 3: Primitive.lean" --type=task --priority=2
bd create --title="Jordan Phase 4: Peirce.lean" --type=task --priority=2
bd create --title="Jordan Phase 5: Eigenspace.lean" --type=task --priority=2
bd create --title="Jordan Phase 6: SpectralTheorem.lean" --type=task --priority=1
bd create --title="Jordan Phase 7: Sorry elimination" --type=task --priority=1
```

Set dependencies:
```bash
bd dep add <phase2> <phase1>
bd dep add <phase3> <phase2>
bd dep add <phase4> <phase3>
bd dep add <phase5> <phase4>
bd dep add <phase6> <phase5>
bd dep add <phase7> <phase6>
```
