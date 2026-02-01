# Sorry Elimination Plan: Primitive.lean

This document provides detailed elimination plans for the 6 sorries in `AfTests/Jordan/Primitive.lean`.

---

## Sorry 1: `lagrange_idempotent_in_peirce_one` coefficient calculation (line 261)

### Current State
- **Goal**: `1 / Δ * (s + ((r - √Δ) / 2) ^ 2) = -(1 / √Δ) * ((r - √Δ) / 2)`
- **Context**:
  - `Δ := r^2 + 4*s` (discriminant of quadratic x² = r*x + s*e)
  - `μ := (r - √Δ) / 2` (smaller root)
  - `hΔ_pos : Δ > 0`
  - `hΔ_ne : Δ ≠ 0`
  - `hsqrt_ne : √Δ ≠ 0`
- **File location**: `AfTests/Jordan/Primitive.lean:252-261`

### Dependencies
- **Requires**: None (pure algebraic calculation on ℝ)
- **Blocks**: `lagrange_idempotent_in_peirce_one` completion, which blocks `primitive_peirce_one_dim_one`

### Elimination Strategy

#### Step 1 (15-20 LOC): Algebraic verification
- **Approach**: This is a pure real number calculation. Expand both sides and show equality.
- **Key algebraic facts**:
  - `μ = (r - √Δ)/2`, so `μ² = (r² - 2r√Δ + Δ)/4`
  - `s + μ² = s + (r² - 2r√Δ + Δ)/4`
  - Since `Δ = r² + 4s`, we have `4s = Δ - r²`
  - So `s + μ² = (Δ - r²)/4 + (r² - 2r√Δ + Δ)/4 = (2Δ - 2r√Δ)/4 = (Δ - r√Δ)/2`
  - LHS: `(1/Δ)(s + μ²) = (Δ - r√Δ)/(2Δ) = 1/2 - r/(2√Δ)`
  - RHS: `-μ/√Δ = -(r - √Δ)/(2√Δ) = -r/(2√Δ) + 1/2`
  - LHS = RHS ✓

- **Key lemmas**:
  - `Real.sq_sqrt hΔ_nonneg : √Δ * √Δ = Δ`
  - `field_simp` with `hΔ_ne` and `hsqrt_ne`

- **Lean pattern**:
```lean
have h_coeff_e : (1 / Δ) * (s + μ ^ 2) = -(1 / √Δ) * μ := by
  dsimp only [μ]
  -- Expand μ² and simplify s + μ²
  have h_expand : s + ((r - √Δ) / 2) ^ 2 = (Δ - r * √Δ) / 2 := by
    have hΔ_eq : Δ = r^2 + 4*s := rfl
    field_simp
    ring_nf
    -- May need to use hΔ_eq to substitute
  rw [h_expand]
  field_simp [hΔ_ne, hsqrt_ne]
  -- Goal: 2 * (Δ - r * √Δ) * √Δ = -Δ * 2 * (r - √Δ)
  rw [Real.sq_sqrt hΔ_nonneg]
  ring
```

### Risk Assessment
- **Difficulty**: EASY
- **Estimated total LOC**: 15-20
- **Potential blockers**: None - this is straightforward algebra

---

## Sorry 2: `primitive_peirce_one_dim_one` (line 322)

### Current State
- **Goal (case neg)**: `∃ a, a • e = x` (given `x ∈ PeirceSpace e 1`, `x ≠ 0`)
- **Context**:
  - `he : IsPrimitive e`
  - `x ∈ PeirceSpace e 1` (so `jmul e x = x`)
  - `hx_zero : ¬x = 0`
  - `hx2 : jsq x ∈ PeirceSpace e 1`
- **File location**: `AfTests/Jordan/Primitive.lean:301-322`

### Dependencies
- **Requires**:
  - Sorry 1 (`lagrange_idempotent_in_peirce_one`) must be filled first
  - `peirce_one_sq_nonpos_imp_zero` (already proven, line 170-196)
  - `primitive_idempotent_in_P1` (already proven, line 160-166)
  - Lemma to extract quadratic relation from finite dimension
- **Blocks**: `primitive_peirce_one_scalar` (depends on this for dim=1 result)

### Elimination Strategy

#### Step 1 (25-30 LOC): Extract quadratic relation
- **Approach**: Use finite dimensionality to show {e, x, x²} is linearly dependent, extracting coefficients r, s such that x² = r•x + s•e.
- **Key lemmas**:
  - `Module.finrank_pos` for positive dimension
  - `LinearMap.exists_relation_of_linearDependent` or similar
  - `FiniteDimensional.exists_smul_eq_of_mem_of_ne_zero` pattern

- **Lean pattern**:
```lean
-- P₁(e) is finite-dimensional (from FinDimJordanAlgebra)
haveI : FiniteDimensional ℝ (PeirceSpace e 1) := inferInstance
-- Get linear dependence of {e, x, x²}
-- Since all three are in P₁(e) and dim is finite, extract relation
-- Result: ∃ r s, x² = r • x + s • e
obtain ⟨r, s, hquad⟩ : ∃ r s : ℝ, jsq x = r • x + s • e := by
  -- Use finite dimension argument
  sorry  -- Sub-lemma needed
```

#### Step 2 (30-40 LOC): Discriminant case analysis
- **Approach**: Case split on `Δ = r² + 4*s`:
  - **Case Δ ≤ 0**: Use `peirce_one_sq_nonpos_imp_zero` on y = x - (r/2)•e
  - **Case Δ > 0**: Use `lagrange_idempotent_in_peirce_one` to get idempotent f, then `primitive_idempotent_in_P1` to get f = 0 or f = e

- **Key lemmas**:
  - `peirce_one_sq_nonpos_imp_zero` for Δ ≤ 0 case
  - `lagrange_idempotent_in_peirce_one` for Δ > 0 case
  - `primitive_idempotent_in_P1` to conclude

- **Lean pattern for Δ ≤ 0**:
```lean
rcases le_or_lt (r^2 + 4*s) 0 with hΔ_le | hΔ_pos
· -- Δ ≤ 0 case: y = x - (r/2)•e satisfies y² = (Δ/4)•e ≤ 0
  let y := x - (r/2) • e
  have hy_in : y ∈ PeirceSpace e 1 := Submodule.sub_mem _ hx (Submodule.smul_mem _ _ he_in)
  have hy_sq : jsq y = (r^2 + 4*s) / 4 • e := by
    -- Expand using x² = r•x + s•e
    sorry  -- Pure algebra
  have hcoef_le : (r^2 + 4*s) / 4 ≤ 0 := by linarith
  have hy_zero := peirce_one_sq_nonpos_imp_zero he.isIdempotent he.ne_zero hy_in hcoef_le hy_sq
  -- y = 0 means x = (r/2)•e
  use r/2
  calc x = y + (r/2) • e := by simp [y]
    _ = 0 + (r/2) • e := by rw [hy_zero]
    _ = (r/2) • e := by rw [zero_add]
```

- **Lean pattern for Δ > 0**:
```lean
· -- Δ > 0 case: Lagrange idempotent
  have ⟨hf_idem, hf_in⟩ := lagrange_idempotent_in_peirce_one he.isIdempotent hx hquad hΔ_pos
  -- By primitivity, f = 0 or f = e
  have hf_cases := primitive_idempotent_in_P1 he hf_idem hf_in
  rcases hf_cases with hf_zero | hf_eq_e
  · -- f = 0 case: x = μ•e
    use μ
    -- Extract from f = 0
    sorry
  · -- f = e case: x = λ•e
    use (r + √(r^2 + 4*s)) / 2
    sorry
```

### Risk Assessment
- **Difficulty**: MEDIUM-HARD
- **Estimated total LOC**: 60-80
- **Potential blockers**:
  - Extracting the quadratic relation from finite dimensionality (may need sub-lemma)
  - Algebraic manipulations in the discriminant cases

---

## Sorry 3: `orthogonal_primitive_peirce_sq` (line 390)

### Current State
- **Goal**: `∃ μ, 0 ≤ μ ∧ jsq a = μ • (e + f)`
- **Context**:
  - `he : IsPrimitive e`, `hf : IsPrimitive f`
  - `horth : AreOrthogonal e f` (so `jmul e f = 0`)
  - `a` is in both `PeirceSpace e (1/2)` and `PeirceSpace f (1/2)`
  - Have decompositions: `jsq a = c₀e + c₁e` and `jsq a = c₀f + c₁f`
  - `c₁e = r₁ • e` and `c₁f = r₂ • f` (by `primitive_peirce_one_scalar`)
- **File location**: `AfTests/Jordan/Primitive.lean:367-390`

### Dependencies
- **Requires**:
  - Sorry 2 must be filled (for `primitive_peirce_one_scalar`)
  - Understanding of Peirce multiplication rules for orthogonal idempotents
- **Blocks**: `orthogonal_primitive_structure` (H-O 2.9.4(iv))

### Elimination Strategy

#### Step 1 (20-30 LOC): Show r₁ = r₂ using symmetry
- **Approach**: Compute `jmul e (jsq a)` and `jmul f (jsq a)` two ways each:
  - Via decomposition: `jmul e (c₀e + c₁e) = c₁e = r₁ • e`
  - Similarly for f: `jmul f (c₀f + c₁f) = c₁f = r₂ • f`
  - Use symmetry in the hypotheses (e and f play symmetric roles)

- **Key insight from H-O**: For `a ∈ {eAf}` (Peirce 1/2 space for both), the structure is symmetric in e and f, so the scalar coefficients must match.

- **Key lemmas**:
  - `peirce_mult_P0_P0`, `peirce_mult_P0_P1`, `peirce_mult_P1_P1`
  - Orthogonality: `jmul e f = 0`
  - `e ∈ PeirceSpace f 0` and `f ∈ PeirceSpace e 0` (from orthogonality)

#### Step 2 (20-30 LOC): Show c₀e = r₂ • f and c₀f = r₁ • e
- **Approach**: The P₀(e) component of jsq a relates to f, and vice versa.
- **Key insight**: From the decomposition `jsq a = c₀e + c₁e = c₀f + c₁f` and uniqueness:
  - `c₁e` is the P₁(e) component, `c₀e` is P₀(e) component
  - Since f ∈ P₀(e) (orthogonality), the P₀(e) component should be a multiple of f

#### Step 3 (15-20 LOC): Show μ ≥ 0 using formal reality
- **Approach**: If `jsq a = μ • (e + f)` with `μ < 0`, this violates formal reality.
- **Key lemma**: If a = 0, μ = 0 ≥ 0. If a ≠ 0, then `jsq a ≠ 0`, so μ ≠ 0. If μ < 0, then
  `jsq a + jsq (√(-μ) • (e + f)) = 0` but both terms are nonzero, contradicting formal reality.

### Risk Assessment
- **Difficulty**: HARD
- **Estimated total LOC**: 60-80
- **Potential blockers**:
  - Understanding exactly how the P₀/P₁ decompositions interact across e and f
  - May need additional lemmas about Peirce spaces of orthogonal idempotents

---

## Sorry 4: `orthogonal_primitive_structure` (line 402)

### Current State
- **Goal**: `(∀ (a : J), jmul e a = (1/2) • a → jmul f a = (1/2) • a → a = 0) ∨ IsStronglyConnected e f`
- **Context**:
  - `he : IsPrimitive e`, `hf : IsPrimitive f`
  - `horth : AreOrthogonal e f`
- **File location**: `AfTests/Jordan/Primitive.lean:395-402`

### Dependencies
- **Requires**: Sorry 3 (`orthogonal_primitive_peirce_sq`)
- **Blocks**: Structure theory of Jordan algebras with primitive idempotents

### Elimination Strategy

#### Step 1 (15-20 LOC): Case split on existence of nonzero element
- **Approach**: Either all a in the shared Peirce 1/2 space are zero (first disjunct), or there exists nonzero a (leads to second disjunct).

- **Lean pattern**:
```lean
by_cases h : ∀ a : J, jmul e a = (1/2) • a → jmul f a = (1/2) • a → a = 0
· left; exact h
· right
  push_neg at h
  obtain ⟨a, ha_e, ha_f, ha_ne⟩ := h
  -- Construct strong connection
  sorry
```

#### Step 2 (25-35 LOC): Construct strongly connected witness
- **Approach**: Given nonzero `a` in the shared Peirce 1/2 space:
  1. By `orthogonal_primitive_peirce_sq`: `jsq a = μ • (e + f)` with `μ > 0` (μ = 0 would give a = 0)
  2. Let `v = μ^{-1/2} • a`
  3. Then `jsq v = μ⁻¹ • (μ • (e + f)) = e + f`
  4. v is in the Peirce 1/2 spaces for both e and f

- **Key lemmas**:
  - `orthogonal_primitive_peirce_sq` for the μ
  - `jsq_smul_idem` pattern for scalar multiplication
  - `FormallyRealJordan.sq_eq_zero_imp_zero` to show μ > 0

- **Lean pattern**:
```lean
-- Get μ with jsq a = μ • (e + f)
obtain ⟨μ, hμ_nonneg, ha_sq⟩ := orthogonal_primitive_peirce_sq he hf horth ⟨ha_e, ha_f⟩
-- Show μ > 0 (since a ≠ 0)
have hμ_pos : 0 < μ := by
  rcases hμ_nonneg.lt_or_eq with hμ_pos | hμ_zero
  · exact hμ_pos
  · exfalso
    rw [← hμ_zero, zero_smul] at ha_sq
    exact ha_ne (FormallyRealJordan.sq_eq_zero_imp_zero ha_sq)
-- Construct v
let v := (Real.sqrt μ)⁻¹ • a
have hv_sq : jsq v = e + f := by
  rw [jsq_def, smul_jmul, jmul_smul, smul_smul, ← jsq_def, ha_sq]
  simp [Real.sq_sqrt (le_of_lt hμ_pos)]
exact ⟨horth, v, sorry, sorry, hv_sq⟩  -- Need Peirce membership
```

### Risk Assessment
- **Difficulty**: MEDIUM
- **Estimated total LOC**: 40-55
- **Potential blockers**: Showing v remains in the Peirce 1/2 spaces after scaling

---

## Sorry 5: `exists_primitive_decomp` (line 435)

### Current State
- **Goal**: `∃ k p, (∀ (i : Fin k), IsPrimitive (p i)) ∧ PairwiseOrthogonal p ∧ e = ∑ i, p i`
- **Context**:
  - `he : IsIdempotent e`, `hne : e ≠ 0`
  - Finite-dimensional formally real Jordan algebra
- **File location**: `AfTests/Jordan/Primitive.lean:428-435`

### Dependencies
- **Requires**:
  - Definition and properties of primitive idempotents
  - Finite dimensionality (for induction argument)
- **Blocks**: `csoi_refine_primitive`

### Elimination Strategy

#### Step 1 (20-25 LOC): Strong induction setup on dimension
- **Approach**: Induct on `Module.finrank ℝ (PeirceSpace e 1)`:
  - Base: dim = 1 means e is primitive (by `primitive_peirce_one_dim_one`)
  - Step: dim > 1 means e is not primitive, so decompose

- **Lean pattern**:
```lean
-- Induction on dimension of P₁(e)
induction' hn : Module.finrank ℝ (PeirceSpace e 1) using Nat.strong_induction_on with d IH generalizing e
```

#### Step 2 (30-40 LOC): Base case (dim = 1)
- **Approach**: If `Module.finrank ℝ (PeirceSpace e 1) = 1`, then e is primitive.
- **Key insight**: By contrapositive of `primitive_peirce_one_dim_one`: if e is not primitive, dim > 1.

- **Lean pattern**:
```lean
rcases eq_or_lt_of_le (Nat.one_le_of_lt (Module.finrank_pos (R := ℝ) (M := PeirceSpace e 1))) with hd_eq | hd_gt
· -- d = 1: e is primitive
  use 1, ![e]
  constructor
  · intro i; fin_cases i; exact ⟨he, hne, fun f hf hef => sorry⟩
  constructor
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij
  · simp
· -- d > 1: decompose
  sorry
```

#### Step 3 (35-45 LOC): Inductive case - decomposition
- **Approach**: If e is not primitive, there exists proper idempotent f with jmul e f = f and 0 < f < e.
  - Decompose e = f + g where g = e - f is also idempotent and orthogonal to f
  - Apply IH to f and g (smaller dimensions)
  - Combine the primitive decompositions

- **Key lemmas**:
  - Existence of proper sub-idempotent (from non-primitivity)
  - `IsIdempotent.complement` for g = e - f
  - Dimension decreases for sub-idempotents

### Risk Assessment
- **Difficulty**: HARD
- **Estimated total LOC**: 90-120
- **Potential blockers**:
  - Proving dimension strictly decreases for proper sub-idempotents
  - Managing the Finset sum construction when combining decompositions

---

## Sorry 6: `csoi_refine_primitive` (line 442)

### Current State
- **Goal**: `∃ m p, m ≥ n ∧ ∀ (i : Fin m), IsPrimitive (p.idem i)`
- **Context**:
  - `c : CSOI J n` (complete system of orthogonal idempotents)
  - Finite-dimensional formally real Jordan algebra
- **File location**: `AfTests/Jordan/Primitive.lean:438-442`

### Dependencies
- **Requires**: Sorry 5 (`exists_primitive_decomp`)
- **Blocks**: Full spectral theory

### Elimination Strategy

#### Step 1 (35-45 LOC): Apply `exists_primitive_decomp` to each idempotent
- **Approach**: For each `c.idem i`:
  1. If zero, skip (or handle specially)
  2. If nonzero, apply `exists_primitive_decomp` to get primitive decomposition
  3. Combine all primitive decompositions

- **Key challenge**: Constructing the new CSOI with the right cardinality

- **Lean pattern**:
```lean
-- For each idempotent in c, get its primitive decomposition
have hdecomps : ∀ i, c.idem i ≠ 0 →
    ∃ k (p : Fin k → J), (∀ j, IsPrimitive (p j)) ∧ PairwiseOrthogonal p ∧ c.idem i = ∑ j, p j :=
  fun i hi => exists_primitive_decomp (c.is_idem i) hi
-- Combine decompositions
-- Total count m = ∑ᵢ kᵢ ≥ n (equality when all already primitive)
sorry
```

#### Step 2 (25-35 LOC): Construct the refined CSOI
- **Approach**:
  - Collect all primitive idempotents from all decompositions
  - Prove they form a CSOI (orthogonality inherited, sum preserved)

- **Key lemmas**:
  - Orthogonality: primitives from same decomposition are orthogonal (from `exists_primitive_decomp`)
  - Cross-orthogonality: primitives from different original idempotents are orthogonal (inherited from c.orthog)
  - Completeness: sum of all primitives = sum of original = jone

### Risk Assessment
- **Difficulty**: MEDIUM-HARD
- **Estimated total LOC**: 70-90
- **Potential blockers**:
  - Type-level manipulation of dependent sums
  - Proving the combined set remains pairwise orthogonal

---

## Summary Table

| Sorry | Theorem | Line | Difficulty | Est. LOC | Primary Blocker |
|-------|---------|------|------------|----------|-----------------|
| 1 | `lagrange_idempotent_in_peirce_one` (coeff) | 261 | EASY | 15-20 | None |
| 2 | `primitive_peirce_one_dim_one` | 322 | MEDIUM-HARD | 60-80 | Sorry 1, quadratic extraction |
| 3 | `orthogonal_primitive_peirce_sq` | 390 | HARD | 60-80 | Sorry 2, Peirce theory |
| 4 | `orthogonal_primitive_structure` | 402 | MEDIUM | 40-55 | Sorry 3 |
| 5 | `exists_primitive_decomp` | 435 | HARD | 90-120 | Dimension induction |
| 6 | `csoi_refine_primitive` | 442 | MEDIUM-HARD | 70-90 | Sorry 5 |

**Total estimated LOC**: 335-445

## Recommended Order of Attack

1. **Sorry 1** (EASY, no dependencies) - Start here for quick win
2. **Sorry 2** (blocks Sorry 3, 4) - Core H-O 2.9.4(ii) result
3. **Sorry 3** (needs Sorry 2) - H-O 2.9.4(iv) first part
4. **Sorry 4** (needs Sorry 3) - H-O 2.9.4(iv) completion
5. **Sorry 5** (independent of 3,4) - Decomposition theorem
6. **Sorry 6** (needs Sorry 5) - CSOI refinement

---

## References

- H-O = Hanche-Olsen & Stormer, *Jordan Operator Algebras* (1984)
- Section 2.9.4: Primitive idempotent characterization
- Section 2.6: Peirce decomposition
- Section 2.2.6: Classification of formally real fields over ℝ
- LEARNINGS.md: Sessions 83, 84 document partial progress on discriminant approach
