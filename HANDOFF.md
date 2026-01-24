# Handoff: 2026-01-24

## Completed This Session
- **AC-P3.2 COMPLETE**: Archimedean bound for states (73 LOC, 0 sorries)
  - Key theorems: `apply_star_mul_self_le_bound`, `apply_bound`, `apply_abs_le`
- **AC-P3.3 STRUCTURE DONE**: Generating cone lemma (112 LOC, 1 sorry)
  - Key theorems: `decomp_terms_in_M`, `quadraticModule_selfAdjoint_generating`
  - Sorry: `selfAdjoint_decomp` - **SOLUTION FOUND** (see below)

---

## PRIORITY: Fix selfAdjoint_decomp Sorry

### Location
`AfTests/ArchimedeanClosure/Boundedness/GeneratingCone.lean:77`

### Solution Summary
Use `Commute.mul_self_sub_mul_self_eq` (difference of squares for commuting elements).

### Granular Implementation Steps

#### Step 0: Check Import (May be optional)
```lean
-- At top of file, add if not transitively imported:
import Mathlib.Algebra.Ring.Commute
```

#### Step 1: Replace the `sorry` at line 77
Current code:
```lean
theorem selfAdjoint_decomp {x : FreeStarAlgebra n} (hx : IsSelfAdjoint x) :
    x = (1/4 : ℝ) • (star (1 + x) * (1 + x)) -
        (1/4 : ℝ) • (star (1 - x) * (1 - x)) := by
  have h1 : star (1 + x) = 1 + x := (isSelfAdjoint_one_add hx).star_eq
  have h2 : star (1 - x) = 1 - x := (isSelfAdjoint_one_sub hx).star_eq
  rw [h1, h2]
  sorry  -- <-- REPLACE THIS
```

#### Step 2: Add scalar factoring (after `rw [h1, h2]`)
```lean
  rw [← smul_sub]
```
**What this does**: Converts `a•p - a•q` to `a•(p-q)`, factoring out `(1/4)`

#### Step 3: Build the Commute hypothesis
```lean
  have hcomm : Commute (1 + x) (1 - x) := by
    apply Commute.add_left
    · exact (Commute.one_left _).sub_right (Commute.one_left x)
    · exact (Commute.one_right x).sub_right (Commute.refl x)
```
**What this does**: Proves `(1+x)` and `(1-x)` commute by decomposition

#### Step 4: Apply difference of squares
```lean
  rw [hcomm.mul_self_sub_mul_self_eq]
```
**What this does**: Rewrites `(1+x)²-(1-x)² = ((1+x)+(1-x))*((1+x)-(1-x))`

#### Step 5: Prove `(1+x) + (1-x) = 2`
```lean
  have sum_eq : (1 : FreeStarAlgebra n) + x + (1 - x) = 2 := by
    have h : (1 : FreeStarAlgebra n) + x + (1 - x) = (2 : ℕ) • (1 : FreeStarAlgebra n) := by abel
    rw [h, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
```
**What this does**: Uses `abel` to simplify, then converts ℕ-smul to ring multiplication

#### Step 6: Prove `(1+x) - (1-x) = 2*x`
```lean
  have diff_eq : (1 : FreeStarAlgebra n) + x - (1 - x) = 2 * x := by
    have h : (1 : FreeStarAlgebra n) + x - (1 - x) = (2 : ℕ) • x := by abel
    rw [h, nsmul_eq_mul, Nat.cast_ofNat]
```
**What this does**: Same pattern as above

#### Step 7: Rewrite with sum_eq and diff_eq
```lean
  rw [sum_eq, diff_eq]
```
**Goal is now**: `x = (1/4) • (2 * (2 * x))`

#### Step 8: Associate multiplications
```lean
  simp only [← mul_assoc]
```
**Goal is now**: `x = (1/4) • (2 * 2 * x)`

#### Step 9: Simplify `2 * 2 = 4`
```lean
  have h_four : (2 : FreeStarAlgebra n) * 2 = 4 := by norm_num
  rw [h_four]
```
**Goal is now**: `x = (1/4) • (4 * x)`

#### Step 10: Convert ring multiplication to scalar multiplication
```lean
  have h_scalar : (4 : FreeStarAlgebra n) * x = (4 : ℝ) • x := by
    rw [Algebra.smul_def]; rfl
  rw [h_scalar]
```
**Goal is now**: `x = (1/4) • (4 • x)`

#### Step 11: Combine scalars and finish
```lean
  rw [smul_smul]
  norm_num
```
**What this does**: `(1/4) • (4 • x) = (1/4 * 4) • x = 1 • x = x` ✓

### Complete Replacement Code

Replace lines 69-77 with:
```lean
theorem selfAdjoint_decomp {x : FreeStarAlgebra n} (hx : IsSelfAdjoint x) :
    x = (1/4 : ℝ) • (star (1 + x) * (1 + x)) -
        (1/4 : ℝ) • (star (1 - x) * (1 - x)) := by
  have h1 : star (1 + x) = 1 + x := (isSelfAdjoint_one_add hx).star_eq
  have h2 : star (1 - x) = 1 - x := (isSelfAdjoint_one_sub hx).star_eq
  rw [h1, h2, ← smul_sub]
  have hcomm : Commute (1 + x) (1 - x) := by
    apply Commute.add_left
    · exact (Commute.one_left _).sub_right (Commute.one_left x)
    · exact (Commute.one_right x).sub_right (Commute.refl x)
  rw [hcomm.mul_self_sub_mul_self_eq]
  have sum_eq : (1 : FreeStarAlgebra n) + x + (1 - x) = 2 := by
    have h : (1 : FreeStarAlgebra n) + x + (1 - x) = (2 : ℕ) • (1 : FreeStarAlgebra n) := by abel
    rw [h, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  have diff_eq : (1 : FreeStarAlgebra n) + x - (1 - x) = 2 * x := by
    have h : (1 : FreeStarAlgebra n) + x - (1 - x) = (2 : ℕ) • x := by abel
    rw [h, nsmul_eq_mul, Nat.cast_ofNat]
  rw [sum_eq, diff_eq]
  simp only [← mul_assoc]
  have h_four : (2 : FreeStarAlgebra n) * 2 = 4 := by norm_num
  rw [h_four]
  have h_scalar : (4 : FreeStarAlgebra n) * x = (4 : ℝ) • x := by
    rw [Algebra.smul_def]; rfl
  rw [h_scalar, smul_smul]
  norm_num
```

### Verification Checklist
- [ ] Add import if needed: `import Mathlib.Algebra.Ring.Commute`
- [ ] Replace lines 69-77 with the new proof
- [ ] Run `lake build AfTests.ArchimedeanClosure.Boundedness.GeneratingCone`
- [ ] Verify no errors
- [ ] Check LOC still ≤ 200

---

## Current State

### Phase 1-2: COMPLETE

| File | Status | LOC | Sorries |
|------|--------|-----|---------|
| Algebra/FreeStarAlgebra.lean | ✅ | 56 | 0 |
| Algebra/QuadraticModule.lean | ✅ | 93 | 0 |
| Algebra/Archimedean.lean | ✅ | 46 | 0 |
| State/MPositiveState.lean | ✅ | 100 | 0 |
| State/MPositiveStateProps.lean | ✅ | 63 | 0 |
| State/NonEmptiness.lean | ✅ | 149 | 0 |

### Phase 3: IN PROGRESS

| File | Status | LOC | Sorries |
|------|--------|-----|---------|
| Boundedness/CauchySchwarzM.lean | ✅ | 104 | 0 |
| Boundedness/ArchimedeanBound.lean | ✅ | 73 | 0 |
| Boundedness/GeneratingCone.lean | 🔶 | 112 | 1 (solution ready) |

---

## After Fix: Next Steps

1. **Complete Phase 3**: GeneratingCone.lean → 0 sorries
2. **Phase 4**: Topology (StateTopology, Compactness)
3. **Phase 5**: Seminorm (StateSeminorm, SeminormProps, Closure)

---

## Key Learnings Reference

See `docs/ArchimedeanClosure/LEARNINGS.md` section:
- **"SOLUTION FOUND - selfAdjoint_decomp via Commute Lemmas"**
- **"Non-Commutative Algebra Proof Patterns (Reference)"**

### Quick Pattern Reference

**Commute construction**:
```lean
have hcomm : Commute a b := by
  apply Commute.add_left  -- or add_right, sub_left, sub_right
  · exact (Commute.one_left _).sub_right (Commute.one_left x)
  · exact (Commute.one_right x).sub_right (Commute.refl x)
```

**Additive simplification in non-comm algebras**:
```lean
have h : expr = (n : ℕ) • z := by abel
rw [h, nsmul_eq_mul, Nat.cast_ofNat, ...]
```

**Scalar cancellation**:
```lean
have h : (c : R) * x = (c : ℝ) • x := by rw [Algebra.smul_def]; rfl
rw [h, smul_smul]
norm_num
```

---

## Files Modified This Session

- `AfTests/ArchimedeanClosure/Boundedness/ArchimedeanBound.lean` (NEW)
- `AfTests/ArchimedeanClosure/Boundedness/GeneratingCone.lean` (NEW, 1 sorry)
- `docs/ArchimedeanClosure/LEARNINGS.md` (extended with solution)
- `HANDOFF.md` (this file)
