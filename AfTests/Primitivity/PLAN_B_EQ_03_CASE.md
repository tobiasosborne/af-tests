# Implementation Plan: B' = {0, 3} Case in case_n_geq_2

**File**: `Lemma11_5_Case2.lean`
**Line**: 322
**Context**: Inside `case_n_geq_2`, when B' = {0, 3}

---

## Goal State at Line 322

```lean
⊢ False
```

**Available hypotheses:**
- `hB'_eq_03 : B' = {⟨0, ⋯⟩, ⟨3, ⋯⟩}`
- `hx_in : x ∈ {⟨0, ⋯⟩, ⟨3, ⋯⟩}`
- `hx_out : (g₁ n k m) ((g₁ n k m) x) ∉ {⟨0, ⋯⟩, ⟨3, ⋯⟩}` (g₁²(x) ∉ {0, 3})
- `h0_in_orbit : ⟨0, ⋯⟩ ∈ B'`
- `hB_in_BS : B ∈ BS.blocks`
- `hInv : IsHInvariant BS`
- `j : ℤ` with `B' = g₁^j '' B`

---

## Proof Strategy

The key insight: g₁²(0) = 3, so g₁² maps an element of B' into B', meaning g₁²(B') ∩ B' ≠ ∅. But we also have an element x ∈ B' with g₁²(x) ∉ B', so g₁²(B') ≠ B'. This violates block dichotomy.

---

## Step-by-Step Implementation

### Step 1: Get B' ∈ BS.blocks

**Lemma needed**: `g₁_zpow_preserves_blocks` ✓ EXISTS

**Code**:
```lean
have hB'_in_BS : B' ∈ BS.blocks := g₁_zpow_preserves_blocks BS hInv B hB_in_BS j
```

**Lines**: 1

---

### Step 2: Show g₁²(B') ∈ BS.blocks

Since g₁² = g₁^2, we can use H-invariance directly.

**Code**:
```lean
have hg₁sq_B'_in_BS : (g₁ n k m ^ (2 : ℕ)) '' B' ∈ BS.blocks := by
  have hg₁_in_H : g₁ n k m ∈ H n k m := g₁_mem_H n k m
  exact hInv.1 _ (hInv.1 _ hB'_in_BS)
```

**Lines**: 3

---

### Step 3: Show g₁²(B') ≠ B' (using hx_out)

We have x ∈ B' and g₁²(x) ∉ B'.

**Code**:
```lean
have hg₁sq_B'_ne : (g₁ n k m ^ (2 : ℕ)) '' B' ≠ B' := by
  intro h_eq
  have hx_in_B' : x ∈ B' := by rw [hB'_eq_03]; exact hx_in
  have hg₁sq_x_in : (g₁ n k m ^ (2 : ℕ)) x ∈ (g₁ n k m ^ (2 : ℕ)) '' B' :=
    Set.mem_image_of_mem _ hx_in_B'
  rw [h_eq] at hg₁sq_x_in
  simp only [pow_two, Equiv.Perm.coe_mul, Function.comp_apply] at hx_out
  rw [hB'_eq_03] at hg₁sq_x_in
  exact hx_out hg₁sq_x_in
```

**Lines**: 8

---

### Step 4: Show g₁²(B') ∩ B' ≠ ∅ (using g₁²(0) = 3)

We have 0 ∈ B' and g₁²(0) = 3 ∈ B'.

**Lemma needed**: `OrbitCore.g₁_pow2_elem0_eq_elem3` ✓ EXISTS

**Code**:
```lean
have h_not_disjoint : ¬Disjoint ((g₁ n k m ^ (2 : ℕ)) '' B') B' := by
  rw [Set.not_disjoint_iff]
  use ⟨3, by omega⟩
  constructor
  · -- 3 ∈ g₁²(B') because g₁²(0) = 3 and 0 ∈ B'
    rw [hB'_eq_03] at h0_in_orbit ⊢
    have h0_in : (⟨0, by omega⟩ : Omega n k m) ∈ ({⟨0, by omega⟩, ⟨3, by omega⟩} : Set _) :=
      Set.mem_insert _ _
    use ⟨0, by omega⟩, h0_in
    exact OrbitCore.g₁_pow2_elem0_eq_elem3
  · -- 3 ∈ B' = {0, 3}
    rw [hB'_eq_03]
    exact Set.mem_insert_of_mem _ rfl
```

**Lines**: 12

---

### Step 5: Apply block dichotomy for contradiction

Block dichotomy says: for blocks B₁, B₂ ∈ BS.blocks with B₁ ≠ B₂, they are disjoint.

**Code**:
```lean
have hDichotomy := BS.isPartition.1 hg₁sq_B'_in_BS hB'_in_BS hg₁sq_B'_ne
exact h_not_disjoint hDichotomy
```

**Lines**: 2

---

## Complete Code Block

```lean
-- Step 1: B' ∈ BS.blocks
have hB'_in_BS : B' ∈ BS.blocks := g₁_zpow_preserves_blocks BS hInv B hB_in_BS j
-- Step 2: g₁²(B') ∈ BS.blocks
have hg₁sq_B'_in_BS : (g₁ n k m ^ (2 : ℕ)) '' B' ∈ BS.blocks := by
  exact hInv.1 _ (hInv.1 _ hB'_in_BS)
-- Step 3: g₁²(B') ≠ B'
have hg₁sq_B'_ne : (g₁ n k m ^ (2 : ℕ)) '' B' ≠ B' := by
  intro h_eq
  have hx_in_B' : x ∈ B' := by rw [hB'_eq_03]; exact hx_in
  have hg₁sq_x_in : (g₁ n k m ^ (2 : ℕ)) x ∈ (g₁ n k m ^ (2 : ℕ)) '' B' :=
    Set.mem_image_of_mem _ hx_in_B'
  rw [h_eq] at hg₁sq_x_in
  simp only [pow_two, Equiv.Perm.coe_mul, Function.comp_apply] at hx_out
  rw [hB'_eq_03] at hg₁sq_x_in
  exact hx_out hg₁sq_x_in
-- Step 4: g₁²(B') ∩ B' ≠ ∅
have h_not_disjoint : ¬Disjoint ((g₁ n k m ^ (2 : ℕ)) '' B') B' := by
  rw [Set.not_disjoint_iff]
  use ⟨3, by omega⟩
  constructor
  · rw [hB'_eq_03] at h0_in_orbit ⊢
    have h0_in : (⟨0, by omega⟩ : Omega n k m) ∈ ({⟨0, by omega⟩, ⟨3, by omega⟩} : Set _) :=
      Set.mem_insert _ _
    use ⟨0, by omega⟩, h0_in
    exact OrbitCore.g₁_pow2_elem0_eq_elem3
  · rw [hB'_eq_03]
    exact Set.mem_insert_of_mem _ rfl
-- Step 5: Contradiction
have hDichotomy := BS.isPartition.1 hg₁sq_B'_in_BS hB'_in_BS hg₁sq_B'_ne
exact h_not_disjoint hDichotomy
```

---

## Summary

| Step | Description | Lines | Lemmas Needed |
|------|-------------|-------|---------------|
| 1 | B' ∈ BS.blocks | 1 | `g₁_zpow_preserves_blocks` ✓ |
| 2 | g₁²(B') ∈ BS.blocks | 2 | H-invariance |
| 3 | g₁²(B') ≠ B' | 8 | hx_out (given) |
| 4 | g₁²(B') ∩ B' ≠ ∅ | 10 | `g₁_pow2_elem0_eq_elem3` ✓ |
| 5 | Contradiction | 2 | Block dichotomy |

**Total**: ~23 lines

**All required lemmas exist.** This is ready for implementation.

---

## Potential Issues

1. **Type annotations**: May need explicit `(⟨0, by omega⟩ : Omega n k m)` annotations
2. **Import**: Ensure `OrbitCore.g₁_pow2_elem0_eq_elem3` is accessible (should be via imports)
3. **Block system API**: Verify `BS.isPartition.1` gives the right form of dichotomy

---

## Next Smallest Step

**Copy the complete code block above and replace the `sorry` at line 322.**

If build errors occur, they will likely be minor type annotation issues.
