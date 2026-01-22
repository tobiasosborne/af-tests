# Plan: Eliminate Remaining Sorries in Lemma 11.5

**Date**: 2026-01-22 (Updated)
**Status**: Infrastructure COMPLETE - Ready to fill sorries

---

## Executive Summary

All infrastructure is now in place. The 6 sorries can be filled with 4-10 lines each using a standard pattern.

---

## Current State

### Build Status: **PASSING**

### Sorries Count: 6

**Lemma11_5_Case2.lean** (3 sorries):
- Line 321: B' = {0,3} case - needs g₁ block dichotomy
- Line 363: |B'| > 2 case - needs g₂ block dichotomy
- Line 389: y ≠ 3 case - needs g₂ block dichotomy

**Lemma11_5_SymmetricCases.lean** (3 sorries):
- Line 306: k >= 2 symmetric case
- Line 346: m >= 2 symmetric case (sub-case)
- Line 363: m >= 2 symmetric case (sub-case)

---

## Infrastructure Status: COMPLETE

### NEW: `Lemma11_5_ZpowBlocks.lean` (57 lines) - DONE

Created this session. Provides the key lemmas needed by all 6 sorries:

```lean
theorem g₁_zpow_preserves_blocks (BS : BlockSystemOn n k m) (hInv : IsHInvariant BS)
    (B : Set (Omega n k m)) (hB : B ∈ BS.blocks) (j : ℤ) :
    (g₁ n k m ^ j) '' B ∈ BS.blocks

theorem g₂_zpow_preserves_blocks (BS : BlockSystemOn n k m) (hInv : IsHInvariant BS)
    (B : Set (Omega n k m)) (hB : B ∈ BS.blocks) (j : ℤ) :
    (g₂ n k m ^ j) '' B ∈ BS.blocks

theorem g₃_zpow_preserves_blocks (BS : BlockSystemOn n k m) (hInv : IsHInvariant BS)
    (B : Set (Omega n k m)) (hB : B ∈ BS.blocks) (j : ℤ) :
    (g₃ n k m ^ j) '' B ∈ BS.blocks
```

### Key Discovery: Infrastructure Already Existed

The plan originally called for writing `block_system_invariant_inv` from scratch. However, this already exists in `Lemma11_4_Helpers.lean`:

- `inv_image_mem_blocks` - σ⁻¹ preserves blocks (with finiteness argument)
- `zpow_image_mem_blocks` - σ^j preserves blocks for j : ℤ

The new `Lemma11_5_ZpowBlocks.lean` simply wraps these with the H-invariance context.

### Other Available Infrastructure

**In `Lemma11_5_OrbitInfra.lean`:**
- `set_0_3_not_g₁_closed` - ∃ x ∈ {0,3}, g₁²(x) ∉ {0,3}
- `g₂_fixes_in_supp_g₁_not_0_3` - x ∈ supp(g₁) \ {0,3} → g₂(x) = x

**In `Lemma11_5_OrbitContinuation.lean`:**
- `g₁_sq_elem3_eq_elem6` - g₁²(3) = 6 when n >= 1

**In `Lemma11_5_Defs.lean`:**
- `fixed_point_blocks_intersect` - x fixed by σ and x ∈ B → x ∈ σ(B) ∩ B

---

## NEXT STEPS: Fill the 6 Sorries

### Pattern for Sorries 2, 3 (Lines 363, 389) - EASIEST

These follow the identical pattern. Context at each site:
- `B' = (g₁ n k m ^ j) '' B` is defined
- `j : ℤ` is in scope (from `IsCycle.exists_zpow_eq`)
- `hB_in_BS : B ∈ BS.blocks` is in scope
- `hInv : IsHInvariant BS` is in scope
- `hg₂_B'_ne : g₂ n k m '' B' ≠ B'` is established
- A witness point is in both B' and g₂(B')

**Fill-in code for Line 363:**
```lean
-- Replace the sorry at line 363 with:
have hB'_in_BS : B' ∈ BS.blocks := g₁_zpow_preserves_blocks BS hInv B hB_in_BS j
have hg₂B'_in_BS : g₂ n k m '' B' ∈ BS.blocks := hInv.2.1 B' hB'_in_BS
have hDisj : Disjoint B' (g₂ n k m '' B') := by
  apply BS.isPartition.1.elim hB'_in_BS hg₂B'_in_BS
  exact fun h => hg₂_B'_ne h.symm
exact Set.disjoint_iff.mp hDisj ⟨hz_in_B', hz_in_g₂B'⟩
```

**Fill-in code for Line 389:**
```lean
-- Replace the sorry at line 389 with:
have hB'_in_BS : B' ∈ BS.blocks := g₁_zpow_preserves_blocks BS hInv B hB_in_BS j
have hg₂B'_in_BS : g₂ n k m '' B' ∈ BS.blocks := hInv.2.1 B' hB'_in_BS
have hDisj : Disjoint B' (g₂ n k m '' B') := by
  apply BS.isPartition.1.elim hB'_in_BS hg₂B'_in_BS
  exact fun h => hg₂_B'_ne h.symm
exact Set.disjoint_iff.mp hDisj ⟨hy_in_B', hy_in_g₂B'⟩
```

### Pattern for Sorry 1 (Line 321) - SLIGHTLY HARDER

This is the B' = {0, 3} case. The argument uses g₁ dichotomy (not g₂).

**Context at line 321:**
- `hB'_eq_03 : B' = {⟨0, _⟩, ⟨3, _⟩}` is established
- `set_0_3_not_g₁_closed` gives: ∃ x ∈ {0,3}, g₁²(x) ∉ {0,3}

**Mathematical argument:**
1. B' ∈ BS.blocks (via g₁_zpow_preserves_blocks)
2. g₁²(B') ∈ BS.blocks (via H-invariance, g₁² = g₁ * g₁)
3. g₁²(B') ≠ B' (from set_0_3_not_g₁_closed: some element leaves)
4. g₁²(0) = 3 ∈ B' (need to verify: g₁²(0) = g₁(g₁(0)) = g₁(5) = 3)
5. So 3 ∈ g₁²(B') ∩ B', contradicting disjointness

**Fill-in code for Line 321:**
```lean
-- Replace the sorry at line 321 with:
have hB'_in_BS : B' ∈ BS.blocks := g₁_zpow_preserves_blocks BS hInv B hB_in_BS j
-- g₁² preserves blocks (compose twice)
have hg₁sq_B'_in_BS : (g₁ n k m)^2 '' B' ∈ BS.blocks := by
  have h1 : g₁ n k m '' B' ∈ BS.blocks := hInv.1 B' hB'_in_BS
  exact hInv.1 _ h1
-- g₁²(B') ≠ B' because ∃ x ∈ B' with g₁²(x) ∉ B'
have hg₁sq_ne : (g₁ n k m)^2 '' B' ≠ B' := by
  intro h_eq
  rw [hB'_eq_03] at h_eq hx_in hx_out
  have hx_in_image : (g₁ n k m)^2 x ∈ (g₁ n k m)^2 '' {⟨0, _⟩, ⟨3, _⟩} :=
    Set.mem_image_of_mem _ hx_in
  rw [h_eq] at hx_in_image
  exact hx_out hx_in_image
-- g₁²(0) = 3 ∈ B' (computational: g₁(0)=5, g₁(5)=3)
have h0_in_B' : (⟨0, by omega⟩ : Omega n k m) ∈ B' := by
  rw [hB'_eq_03]; left; rfl
have hg₁sq_0 : (g₁ n k m)^2 ⟨0, by omega⟩ = ⟨3, by omega⟩ := by native_decide
have h3_in_g₁sq_B' : (⟨3, by omega⟩ : Omega n k m) ∈ (g₁ n k m)^2 '' B' := by
  rw [← hg₁sq_0]; exact Set.mem_image_of_mem _ h0_in_B'
have h3_in_B' : (⟨3, by omega⟩ : Omega n k m) ∈ B' := by
  rw [hB'_eq_03]; right; rfl
-- Disjointness contradiction
have hDisj : Disjoint B' ((g₁ n k m)^2 '' B') := by
  apply BS.isPartition.1.elim hB'_in_BS hg₁sq_B'_in_BS
  exact fun h => hg₁sq_ne h.symm
exact Set.disjoint_iff.mp hDisj ⟨h3_in_B', h3_in_g₁sq_B'⟩
```

**Note:** The `native_decide` for `hg₁sq_0` may need adjustment. If it fails, use explicit cycle computation or reference `g₁_sq_elem0_eq_elem3` if it exists (may need to add it).

### Pattern for SymmetricCases.lean Sorries (Lines 306, 346, 363)

These should follow the same pattern as Case2.lean sorries 2 and 3, but using the appropriate generator (g₂ or g₃) and different variable names. Check the context at each site for:
- What generator's dichotomy is needed
- What witness point is available
- What inequality is established

---

## Import Requirements

To use the new infrastructure, add to files that need it:

```lean
import AfTests.Primitivity.Lemma11_5_ZpowBlocks
```

**Files needing this import:**
- `Lemma11_5_Case2.lean`
- `Lemma11_5_SymmetricCases.lean`

---

## Verification Checklist

After filling all sorries:

```bash
# 1. Build must pass
lake build AfTests

# 2. No sorries should remain
grep -rn "sorry" AfTests/Primitivity/ --include="*.lean"

# 3. Check LOC limits (should all be ≤ 200)
wc -l AfTests/Primitivity/Lemma11_5_*.lean | sort -n
```

---

## Risk Assessment

### Low Risk (Sorries 2, 3, and SymmetricCases)
- Pattern is straightforward: establish B' ∈ blocks, get disjointness, contradiction
- All pieces are now available
- Estimated: 4-6 lines each

### Medium Risk (Sorry 1 - B' = {0,3} case)
- Needs computational fact g₁²(0) = 3
- May need to add `g₁_sq_elem0_eq_elem3` lemma if native_decide fails
- Estimated: 10-15 lines

### Potential Issues
1. **native_decide failures**: If computational proofs fail, add explicit lemmas
2. **Variable name mismatches**: The fill-in code uses generic names; adjust to match actual context
3. **PairwiseDisjoint.elim argument order**: May need `.symm` on some equalities

---

## Critical Support Intersection Facts (Reference)

```
g₁CoreList = [0, 5, 3, 2]  =>  supp(g₁) = {0, 2, 3, 5} ∪ tailA
g₂CoreList = [1, 3, 4, 0]  =>  supp(g₂) = {0, 1, 3, 4} ∪ tailB
g₃CoreList = [2, 4, 5, 1]  =>  supp(g₃) = {1, 2, 4, 5} ∪ tailC

supp(g₁) ∩ supp(g₂) = {0, 3}  <- g₂ moves ONLY these in supp(g₁)
supp(g₁) ∩ supp(g₃) = {2, 5}
supp(g₂) ∩ supp(g₃) = {1, 4}

g₁ cycle: 0 → 5 → 3 → 2 → (tail) → 0
g₁²(0) = g₁(5) = 3
g₁²(3) = g₁(2) = 6 (first tail element, when n ≥ 1)
```

---

## Known Issues (Lower Priority)

- `Lemma11_5_OrbitInfra.lean` is 315 lines (exceeds 200 LOC limit)
- `Lemma11_5_OrbitContinuation.lean` is 287 lines (exceeds 200 LOC limit)
- Duplicate definition `elem2_in_support_g₁'` in OrbitContinuation and Case2_Helpers

These should be addressed after the sorries are eliminated.
