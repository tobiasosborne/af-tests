# Plan: Eliminate Remaining Sorries in Lemma 11.5

**Date**: 2026-01-22 (Updated)
**Status**: In Progress

## Current State

### Build Status: **PASSING**
All files compile.

### Sorries Count: 6
All 6 sorries need the same fix: **prove zpow preserves block membership**.

**Lemma11_5_Case2.lean** (3 sorries):
- Line 321: B' = {0,3} case needs block dichotomy for g₂
- Line 363: |B'| > 2 case needs block dichotomy for g₂
- Line 389: y ≠ 3 case needs block dichotomy for g₂

**Lemma11_5_SymmetricCases.lean** (3 sorries):
- Line 306: k >= 2 symmetric case
- Line 346: m >= 2 symmetric case (sub-case)
- Line 363: m >= 2 symmetric case (sub-case)

### Infrastructure Implemented

**In `Lemma11_5_OrbitInfra.lean`:**
- `BlockSystemOn.orbit_subset_blocks` - σ^j(B) ∈ blocks when σ preserves blocks (j : ℕ)
- `g₂_fixes_in_supp_g₁_not_0_3` - x ∈ supp(g₁) \ {0,3} → g₂(x) = x
- `g₂_map_3_not_in_supp_g₁` - g₂(3) = 4 ∉ supp(g₁)
- `g₂_map_0_not_in_supp_g₁` - g₂(0) ∉ supp(g₁)
- `set_0_3_not_g₁_closed` - {0, 3} is NOT a valid g₁-block

**In `Lemma11_5_OrbitContinuation.lean`:**
- `g₁_block_system_invariant` - IsHInvariant BS → BlockSystemInvariant g₁ BS.blocks
- `g₁_sq_elem3_eq_elem6` - g₁²(3) = 6 when n >= 1

---

## NEXT STEP: Add zpow_preserves_blocks Lemma

### Goal
Prove that for any j : ℤ, if B ∈ BS.blocks and IsHInvariant BS, then (g₁ ^ j) '' B ∈ BS.blocks.

### Mathematical Foundation

For a finite permutation σ with order L = |supp(σ)|:
1. σ^L = 1 (identity)
2. For any j : ℤ, σ^j = σ^(j mod L) where (j mod L) ∈ {0, 1, ..., L-1} ⊆ ℕ
3. Therefore zpow can always be reduced to npow

### Implementation Approach

**Option A: Direct zpow lemma (Recommended)**
Prove that σ^j for j : ℤ preserves blocks directly by case split:
- If j ≥ 0: σ^j = σ^(j.toNat), use existing npow lemma
- If j < 0: σ^j = (σ⁻¹)^(-j).toNat, prove σ⁻¹ preserves blocks

**Option B: Via order reduction**
Convert zpow to npow using finite group order, then use existing lemma.

### Detailed Implementation Plan

#### Helper Lemma 1: Inverse preserves blocks
```lean
-- Location: Lemma11_5_OrbitInfra.lean (add after line 53)
theorem block_system_invariant_inv {σ : Perm α} {blocks : Set (Set α)}
    (hInv : BlockSystemInvariant σ blocks) :
    BlockSystemInvariant σ⁻¹ blocks := by
  intro B hB
  -- σ '' (σ⁻¹ '' B) = B, so σ⁻¹ '' B must be a block
  -- Key: σ is a bijection on blocks, so σ⁻¹ also permutes blocks
  have hσB_in : σ '' (σ⁻¹ '' B) ∈ blocks := by
    rw [Set.image_image, Equiv.self_comp_symm, Set.image_id]
    exact hB
  -- Need: blocks are disjoint, σ '' X ∈ blocks for all X ∈ blocks
  -- So σ⁻¹ '' B must equal some block C, hence C ∈ blocks
  sorry -- Fill in with partition argument
```

**Proof sketch for Helper 1:**
- BlockSystemInvariant σ means σ permutes the blocks (σ '' B ∈ blocks for B ∈ blocks)
- Since blocks form a partition, σ induces a bijection on the finite set of blocks
- Therefore σ⁻¹ also induces a bijection, meaning σ⁻¹ '' B ∈ blocks

#### Helper Lemma 2: zpow preserves blocks (main lemma)
```lean
-- Location: Lemma11_5_OrbitInfra.lean (add after Helper 1)
theorem block_system_invariant_zpow {σ : Perm α} {blocks : Set (Set α)}
    (hInv : BlockSystemInvariant σ blocks) (j : ℤ) :
    BlockSystemInvariant (σ ^ j) blocks := by
  induction j using Int.induction_on with
  | zero =>
    simp only [zpow_zero]
    intro B hB
    simp only [Equiv.Perm.coe_one, Set.image_id]
    exact hB
  | succ k ih =>
    intro B hB
    rw [zpow_add, zpow_one, Equiv.Perm.coe_mul, Set.image_comp]
    exact hInv _ (ih B hB)
  | pred k ih =>
    intro B hB
    rw [Int.sub_eq_add_neg, zpow_add, zpow_neg_one, Equiv.Perm.coe_mul, Set.image_comp]
    exact block_system_invariant_inv hInv _ (ih B hB)
```

#### Helper Lemma 3: Specialized for g₁
```lean
-- Location: Lemma11_5_OrbitInfra.lean (add after Helper 2)
theorem g₁_zpow_preserves_blocks (BS : BlockSystemOn n k m) (hInv : IsHInvariant BS)
    (B : Set (Omega n k m)) (hB : B ∈ BS.blocks) (j : ℤ) :
    (g₁ n k m ^ j) '' B ∈ BS.blocks := by
  have hBSInv := g₁_block_system_invariant BS hInv
  exact block_system_invariant_zpow hBSInv j B hB
```

#### Similar lemmas for g₂ and g₃
```lean
theorem g₂_zpow_preserves_blocks (BS : BlockSystemOn n k m) (hInv : IsHInvariant BS)
    (B : Set (Omega n k m)) (hB : B ∈ BS.blocks) (j : ℤ) :
    (g₂ n k m ^ j) '' B ∈ BS.blocks := by
  have hBSInv : BlockSystemInvariant (g₂ n k m) BS.blocks := fun b hb => hInv.2.1 b hb
  exact block_system_invariant_zpow hBSInv j B hB

theorem g₃_zpow_preserves_blocks (BS : BlockSystemOn n k m) (hInv : IsHInvariant BS)
    (B : Set (Omega n k m)) (hB : B ∈ BS.blocks) (j : ℤ) :
    (g₃ n k m ^ j) '' B ∈ BS.blocks := by
  have hBSInv : BlockSystemInvariant (g₃ n k m) BS.blocks := fun b hb => hInv.2.2 b hb
  exact block_system_invariant_zpow hBSInv j B hB
```

### File Changes Required

#### 1. Lemma11_5_OrbitInfra.lean
Add after line 53 (after `orbit_subset_blocks`):
- `block_system_invariant_inv` (~15 lines)
- `block_system_invariant_zpow` (~15 lines)
- `g₁_zpow_preserves_blocks` (~5 lines)
- `g₂_zpow_preserves_blocks` (~5 lines)
- `g₃_zpow_preserves_blocks` (~5 lines)

**Total addition: ~45 lines**
**Warning: File is already 315 lines (exceeds 200 LOC limit)**
**Recommendation: Extract to new file `Lemma11_5_ZpowBlocks.lean`**

#### 2. Lemma11_5_Case2.lean
At each sorry (lines 321, 363, 389), add:
```lean
-- Establish B' ∈ BS.blocks
have hB'_in_BS : B' ∈ BS.blocks := g₁_zpow_preserves_blocks BS hInv B hB_in_BS j
-- Use block dichotomy
have hDichotomy := BS.block_dichotomy hB'_in_BS (hInv.2.1 B' hB'_in_BS)
-- Either g₂(B') = B' or disjoint
rcases hDichotomy with hEq | hDisj
· -- g₂(B') = B' contradicts hg₂_B'_ne
  exact hg₂_B'_ne hEq
· -- g₂(B') disjoint from B' contradicts y ∈ B' ∩ g₂(B')
  exact Set.disjoint_iff.mp hDisj ⟨hy_in_B', hy_in_g₂B'⟩
```

#### 3. Lemma11_5_SymmetricCases.lean
Similar pattern at lines 306, 346, 363, using appropriate generator (g₂ or g₃).

### Verification Checklist

After implementation:
```bash
lake build AfTests                                    # Must pass
grep -rn "sorry" AfTests/Primitivity/ --include="*.lean"  # Should show 0
wc -l AfTests/Primitivity/Lemma11_5_*.lean | sort -n  # Check LOC limits
```

### Dependencies

The `block_system_invariant_inv` proof requires:
1. Blocks form a partition (available via `BS.isPartition`)
2. σ induces a bijection on blocks (follows from BlockSystemInvariant)

May need to import:
- `Mathlib.Data.Set.Card` for finite block counting
- Or use the fact that `blocks` is a Finset/finite

### Risk Assessment

**Low Risk:**
- Mathematical argument is straightforward (inverse of permutation permutes blocks)
- Pattern matches existing `orbit_subset_blocks` lemma

**Medium Risk:**
- `block_system_invariant_inv` proof may require careful handling of partition properties
- May need additional lemmas about finite partitions

**Mitigation:**
- If `block_system_invariant_inv` is hard, can use alternative: convert zpow to npow via order
- For finite σ, ∃ L : ℕ, σ^(-1) = σ^(L-1), reducing to npow case

---

## Critical Support Intersection Facts (Reference)

```
g₁CoreList = [0, 5, 3, 2]  =>  supp(g₁) = {0, 2, 3, 5} ∪ tailA
g₂CoreList = [1, 3, 4, 0]  =>  supp(g₂) = {0, 1, 3, 4} ∪ tailB
g₃CoreList = [2, 4, 5, 1]  =>  supp(g₃) = {1, 2, 4, 5} ∪ tailC

supp(g₁) ∩ supp(g₂) = {0, 3}  <- g₂ moves ONLY these in supp(g₁)
supp(g₁) ∩ supp(g₃) = {2, 5}
supp(g₂) ∩ supp(g₃) = {1, 4}
```

## Known Issues

- `Lemma11_5_OrbitInfra.lean` is 315 lines (exceeds 200 LOC limit)
- `Lemma11_5_OrbitContinuation.lean` is 287 lines (exceeds 200 LOC limit)
- Duplicate definition `elem2_in_support_g₁'` in OrbitContinuation and Case2_Helpers
- **Recommendation**: Create `Lemma11_5_ZpowBlocks.lean` for new zpow lemmas
