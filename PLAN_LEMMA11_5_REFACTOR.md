# Plan: Fix Lemma 11.5 Build Failures and Eliminate Sorries

**Date**: 2026-01-22
**Status**: In Progress

## Current State Analysis

### Build Status: **FAILING**
The project doesn't compile due to **6 missing lemmas/methods**:

**BlockSystemOn Methods (undefined):**
- `BlockSystemOn.exists_block_containing_element_in_support`
- `BlockSystemOn.orbit_subset_blocks`

**Helper Lemmas (undefined):**
- `fixed_of_in_supp_g₁_not_2_5` - Elements in supp(g₁) not equal to 2 or 5 are fixed by g₂
- `g₂_map_5_not_in_supp_g₁` - g₂(5) is not in supp(g₁)
- `impossible_block_2_5_in_g₁` - {2,5} cannot be a block of size 2 in the g₁ orbit

These are used in:
- `AfTests/Primitivity/Lemma11_5_Case2.lean` (lines 242, 273, 289, 294, 298, 304)
- `AfTests/Primitivity/Lemma11_5_SymmetricCases.lean` (lines 294, 356, 404, 447)

### Sorries Count: 7
All in `Lemma11_5_SymmetricCases.lean`:
- Lines 324, 339, 351, 399, 408, 413, 442

## Understanding the Proof Structure

The NL proof (Node 1.9.5) uses a **fixed-point argument**:

1. **Case 2 Setup**: g₁(B) ≠ B (so g₁(B) disjoint from B), a₁ ∈ B
2. **Force g₂(B) = g₃(B) = B**: a₁ is fixed by g₂ and g₃ (not in their supports)
3. **Show B ⊆ tailA**: B disjoint from supp(g₂) ∪ supp(g₃) (else Lemma 11.2 contradiction)
4. **Derive contradiction**:
   - n=1: |tailA|=1, but |B|>1
   - n=2: B={a₁,a₂}, g₁(a₁)=a₂, so g₁(B)∩B≠∅
   - n≥3: Need orbit argument (current code path)

The n≥3 case requires:
- B ⊆ supp(g₁) (since B ⊆ tailA ⊆ supp(g₁))
- Orbit of B under g₁ partitions supp(g₁)
- There's a block B' containing element 5
- g₂(B') ≠ B' (since g₂(5) ∉ supp(g₁))
- B' has a fixed point of g₂ (since |B'| > 2 and only {0,3} are moved by g₂ in supp(g₁))
- Therefore g₂(B') ∩ B' ≠ ∅, contradicting block property

## Implementation Plan

### Phase 1: Define All Missing Infrastructure (Priority: Critical)

**New File**: `AfTests/Primitivity/Lemma11_5_OrbitInfra.lean`

This keeps the infrastructure separate from definitions and avoids bloating existing files.

#### 1.1 BlockSystemOn Methods

```lean
-- Orbit membership: σ^j '' B ∈ blocks when B ∈ blocks and σ preserves blocks
theorem BlockSystemOn.orbit_subset_blocks (σ : Perm (Omega n k m))
    (hB : B ∈ BS.blocks) (hInv : ∀ B ∈ BS.blocks, σ '' B ∈ BS.blocks)
    (B' : Set (Omega n k m)) (hB'_orbit : ∃ j : ℕ, B' = (σ ^ j) '' B) :
    B' ∈ BS.blocks := by
  obtain ⟨j, rfl⟩ := hB'_orbit
  exact blockSystemInvariant_pow σ BS.blocks hInv j B hB  -- Uses existing lemma!

-- Element coverage: find block containing x in σ-orbit of B
-- Key insight: σ is a cycle, orbit of B covers supp(σ), partition gives uniqueness
theorem BlockSystemOn.exists_block_containing_element_in_support
    (σ : Perm (Omega n k m)) (B : Set (Omega n k m)) (hB : B ∈ BS.blocks)
    (hB_sub_supp : ∀ x ∈ B, x ∈ σ.support)
    (x : Omega n k m) (hx_supp : x ∈ σ.support) :
    ∃ B' : Set (Omega n k m), (∃ j : ℕ, B' = (σ ^ j) '' B) ∧ x ∈ B'
-- Proof: Use partition property - x must be in some block, show it's in orbit
```

#### 1.2 Fixed Point Helper (CORRECTED)

**Note:** The existing code references `fixed_of_in_supp_g₁_not_2_5` which has WRONG logic.
The correct statement is:

```lean
-- Elements in supp(g₁) that are NOT in supp(g₂) are fixed by g₂
-- supp(g₁) = {0, 2, 3, 5} ∪ tailA
-- supp(g₂) = {0, 1, 3, 4} ∪ tailB
-- supp(g₁) ∩ supp(g₂) = {0, 3} (only these are moved by g₂)
-- supp(g₁) \ supp(g₂) = {2, 5} ∪ tailA (these are fixed by g₂)

theorem g₂_fixes_in_supp_g₁_not_0_3 (x : Omega n k m)
    (hx_supp : x ∈ (g₁ n k m).support)
    (hx_ne_0 : x ≠ ⟨0, by omega⟩)
    (hx_ne_3 : x ≠ ⟨3, by omega⟩) :
    g₂ n k m x = x := by
  -- x ∈ supp(g₁) \ {0,3} = {2, 5} ∪ tailA
  -- {2, 5} ∪ tailA are disjoint from supp(g₂)
  -- Therefore x ∉ supp(g₂), so g₂(x) = x
```

The code in Case2.lean:289 uses the WRONG condition (`x ≠ 2 ∧ x ≠ 5`).
Need to fix this to use the CORRECT condition (`x ≠ 0 ∧ x ≠ 3`), but actually the
overall proof structure needs revision - see "Correct Fixed-Point Argument" section.

#### 1.3 Image Mapping Helper

```lean
-- g₂(5) ∉ supp(g₁)
-- g₂ = (1 3 4 0 b₁ ... bₖ), so g₂(5) = 5 (fixed!) Wait, 5 is NOT in g₂CoreList!
-- Actually g₂CoreList = [1, 3, 4, 0], so 5 ∉ supp(g₂), meaning g₂(5) = 5.
-- But 5 ∈ supp(g₁), so this doesn't help the argument.
--
-- CORRECTION: We need g₂(element in B') to leave supp(g₁).
-- Actually, the argument should use that g₂(0) or g₂(3) leaves supp(g₁).
-- g₂(0) = b₁ (if k≥1) or g₂(0) = 1 (if k=0). Neither in supp(g₁).
-- g₂(3) = 4. 4 ∉ supp(g₁) = {0,2,3,5,tailA}.
-- So g₂(3) = 4 ∉ supp(g₁). This is the useful fact!

theorem g₂_map_3_not_in_supp_g₁ :
    g₂ n k m (⟨3, by omega⟩ : Omega n k m) ∉ (g₁ n k m).support := by
  -- g₂(3) = 4 by cycle definition
  -- 4 ∉ supp(g₁) = {0, 2, 3, 5} ∪ tailA
```

#### 1.4 Block Impossibility (REVISED)

The existing code tries to show `B' ⊆ {2, 5}` as a contradiction path. But this
approach has logic errors (see above). A CLEANER approach:

```lean
-- For n ≥ 3, no size-2 blocks exist in g₁-orbit (cycle length is odd)
-- This makes the fixed-point argument simpler: |B'| ≥ 3 automatically

theorem no_size_2_blocks_for_n_ge_3 (hn : n ≥ 3) (B' : Set (Omega n k m))
    (hB'_in_orbit : ∃ j : ℕ, B' = (g₁ n k m ^ j) '' B)
    (hB_size : B.ncard > 1) : B'.ncard ≥ 3 ∨ B'.ncard = B.ncard := by
  -- Cycle length = 4 + n ≥ 7 (odd)
  -- Block sizes must divide cycle length
  -- 2 does not divide any odd number
  -- So no size-2 blocks exist
```

Then the main fixed-point lemma becomes:

```lean
theorem case2_B'_has_g₂_fixed_point (hn : n ≥ 3) (B' : Set (Omega n k m))
    (hB'_sub : B' ⊆ (g₁ n k m).support)
    (hSize : B'.ncard ≥ 3) :
    ∃ y ∈ B', g₂ n k m y = y := by
  -- B' ⊆ supp(g₁) = {0, 2, 3, 5} ∪ tailA
  -- g₂ moves only {0, 3} in supp(g₁)
  -- |{0,3}| = 2 < 3 ≤ |B'|
  -- So B' must contain element from {2, 5} ∪ tailA
  -- All such elements are fixed by g₂
```

### Phase 2: Verify Lemma11_5_Case2.lean Compiles (Priority: High)

Once Phase 1 is complete, the existing code should compile. Verify with:
```bash
lake build AfTests.Primitivity.Lemma11_5_Case2
```

### Phase 3: Complete Lemma11_5_SymmetricCases.lean (Priority: High)

Fill the 7 sorries using analogous arguments. Need symmetric versions of Phase 1 helpers:

**Additional helpers needed for symmetric cases:**
- `g₁_map_2_not_in_supp_g₂` - g₁(2) ∉ supp(g₂)
- `fixed_of_in_supp_g₂_not_X` - Fixed point lemma for g₂ case
- `impossible_block_X_Y_in_g₂` - Block impossibility for g₂ orbit
- Similar for g₃ case

| Line | Description | Fix |
|------|-------------|-----|
| 324 | y in tailB, show in support | `tailB_in_support_g₂` exists, just apply |
| 339 | g₁(2) not in supp(g₂) | Compute g₁(2) = 0 or a₁, show ∉ supp(g₂) |
| 351 | B' has fixed point of g₁ | Same pattern as Case2.lean:277-290 |
| 399 | |B| ≤ m cardinality | Copy cardinality proof pattern |
| 408 | tailC in support g₃ | `tailC_in_support_g₃` exists |
| 413 | orbit subset supp | Same pattern as Case2.lean:253-263 |
| 442 | B' has fixed point of g₂ | Same fixed-point pattern |

### Phase 4: Verify and Test

1. Build full project: `lake build AfTests`
2. Check no sorries remain: `grep -rn "sorry" AfTests/Primitivity/ --include="*.lean"`
3. Verify Lemma 11.5 statement: `lake build AfTests.Primitivity.Lemma11_5`

## Files to Modify/Create

### New File
1. **`AfTests/Primitivity/Lemma11_5_OrbitInfra.lean`** (~100 lines)
   - BlockSystemOn.orbit_subset_blocks
   - BlockSystemOn.exists_block_containing_element_in_support
   - g₂_fixes_in_supp_g₁_not_0_3
   - g₂_map_3_not_in_supp_g₁
   - case2_B'_has_g₂_fixed_point

### Modify Existing Files
2. **`AfTests/Primitivity/Lemma11_5_Case2.lean`**
   - Add import for new infrastructure file
   - Fix logic bug in fixed-point argument
   - Should compile once infrastructure exists

3. **`AfTests/Primitivity/Lemma11_5_SymmetricCases.lean`**
   - Add import for new infrastructure
   - Add symmetric helpers (g₁_map_2, g₂_map, etc.)
   - Fill 7 sorries

## Critical Support Intersection Facts

**CORRECTED** (based on actual cycle definitions):
```
g₁CoreList = [0, 5, 3, 2]  →  supp(g₁) = {0, 2, 3, 5} ∪ tailA
g₂CoreList = [1, 3, 4, 0]  →  supp(g₂) = {0, 1, 3, 4} ∪ tailB
g₃CoreList = [2, 4, 5, 1]  →  supp(g₃) = {1, 2, 4, 5} ∪ tailC

supp(g₁) ∩ supp(g₂) = {0, 3}  (NOT {2,5}!)
supp(g₁) ∩ supp(g₃) = {2, 5}
supp(g₂) ∩ supp(g₃) = {1, 4}
```

Key consequences:
- **g₂ moves {0, 3}** and **g₂ fixes {2, 5} ∪ tailA** (elements of supp(g₁) \ supp(g₂))
- **g₃ moves {2, 5}** and **g₃ fixes {0, 3} ∪ tailA** (elements of supp(g₁) \ supp(g₃))

**Important Fix Needed in Code:**
The lemma `fixed_of_in_supp_g₁_not_2_5` has wrong name/logic. Correct statement:
```
x ∈ supp(g₁) ∧ x ∉ {0, 3}  ⟹  g₂(x) = x
```
(NOT `x ∉ {2, 5}` which would be wrong!)

**Correct Fixed-Point Argument for B' (n ≥ 3):**
1. |B'| = |B| > 1
2. For n ≥ 3, cycle length = n+4 ≥ 7 (odd), so no size-2 blocks exist
3. Therefore |B'| ≥ 3
4. B' ⊆ supp(g₁) = {0, 2, 3, 5} ∪ tailA
5. g₂ only moves {0, 3} in supp(g₁)
6. With |B'| ≥ 3, B' cannot be ⊆ {0, 3} (size 2), so B' must contain element from {2, 5} ∪ tailA
7. All such elements are fixed by g₂
8. Therefore B' has a g₂-fixed point ✓

## Summary of Issues Found

1. **6 missing lemmas** - Build doesn't compile
2. **7 sorries** - In SymmetricCases.lean
3. **Logic bug** - `fixed_of_in_supp_g₁_not_2_5` uses wrong condition (should be `not_0_3`)
4. **Outdated plan doc** - Previous version referenced non-existent line 796

## Verification Plan

```bash
# After implementation:
lake build AfTests.Primitivity.Lemma11_5  # Must pass
grep -rn "sorry" AfTests/Primitivity/ --include="*.lean"  # Must be empty
lake build AfTests  # Full project must build
```
