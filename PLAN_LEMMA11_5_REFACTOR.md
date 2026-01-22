# Plan: Eliminate Remaining Sorries in Lemma 11.5

**Date**: 2026-01-22 (Updated)
**Status**: In Progress

## Current State

### Build Status: **PASSING**
All files compile. Legacy stubs have been removed.

### Sorries Count: 4
- `Lemma11_5_Case2.lean:248` - n ≥ 3 case
- `Lemma11_5_SymmetricCases.lean:306, 346, 363` - k ≥ 2 and m ≥ 2 cases

### Infrastructure Already Implemented
In `Lemma11_5_OrbitInfra.lean`:
- `BlockSystemOn.orbit_subset_blocks` - σ^j(B) ∈ blocks when σ preserves blocks
- `g₂_fixes_in_supp_g₁_not_0_3` - CORRECT fixed-point lemma
- `g₂_map_3_not_in_supp_g₁` - g₂(3) = 4 ∉ supp(g₁)
- `g₂_map_0_not_in_supp_g₁` - g₂(0) ∉ supp(g₁)

## Critical Support Intersection Facts

```
g₁CoreList = [0, 5, 3, 2]  →  supp(g₁) = {0, 2, 3, 5} ∪ tailA
g₂CoreList = [1, 3, 4, 0]  →  supp(g₂) = {0, 1, 3, 4} ∪ tailB
g₃CoreList = [2, 4, 5, 1]  →  supp(g₃) = {1, 2, 4, 5} ∪ tailC

supp(g₁) ∩ supp(g₂) = {0, 3}  ← g₂ moves ONLY these in supp(g₁)
supp(g₁) ∩ supp(g₃) = {2, 5}
supp(g₂) ∩ supp(g₃) = {1, 4}
```

## Correct Proof Strategy for n ≥ 3 Case

### Key Insight: {0, 3} Cannot Be a Block

The critical observation is that **{0, 3} is NOT a valid block for g₁**:

```
g₁(0) = 5, g₁(5) = 3  →  g₁²(0) = 3
g₁(3) = 2, g₁(2) = a₁  →  g₁²(3) = 6

Therefore: g₁²({0, 3}) = {3, 6}
```

This set:
- Intersects {0, 3} at element 3
- Is NOT equal to {0, 3} (since 6 ≠ 0)

This violates the block property (g^j(B) must be equal to B or disjoint from B).

### Consequence

Any block B' containing 0 must ALSO contain some element y where:
- y ≠ 0 (since |B'| > 1)
- y ≠ 3 (since {0, 3} is not a valid block)

Therefore y ∈ supp(g₁) \ {0, 3} = {2, 5} ∪ tailA, so g₂(y) = y.

### The Contradiction Argument

1. **Find B' containing 0**: The g₁-orbit of B partitions supp(g₁). Since 0 ∈ supp(g₁), some B' = g₁^j(B) contains 0.

2. **B' has a g₂-fixed element**: B' contains 0 and some y ∉ {0, 3}. That y is fixed by g₂.

3. **g₂(B') ≠ B'**: Since 0 ∈ B' but g₂(0) ∉ supp(g₁) ⊇ B', we have g₂(B') ≠ B'.

4. **Block dichotomy**: g₂(B') ∩ B' = ∅ (since g₂(B') ≠ B').

5. **Contradiction**: y ∈ B' and g₂(y) = y ∈ g₂(B'), so y ∈ B' ∩ g₂(B') ≠ ∅.

### Note on Block Sizes

The old plan incorrectly claimed "|B'| ≥ 3 for n ≥ 3". This is WRONG:
- n ≥ 3 does NOT imply n is odd
- For even n, n+4 is even, so size-2 blocks can exist
- Example: n = 6, then size-2 block {a₁, a₆} ⊆ tailA is possible

However, this doesn't matter because **the argument works for any |B'| ≥ 2** as long as B' ≠ {0, 3}, which is always true since {0, 3} is not a valid block.

## Implementation Steps

### Step 1: Prove {0, 3} is not a g₁-block (Infrastructure)

Add to `Lemma11_5_OrbitInfra.lean`:

```lean
/-- {0, 3} is not closed under g₁² action, hence not a valid block -/
theorem set_0_3_not_g₁_closed (hn : n ≥ 1) :
    ∃ x ∈ ({⟨0, _⟩, ⟨3, _⟩} : Set (Omega n k m)),
      (g₁ n k m ^ 2) x ∉ ({⟨0, _⟩, ⟨3, _⟩} : Set (Omega n k m)) := by
  use ⟨3, _⟩
  constructor
  · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  · -- g₁²(3) = 6 ∉ {0, 3}
    rw [g₁_sq_of_3 hn]  -- Need this lemma
    simp [Fin.ext_iff]
```

### Step 2: Prove block containing 0 has g₂-fixed element

```lean
/-- Any block B' containing 0 also contains an element fixed by g₂ -/
theorem block_containing_0_has_g₂_fixed (hn : n ≥ 1)
    (B' : Set (Omega n k m)) (hB'_block : B' ∈ BS.blocks)
    (hB'_sub : B' ⊆ (g₁ n k m).support)
    (h0_in : (⟨0, _⟩ : Omega n k m) ∈ B')
    (hSize : B'.ncard > 1) :
    ∃ y ∈ B', y ≠ ⟨0, _⟩ ∧ y ≠ ⟨3, _⟩ := by
  -- B' has another element besides 0
  -- That element can't be 3 (since {0,3} is not a block)
  -- So it's in {2, 5} ∪ tailA
  sorry
```

### Step 3: Complete the n ≥ 3 proof in Case2.lean

Use the infrastructure to derive the contradiction.

### Step 4: Apply symmetric arguments for k ≥ 2 and m ≥ 2

The same pattern applies with different generators:
- k ≥ 2: Use g₂ orbit, find block with element from supp(g₂) ∩ supp(g₁)
- m ≥ 2: Use g₃ orbit, find block with element from supp(g₃) ∩ supp(g₁)

## Files to Modify

1. **`Lemma11_5_OrbitInfra.lean`**: Add {0,3} non-block lemma
2. **`Lemma11_5_Case2.lean`**: Complete n ≥ 3 proof using infrastructure
3. **`Lemma11_5_SymmetricCases.lean`**: Apply symmetric arguments

## Verification

```bash
lake build AfTests  # Must pass
grep -rn "sorry" AfTests/Primitivity/ --include="*.lean"  # Must be empty
```
