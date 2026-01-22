# Plan: Eliminate Remaining Sorries in Lemma 11.5

**Date**: 2026-01-22 (Updated)
**Status**: In Progress

## Current State

### Build Status: **PASSING**
All files compile.

### Sorries Count: 4
- `Lemma11_5_Case2.lean:248` - n >= 3 case
- `Lemma11_5_SymmetricCases.lean:306, 346, 363` - k >= 2 and m >= 2 cases

### Infrastructure Implemented
In `Lemma11_5_OrbitInfra.lean`:
- `BlockSystemOn.orbit_subset_blocks` - sigma^j(B) in blocks when sigma preserves blocks
- `g2_fixes_in_supp_g1_not_0_3` - CORRECT fixed-point lemma
- `g2_map_3_not_in_supp_g1` - g2(3) = 4 not in supp(g1)
- `g2_map_0_not_in_supp_g1` - g2(0) not in supp(g1)
- **NEW**: `set_0_3_not_g1_closed` - {0, 3} is NOT a valid g1-block (Step 1 DONE)

In `Lemma11_5_OrbitContinuation.lean`:
- **NEW**: `g1_sq_elem3_eq_elem6` - g1^2(3) = 6 when n >= 1

## Implementation Steps

### Step 1: DONE - Prove {0, 3} is not a g1-block

Added `set_0_3_not_g1_closed` to `Lemma11_5_OrbitInfra.lean:304-315`.

### Step 2: NEXT - Find orbit block containing 0, derive contradiction

**Location**: `Lemma11_5_Case2.lean:248`

**What to prove**: In the n >= 3 case, derive False from:
- `B subseteq tailA` (already established at that point)
- `g1(B) disjoint B` (Case 2 assumption)
- `|B| > 1` (non-trivial block)

**Proof sketch**:
1. The g1-orbit of B partitions supp(g1) = {0, 2, 3, 5} union tailA
2. Since B subseteq tailA, some other block B' = g1^j(B) contains element 0
3. B' cannot equal {0, 3} (by `set_0_3_not_g1_closed`)
4. So B' contains some y in {2, 5} union tailA, which is g2-fixed
5. g2(B') != B' (since g2(0) not in supp(g1) supseteq B')
6. By block dichotomy: g2(B') disjoint B'
7. But y in B' and g2(y) = y in g2(B') => y in B' cap g2(B') != empty
8. Contradiction!

**Key lemmas needed** (may need to add):
- Orbit partition lemma: exists j, 0 in g1^j '' B
- Block size preservation: |g1^j(B)| = |B| > 1

### Step 3: Apply symmetric arguments for k >= 2 and m >= 2

After n >= 3 is done, apply same pattern:
- k >= 2: Use g2 orbit, element 1, and {1, 4} non-block argument
- m >= 2: Use g3 orbit, element 2, and {2, 5} non-block argument

## Critical Support Intersection Facts

```
g1CoreList = [0, 5, 3, 2]  =>  supp(g1) = {0, 2, 3, 5} union tailA
g2CoreList = [1, 3, 4, 0]  =>  supp(g2) = {0, 1, 3, 4} union tailB
g3CoreList = [2, 4, 5, 1]  =>  supp(g3) = {1, 2, 4, 5} union tailC

supp(g1) cap supp(g2) = {0, 3}  <- g2 moves ONLY these in supp(g1)
supp(g1) cap supp(g3) = {2, 5}
supp(g2) cap supp(g3) = {1, 4}
```

## The Contradiction Argument (for reference)

1. **Find B' containing 0**: The g1-orbit of B partitions supp(g1). Since 0 in supp(g1), some B' = g1^j(B) contains 0.

2. **B' has a g2-fixed element**: B' contains 0 and some y not in {0, 3}. That y is fixed by g2.

3. **g2(B') != B'**: Since 0 in B' but g2(0) not in supp(g1) supseteq B', we have g2(B') != B'.

4. **Block dichotomy**: g2(B') cap B' = empty (since g2(B') != B').

5. **Contradiction**: y in B' and g2(y) = y in g2(B'), so y in B' cap g2(B') != empty.

## Files to Modify

1. **`Lemma11_5_Case2.lean`**: Complete n >= 3 proof (line 248)
2. **`Lemma11_5_SymmetricCases.lean`**: Apply symmetric arguments (lines 306, 346, 363)

## Known Issues

- `Lemma11_5_OrbitInfra.lean` is 315 lines (exceeds 200 LOC limit)
- `Lemma11_5_OrbitContinuation.lean` is 287 lines (exceeds 200 LOC limit)
- Duplicate definition `elem2_in_support_g1'` in OrbitContinuation and Case2_Helpers

## Verification

```bash
lake build AfTests  # Must pass
grep -rn "sorry" AfTests/Primitivity/ --include="*.lean"  # Must show only 4
```
