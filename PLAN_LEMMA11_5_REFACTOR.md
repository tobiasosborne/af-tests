# Plan: Eliminate Remaining Sorries in Lemma 11.5

**Date**: 2026-01-22 (Updated)
**Status**: 1 of 6 sorries FILLED - 5 remaining

---

## Executive Summary

Infrastructure is complete. One sorry filled this session. The remaining 5 sorries follow the same proven pattern.

---

## Current State

### Build Status: **PASSING**

### Sorries Count: 5 (was 6)

**Lemma11_5_Case2.lean** (2 sorries, was 3):
- Line 322: B' = {0,3} case - needs g₁ block dichotomy (HARDER)
- Line 393: y ≠ 3 case - needs g₂ block dichotomy (EASY - same pattern as filled sorry)
- ~~Line 363: |B'| > 2 case~~ **DONE**

**Lemma11_5_SymmetricCases.lean** (3 sorries):
- Line 306: k >= 2 symmetric case
- Line 346: m >= 2 symmetric case (sub-case)
- Line 363: m >= 2 symmetric case (sub-case)

---

## NEXT STEP: Fill Line 393 in Lemma11_5_Case2.lean

This is the **easiest** remaining sorry - identical pattern to the one just filled.

### Context at line 393:
```lean
y : Omega n k m
hy_in_B' : y ∈ B'
hy_ne_0 : y ≠ ⟨0, _⟩
hy_eq_3 : y ≠ ⟨3, _⟩   -- NOTE: this is the negation, y ≠ 3
hy_in_supp : y ∈ (g₁ n k m).support
hg₂_fixes_y : g₂ n k m y = y
hy_in_g₂B' : y ∈ g₂ n k m '' B'
hg₂_B'_ne : g₂ n k m '' B' ≠ B'
```

### Exact fill-in code (PROVEN PATTERN):
```lean
have hB'_in_BS : B' ∈ BS.blocks := g₁_zpow_preserves_blocks BS hInv B hB_in_BS j
have hg₂B'_in_BS : g₂ n k m '' B' ∈ BS.blocks := hInv.2.1 B' hB'_in_BS
have hDisj : Disjoint B' (g₂ n k m '' B') :=
  BS.isPartition.1 hB'_in_BS hg₂B'_in_BS hg₂_B'_ne.symm
exact Set.disjoint_iff.mp hDisj ⟨hy_in_B', hy_in_g₂B'⟩
```

**Key insight from this session**: Use `BS.isPartition.1` directly (not `.elim`). It's a `PairwiseDisjoint` which unfolds to `∀ x ∈ s, ∀ y ∈ s, x ≠ y → Disjoint x y`.

---

## Remaining Sorries (After Line 393)

### Priority 2: SymmetricCases.lean (3 sorries)

Same pattern as Case2.lean. Need to:
1. Add import: `import AfTests.Primitivity.Lemma11_5_ZpowBlocks`
2. Use appropriate generator (`g₂_zpow_preserves_blocks` or `g₃_zpow_preserves_blocks`)
3. Apply the disjointness pattern

### Priority 3: Line 322 in Case2.lean (B' = {0,3} case)

This is HARDER - uses g₁ dichotomy instead of g₂. Mathematical argument:
1. B' = {0, 3} ∈ BS.blocks
2. g₁²(B') ∈ BS.blocks
3. g₁²(B') ≠ B' (from `set_0_3_not_g₁_closed`: some element leaves)
4. g₁²(0) = 3 ∈ B' (computational fact)
5. So 3 ∈ g₁²(B') ∩ B', contradicting disjointness

May need `native_decide` or explicit lemma for g₁²(0) = 3.

---

## Infrastructure Status: COMPLETE

### Available lemmas:

**In `Lemma11_5_ZpowBlocks.lean`:**
- `g₁_zpow_preserves_blocks` - g₁^j '' B ∈ BS.blocks
- `g₂_zpow_preserves_blocks` - g₂^j '' B ∈ BS.blocks
- `g₃_zpow_preserves_blocks` - g₃^j '' B ∈ BS.blocks

**In `Lemma11_5_OrbitInfra.lean`:**
- `set_0_3_not_g₁_closed` - ∃ x ∈ {0,3}, g₁²(x) ∉ {0,3}
- `g₂_fixes_in_supp_g₁_not_0_3` - x ∈ supp(g₁) \ {0,3} → g₂(x) = x

---

## Session Log

### 2026-01-22 Session:
- **FILLED**: Line 363 sorry (|B'| > 2 case)
- **FIXED**: Duplicate `elem2_in_support_g₁'` conflict by adding OrbitContinuation import to Case2_Helpers
- **DISCOVERED**: Correct pattern is `BS.isPartition.1 hB1 hB2 hne` (direct application, not `.elim`)

---

## Verification Commands

```bash
# Build
lake build AfTests

# Check sorries
grep -rn "sorry" AfTests/Primitivity/ --include="*.lean"

# Check LOC
wc -l AfTests/Primitivity/Lemma11_5_*.lean | sort -n
```

---

## Known Issues (Lower Priority)

- `Lemma11_5_OrbitInfra.lean` is 315 lines (exceeds 200 LOC limit)
- `Lemma11_5_OrbitContinuation.lean` is 287 lines (exceeds 200 LOC limit)

Address after sorries are eliminated.
