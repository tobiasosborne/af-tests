# Handoff: 2026-01-22

## Build Status: PASSING
All files compile successfully.

## Sorry Count: 6
All 6 sorries are ready to be filled - infrastructure is complete.

**Lemma11_5_Case2.lean** (3 sorries):
- Line 321: B' = {0,3} case needs g₁ block dichotomy
- Line 363: |B'| > 2 case needs g₂ block dichotomy
- Line 389: y ≠ 3 case needs g₂ block dichotomy

**Lemma11_5_SymmetricCases.lean** (3 sorries):
- Line 306: k >= 2 symmetric case
- Line 346: m >= 2 symmetric case (sub-case)
- Line 363: m >= 2 symmetric case (sub-case)

## Completed This Session

1. **Created `Lemma11_5_ZpowBlocks.lean`** (57 lines, builds successfully)
   - `g₁_zpow_preserves_blocks`: (g₁ ^ j) '' B ∈ BS.blocks
   - `g₂_zpow_preserves_blocks`: (g₂ ^ j) '' B ∈ BS.blocks
   - `g₃_zpow_preserves_blocks`: (g₃ ^ j) '' B ∈ BS.blocks

2. **Key Discovery**: Infrastructure already existed in `Lemma11_4_Helpers.lean`
   - `inv_image_mem_blocks` - σ⁻¹ preserves blocks
   - `zpow_image_mem_blocks` - σ^j preserves blocks for j : ℤ
   - New file wraps these with H-invariance context

3. **Updated PLAN_LEMMA11_5_REFACTOR.md** with detailed fill-in code for each sorry

## Next Steps (Priority Order)

### 1. Fill Sorries 2 and 3 (Lines 363, 389) - EASIEST

Add import to `Lemma11_5_Case2.lean`:
```lean
import AfTests.Primitivity.Lemma11_5_ZpowBlocks
```

Then replace each sorry with (adjust variable names as needed):
```lean
have hB'_in_BS : B' ∈ BS.blocks := g₁_zpow_preserves_blocks BS hInv B hB_in_BS j
have hg₂B'_in_BS : g₂ n k m '' B' ∈ BS.blocks := hInv.2.1 B' hB'_in_BS
have hDisj : Disjoint B' (g₂ n k m '' B') := by
  apply BS.isPartition.1.elim hB'_in_BS hg₂B'_in_BS
  exact fun h => hg₂_B'_ne h.symm
exact Set.disjoint_iff.mp hDisj ⟨hy_in_B', hy_in_g₂B'⟩
```

### 2. Fill Sorry 1 (Line 321) - Uses g₁ dichotomy, needs g₁²(0)=3

See PLAN_LEMMA11_5_REFACTOR.md for detailed 15-line fill-in code.

### 3. Fill SymmetricCases sorries (Lines 306, 346, 363)

Same pattern as Case2.lean sorries 2/3, using appropriate generator.

### 4. Address LOC violations (lower priority)
- OrbitInfra.lean: 315 lines
- OrbitContinuation.lean: 287 lines

## Known Issues / Gotchas

- **Import required**: Files using `g₁_zpow_preserves_blocks` must import `Lemma11_5_ZpowBlocks`

- **Variable names**: The fill-in code in the plan uses generic names. Check actual context:
  - Sorry at 363 uses `hz_in_B'`, `hz_in_g₂B'`
  - Sorry at 389 uses `hy_in_B'`, `hy_in_g₂B'`

- **PairwiseDisjoint.elim**: Takes (hB1 : B1 ∈ blocks) (hB2 : B2 ∈ blocks) (hne : B1 ≠ B2)
  - We have `hg₂_B'_ne : g₂ '' B' ≠ B'`, need `B' ≠ g₂ '' B'`
  - Use `fun h => hg₂_B'_ne h.symm`

- **native_decide for g₁²(0)=3**: May fail for symbolic n,k,m. If so, add explicit lemma.

## Files Modified This Session

- `AfTests/Primitivity/Lemma11_5_ZpowBlocks.lean` - **NEW** (57 lines)
- `PLAN_LEMMA11_5_REFACTOR.md` - Updated with detailed fill-in instructions
- `HANDOFF.md` - This file

## Reference: NL Proof Alignment

The Lean approach matches NL proof Node 1.9.5:
1. ✅ Fixed-point argument: a₁ ∈ B forces g₂(B) = g₃(B) = B
2. ✅ B ⊆ tailA (disjoint from supp(g₂) ∪ supp(g₃))
3. ✅ Orbit argument: ∃ j, 0 ∈ g₁^j '' B
4. ✅ Block dichotomy infrastructure: `g₁_zpow_preserves_blocks` now available

## Verification Commands

```bash
# Build
lake build AfTests

# Check sorries
grep -rn "sorry" AfTests/Primitivity/ --include="*.lean"

# Check LOC
wc -l AfTests/Primitivity/Lemma11_5_*.lean | sort -n
```
