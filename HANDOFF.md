# Handoff: 2026-01-22

## Build Status: PASSING
All files compile successfully.

## Sorry Count: 6
All 6 sorries need the **same fix**: prove zpow preserves block membership.

**Lemma11_5_Case2.lean** (3 sorries):
- Line 321: B' = {0,3} case needs block dichotomy for g₂
- Line 363: |B'| > 2 case needs block dichotomy for g₂
- Line 389: y ≠ 3 case needs block dichotomy for g₂

**Lemma11_5_SymmetricCases.lean** (3 sorries):
- Line 306: k >= 2 symmetric case
- Line 346: m >= 2 symmetric case (sub-case)
- Line 363: m >= 2 symmetric case (sub-case)

## Completed This Session

1. **Structured the n≥3 proof** in `Lemma11_5_Case2.lean`:
   - Added orbit membership logic using `IsCycle.exists_zpow_eq`
   - Proved B' = g₁^j '' B ⊆ supp(g₁) via `zpow_apply_mem_support`
   - Split case y = 3 into |B'| = 2 vs |B'| > 2 sub-cases
   - Set up fixed-point and disjointness arguments completely
   - All that remains is establishing B' ∈ BS.blocks

2. **Identified common missing piece**: All 6 sorries reduce to one lemma:
   ```lean
   theorem g₁_zpow_preserves_blocks (BS : BlockSystemOn n k m) (hInv : IsHInvariant BS)
       (B : Set (Omega n k m)) (hB : B ∈ BS.blocks) (j : ℤ) :
       (g₁ n k m ^ j) '' B ∈ BS.blocks
   ```

3. **Wrote detailed implementation plan** in `PLAN_LEMMA11_5_REFACTOR.md`:
   - Helper 1: `block_system_invariant_inv` (σ⁻¹ preserves blocks)
   - Helper 2: `block_system_invariant_zpow` (σ^j preserves blocks for j : ℤ)
   - Helper 3: Specialized versions for g₁, g₂, g₃
   - Usage pattern at each sorry site

## Next Steps (Priority Order)

1. **Add `block_system_invariant_inv` lemma**
   - Location: New file `Lemma11_5_ZpowBlocks.lean` (to avoid LOC limit)
   - Proof: σ permutes blocks ⟹ σ⁻¹ permutes blocks (bijection argument)

2. **Add `block_system_invariant_zpow` lemma**
   - Uses Int.induction_on with cases zero/succ/pred
   - pred case uses `block_system_invariant_inv`

3. **Fill all 6 sorries** using the new infrastructure
   - Pattern at each site is identical (see PLAN for code)

4. **Address LOC violations** (lower priority)
   - OrbitInfra.lean: 315 lines
   - OrbitContinuation.lean: 287 lines

## Known Issues / Gotchas

- **j : ℤ vs j : ℕ**: The `IsCycle.exists_zpow_eq` returns j : ℤ, but existing `orbit_subset_blocks` only handles j : ℕ. This is why we need the zpow lemmas.

- **block_system_invariant_inv** proof sketch:
  - BlockSystemInvariant σ means σ '' B ∈ blocks for all B ∈ blocks
  - Need to show σ⁻¹ '' B ∈ blocks
  - Key: σ '' (σ⁻¹ '' B) = B ∈ blocks, so σ⁻¹ '' B must be a block (partition argument)

- **Duplicate definition**: `elem2_in_support_g₁'` exists in both OrbitContinuation and Case2_Helpers

## Files Modified This Session

- `AfTests/Primitivity/Lemma11_5_Case2.lean` - Major restructuring of n≥3 case (lines 239-389)
- `PLAN_LEMMA11_5_REFACTOR.md` - Detailed implementation notes for zpow lemmas
- `HANDOFF.md` - This file

## Reference: NL Proof Alignment

The Lean approach matches NL proof Node 1.9.5:
1. ✅ Fixed-point argument: a₁ ∈ B forces g₂(B) = g₃(B) = B
2. ✅ B ⊆ tailA (disjoint from supp(g₂) ∪ supp(g₃))
3. ✅ Orbit argument: ∃ j, 0 ∈ g₁^j '' B
4. ⏳ Block dichotomy: need B' ∈ BS.blocks to apply

The mathematical content is complete; only the Lean infrastructure for zpow blocks is missing.
