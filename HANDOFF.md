# Handoff: 2026-01-19 (Session 17)

## Completed This Session

### Lemma11_4.lean - Block Orbit (Filled 2 of 3 sorries)

1. **Filled `blockOrbitSize_eq_setPeriod`** (was line 127)
   - Added import `Mathlib.Data.ZMod.QuotientGroup` for `MulAction.minimalPeriod_eq_card`
   - Added helper lemmas:
     - `blockOrbit_eq_MulAction_orbit`: Shows blockOrbit = MulAction.orbit over zpowers
     - `orbit_ncard_eq_period`: Uses `MulAction.minimalPeriod_eq_card` to get ncard = period
   - Key insight: orbit ncard = Fintype.card = minimalPeriod = period

2. **Filled `orbit_blocks_partition_support`** (was line 165)
   - Uses `IsCycle.sameCycle` to get transitivity: for any x ∈ support, exists k with σ^k(y) = x
   - Then x ∈ (σ^k '' B) ∩ support, showing support ⊆ union
   - Reverse inclusion is trivial

3. **Documented `block_support_intersection_card`** (line 250, still sorry)
   - Added helper lemma `orbit_blocks_same_card`: all orbit blocks have equal intersection size with support
   - Added `sigma_preserves_intersection_card`: σ preserves |B ∩ support| via bijection
   - Proof outline documented in file - requires cardinality arithmetic over finite sums

## Current State

- **Build status**: PASSING (with 1 sorry in Lemma11_4.lean)
- **Sorry count in Lemma11_4**: 1 (down from 3)
- **LOC violation**: Lemma11_4.lean is 271 lines (P0 issue created: af-tests-bqj)

## Remaining Sorry in Lemma11_4.lean

| Line | Lemma | Strategy |
|------|-------|----------|
| 250 | `block_support_intersection_card` | Has `orbit_blocks_same_card` helper. Needs: (1) orbit blocks pairwise disjoint, (2) use `Set.Finite.ncard_biUnion` for sum, (3) arithmetic: cycleLength = blockOrbitSize × |B ∩ support| |

## Key Lemmas Added

```lean
-- New helpers in Lemma11_4.lean
blockOrbit_eq_MulAction_orbit : blockOrbit σ B = MulAction.orbit (zpowers σ) B
orbit_ncard_eq_period : (orbit zpowers B).ncard = MulAction.period σ B
sigma_preserves_intersection_card : (σ '' B ∩ support).ncard = (B ∩ support).ncard
orbit_blocks_same_card : ((σ^k '' B) ∩ support).ncard = (B ∩ support).ncard
```

## Next Steps (Priority Order)

1. **Refactor Lemma11_4.lean** (af-tests-bqj, P0)
   - Extract helper lemmas to `Lemma11_4_Helpers.lean`
   - Target: main file under 200 LOC

2. **Complete `block_support_intersection_card`** (af-tests-2hl)
   - Need to show orbit blocks are pairwise disjoint (inherit from block system)
   - Use `Set.Finite.ncard_biUnion` for cardinality sum
   - Conclude with division arithmetic

## Files Modified This Session

- `AfTests/Primitivity/Lemma11_4.lean` - Filled 2 sorries, added Period-based proofs

## Known Issues / Gotchas

- **LOC exceeded**: 271 lines (limit 200) - helper lemmas should be extracted
- **Fintype instance**: Need `Set.fintype` for `MulAction.minimalPeriod_eq_card`
- **Cardinality arithmetic**: `finsum` machinery needed for partition argument

## Issue Status

- **af-tests-2hl** (Lemma11_4): IN_PROGRESS - 1 sorry remaining (was 3)
- **af-tests-bqj** (Refactor): OPEN - Lemma11_4.lean exceeds 200 LOC
