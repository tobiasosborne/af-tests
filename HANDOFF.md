# Handoff: GNS Uniqueness Step 2 Complete

**Date:** 2026-01-24
**Session Focus:** Implement GNS-U2 (LinearMap structure)

---

## Completed This Session

1. **Implemented GNS-U2 (af-tests-6tj): LinearMap structure**
   - `gnsIntertwinerQuotientLinearMap` - wraps U₀ as a `LinearMap`
   - `gnsIntertwinerQuotientLinearMap_apply` - simp lemma for unfolding
   - All proofs complete, no sorries
   - File: `Main/Uniqueness.lean` (195 lines, under 200 limit)

---

## Current State

- **GNS existence theorem (`gns_theorem`):** ✅ Proven
- **GNS uniqueness theorem (`gns_uniqueness`):** ⏳ In Progress (2/12 steps)
- **Build status:** Passing (zero sorries)
- **Next ready issue:** `af-tests-rb9` (GNS-U3: LinearIsometry on quotient)

---

## GNS Uniqueness Progress

| Step | ID | Description | Status |
|------|----|-------------|--------|
| 1 | af-tests-aov | Linearity of U₀ | ✅ Done |
| 2 | af-tests-6tj | LinearMap structure | ✅ Done |
| 3 | af-tests-rb9 | LinearIsometry on quotient | Ready |
| 4 | af-tests-hqt | Extension to Hilbert space | Blocked by 3 |
| 5 | af-tests-ywt | Extension is isometry | Blocked by 4 |
| 6 | af-tests-5nd | Dense range | Blocked by 5 |
| 7 | af-tests-usd | Surjectivity | Blocked by 6 |
| 8 | af-tests-7hr | LinearIsometryEquiv | Blocked by 7 |
| 9 | af-tests-7em | Cyclic vector mapping | Blocked by 8 |
| 10 | af-tests-2dx | Intertwining on quotient | Blocked by 8 |
| 11 | af-tests-5xr | Full intertwining | Blocked by 10 |
| 12 | af-tests-4f9 | Final theorem | Blocked by 9,11 |

---

## Next Steps

Start with `af-tests-rb9` (GNS-U3):
```bash
bd show af-tests-rb9           # View details
bd update af-tests-rb9 --status=in_progress  # Claim it
```

Then implement in `Main/Uniqueness.lean`:
- `gnsIntertwinerQuotientLinearIsometry` - combine LinearMap with isometry property
- `gnsIntertwinerQuotientLinearIsometry_continuous` - prove continuity

---

## Files Modified This Session

- Modified: `AfTests/GNS/Main/Uniqueness.lean` (+19 lines: LinearMap definition + simp lemma)
- Modified: `HANDOFF.md` (this file)

---

## Implementation Note

Step 2 was straightforward: the `LinearMap` structure in Lean 4 requires:
- `toFun` - the underlying function
- `map_add'` - additivity
- `map_smul'` - scalar multiplication

We had all three from Step 1. The `map_zero'` property is not required - it's
derivable from `map_smul' 0 x`.
