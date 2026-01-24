# Handoff: GNS Uniqueness Step 3 Complete

**Date:** 2026-01-24
**Session Focus:** Implement GNS-U3 (LinearIsometry on quotient)

---

## Completed This Session

1. **Implemented GNS-U3 (af-tests-rb9): LinearIsometry on quotient**
   - `gnsIntertwinerQuotientLinearIsometry` - wraps LinearMap + isometry as LinearIsometry
   - Compacted header docstring to stay under 200 LOC
   - File: `Main/Uniqueness.lean` (189 lines)

---

## Current State

- **GNS existence theorem (`gns_theorem`):** ✅ Proven
- **GNS uniqueness theorem (`gns_uniqueness`):** ⏳ In Progress (3/12 steps)
- **Build status:** Passing (zero sorries)
- **Next ready issue:** `af-tests-hqt` (GNS-U4: Extension to Hilbert space)

---

## GNS Uniqueness Progress

| Step | ID | Description | Status |
|------|----|-------------|--------|
| 1 | af-tests-aov | Linearity of U₀ | ✅ Done |
| 2 | af-tests-6tj | LinearMap structure | ✅ Done |
| 3 | af-tests-rb9 | LinearIsometry on quotient | ✅ Done |
| 4 | af-tests-hqt | Extension to Hilbert space | Ready |
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

Start with `af-tests-hqt` (GNS-U4):
```bash
bd show af-tests-hqt           # View details
bd update af-tests-hqt --status=in_progress  # Claim it
```

Implement in new file `Main/UniquenessExtension.lean`:
- `gnsIntertwiner` - extend U₀ to full Hilbert space via completion
- Key mathlib: `Isometry.completion_extension`

---

## Files Modified This Session

- Modified: `AfTests/GNS/Main/Uniqueness.lean` (compacted header, added LinearIsometry)
- Modified: `HANDOFF.md` (this file)

---

## Learning: Topology Diamond

The `gnsIntertwinerQuotientLinearIsometry_continuous` theorem was dropped due to
topology instance mismatch:
- Quotient has `QuotientModule.Quotient.topologicalSpace`
- LinearIsometry gives `PseudoMetricSpace.toUniformSpace.toTopologicalSpace`

These should be equal for seminormed quotients, but Lean doesn't unify them
automatically. Not blocking for the construction - continuity follows from
the LinearIsometry structure when needed.
