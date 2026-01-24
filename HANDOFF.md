# Handoff: GNS Uniqueness Step 5 Complete

**Date:** 2026-01-24
**Session Focus:** Implement GNS-U5 (Prove extension is isometry)

---

## Completed This Session

1. **Implemented GNS-U5 (af-tests-ywt): Prove extension is isometry**
   - Added to `Main/UniquenessExtension.lean` (now 144 lines, no sorries)
   - `gnsIntertwinerQuotientFun_isometry` - extract isometry from LinearIsometry
   - `gnsIntertwinerFun_isometry` - extension is isometry via `Isometry.completion_extension`
   - `gnsIntertwinerFun_map_zero` - extension maps 0 to 0
   - `gnsIntertwiner_norm` - norm preservation via `Isometry.norm_map_of_map_zero`
   - `gnsIntertwinerLinearIsometry` - wrapped as `LinearIsometry H_φ →ₗᵢ[ℂ] H`

---

## Current State

- **GNS existence theorem (`gns_theorem`):** Proven
- **GNS uniqueness theorem (`gns_uniqueness`):** In Progress (5/12 steps)
- **Build status:** Passing (zero sorries)
- **Next ready issue:** `af-tests-5nd` (GNS-U6: Prove intertwiner has dense range)

---

## GNS Uniqueness Progress

| Step | ID | Description | Status |
|------|----|-------------|--------|
| 1 | af-tests-aov | Linearity of U₀ | Done |
| 2 | af-tests-6tj | LinearMap structure | Done |
| 3 | af-tests-rb9 | LinearIsometry on quotient | Done |
| 4 | af-tests-hqt | Extension to Hilbert space | Done |
| 5 | af-tests-ywt | Extension is isometry | Done |
| 6 | af-tests-5nd | Dense range | Ready |
| 7 | af-tests-usd | Surjectivity | Blocked by 6 |
| 8 | af-tests-7hr | LinearIsometryEquiv | Blocked by 7 |
| 9 | af-tests-7em | Cyclic vector mapping | Blocked by 8 |
| 10 | af-tests-2dx | Intertwining on quotient | Blocked by 8 |
| 11 | af-tests-5xr | Full intertwining | Blocked by 10 |
| 12 | af-tests-4f9 | Final theorem | Blocked by 9,11 |

---

## Next Steps

Start with `af-tests-5nd` (GNS-U6):
```bash
bd show af-tests-5nd           # View details
bd update af-tests-5nd --status=in_progress  # Claim it
```

Implement in `Main/UniquenessExtension.lean`:
- `gnsIntertwiner_range_contains_orbit` - π(a)ξ is in range of U
- `gnsIntertwiner_denseRange` - U has dense range (using cyclicity)

---

## Key Implementation Details

### Isometry Extension Pattern
Used `Isometry.completion_extension` which extends isometries to completions:
```lean
theorem gnsIntertwinerFun_isometry ... : Isometry (gnsIntertwinerFun ...) :=
  (gnsIntertwinerQuotientFun_isometry ...).completion_extension
```

### Norm Preservation from Isometry
Isometry is defined via `edist`, not norm. To get norm preservation:
```lean
theorem gnsIntertwiner_norm ... (x : φ.gnsHilbertSpace) : ‖U x‖ = ‖x‖ :=
  (gnsIntertwinerFun_isometry ...).norm_map_of_map_zero
    (gnsIntertwinerFun_map_zero ...) x
```

---

## Files Modified This Session

- Modified: `AfTests/GNS/Main/UniquenessExtension.lean` (107 → 144 lines)
- Modified: `docs/GNS/learnings/completion-topology.md` (added isometry norm section)
- Modified: `HANDOFF.md` (this file)

---

## Learning: Isometry Norm Preservation

`Isometry` in Mathlib guarantees `edist (f x) (f y) = edist x y`, not directly `‖f x‖ = ‖x‖`.
To get norm preservation, use `Isometry.norm_map_of_map_zero` which requires proving `f 0 = 0`.
For linear maps this is trivial via `map_zero`.
