# Handoff: GNS Uniqueness Step 6 Complete

**Date:** 2026-01-24
**Session Focus:** Implement GNS-U5 and GNS-U6 (Isometry + Dense range)

---

## Completed This Session

1. **Implemented GNS-U5 (af-tests-ywt): Prove extension is isometry**
   - `gnsIntertwinerQuotientFun_isometry` - extract isometry from LinearIsometry
   - `gnsIntertwinerFun_isometry` - extension is isometry via `Isometry.completion_extension`
   - `gnsIntertwiner_norm` - norm preservation via `Isometry.norm_map_of_map_zero`
   - `gnsIntertwinerLinearIsometry` - wrapped as `LinearIsometry H_φ →ₗᵢ[ℂ] H`

2. **Implemented GNS-U6 (af-tests-5nd): Prove intertwiner has dense range**
   - `gnsIntertwiner_range_contains_orbit` - π(a)ξ is in range of U
   - `gnsIntertwiner_orbit_subset_range` - orbit ⊆ range(U)
   - `gnsIntertwiner_denseRange` - U has dense range via `Dense.mono`

---

## Current State

- **GNS existence theorem (`gns_theorem`):** Proven
- **GNS uniqueness theorem (`gns_uniqueness`):** In Progress (6/12 steps)
- **Build status:** Passing (zero sorries)
- **File:** `Main/UniquenessExtension.lean` (175 lines)
- **Next ready issue:** `af-tests-usd` (GNS-U7: Prove intertwiner is surjective)

---

## GNS Uniqueness Progress

| Step | ID | Description | Status |
|------|----|-------------|--------|
| 1 | af-tests-aov | Linearity of U₀ | Done |
| 2 | af-tests-6tj | LinearMap structure | Done |
| 3 | af-tests-rb9 | LinearIsometry on quotient | Done |
| 4 | af-tests-hqt | Extension to Hilbert space | Done |
| 5 | af-tests-ywt | Extension is isometry | Done |
| 6 | af-tests-5nd | Dense range | Done |
| 7 | af-tests-usd | Surjectivity | Ready |
| 8 | af-tests-7hr | LinearIsometryEquiv | Blocked by 7 |
| 9 | af-tests-7em | Cyclic vector mapping | Blocked by 8 |
| 10 | af-tests-2dx | Intertwining on quotient | Blocked by 8 |
| 11 | af-tests-5xr | Full intertwining | Blocked by 10 |
| 12 | af-tests-4f9 | Final theorem | Blocked by 9,11 |

---

## Next Steps

Start with `af-tests-usd` (GNS-U7):
```bash
bd show af-tests-usd           # View details
bd update af-tests-usd --status=in_progress  # Claim it
```

Implement in `Main/UniquenessExtension.lean`:
- `gnsIntertwiner_surjective` - isometry with dense range into complete space is surjective

---

## Key Implementation Details

### Isometry Extension Pattern
```lean
theorem gnsIntertwinerFun_isometry ... : Isometry (gnsIntertwinerFun ...) :=
  (gnsIntertwinerQuotientFun_isometry ...).completion_extension
```

### Dense Range via Subset
```lean
theorem gnsIntertwiner_denseRange ... (hξ_cyclic : DenseRange (fun a => π a ξ)) :
    DenseRange (gnsIntertwiner ...) :=
  hξ_cyclic.mono (gnsIntertwiner_orbit_subset_range ...)
```

Key insight: `Dense.mono` says if S ⊆ T and S is dense, then T is dense.

---

## Files Modified This Session

- Modified: `AfTests/GNS/Main/UniquenessExtension.lean` (107 → 175 lines)
- Modified: `docs/GNS/learnings/completion-topology.md` (added isometry norm section)
- Modified: `HANDOFF.md` (this file)

---

## Learnings

### Isometry Norm Preservation
`Isometry` guarantees `edist (f x) (f y) = edist x y`. For norm preservation, use
`Isometry.norm_map_of_map_zero` which requires `f 0 = 0`.

### Dense Range via Containment
Use `Dense.mono`: if dense set S ⊆ T, then T is dense. Applied as:
`hξ_cyclic.mono (orbit_subset_range ...)` to get `DenseRange (gnsIntertwiner ...)`.
