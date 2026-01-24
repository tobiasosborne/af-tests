# Handoff: GNS Uniqueness Step 7 Complete

**Date:** 2026-01-24
**Session Focus:** Implement GNS-U7 (Surjectivity of intertwiner)

---

## Completed This Session

1. **Implemented GNS-U7 (af-tests-usd): Prove intertwiner is surjective**
   - `Isometry.surjective_of_completeSpace_denseRange` - general theorem: isometry from complete space with dense range is surjective
   - `gnsIntertwiner_surjective` - applied to GNS intertwiner

---

## Current State

- **GNS existence theorem (`gns_theorem`):** Proven
- **GNS uniqueness theorem (`gns_uniqueness`):** In Progress (7/12 steps)
- **Build status:** Passing (zero sorries)
- **File:** `Main/UniquenessExtension.lean` (197 lines)
- **Next ready issue:** `af-tests-7hr` (GNS-U8: Construct LinearIsometryEquiv)

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
| 7 | af-tests-usd | Surjectivity | Done |
| 8 | af-tests-7hr | LinearIsometryEquiv | Ready |
| 9 | af-tests-7em | Cyclic vector mapping | Blocked by 8 |
| 10 | af-tests-2dx | Intertwining on quotient | Blocked by 8 |
| 11 | af-tests-5xr | Full intertwining | Blocked by 10 |
| 12 | af-tests-4f9 | Final theorem | Blocked by 9,11 |

---

## Next Steps

Start with `af-tests-7hr` (GNS-U8):
```bash
bd show af-tests-7hr           # View details
bd update af-tests-7hr --status=in_progress  # Claim it
```

Implement in new file `Main/UniquenessEquiv.lean`:
- `gnsIntertwiner_injective` - isometries are injective
- `gnsIntertwiner_bijective` - combine injective + surjective
- `gnsIntertwinerEquiv` - construct `LinearIsometryEquiv H_φ ≃ₗᵢ[ℂ] H`

---

## Key Implementation Details

### Isometry Surjectivity Chain
The key insight: isometry from complete space has complete (hence closed) range.
Dense + closed = whole space.

```lean
theorem Isometry.surjective_of_completeSpace_denseRange
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace X] [CompleteSpace Y]
    {f : X → Y} (hf : Isometry f) (hd : DenseRange f) : Function.Surjective f :=
  Set.range_eq_univ.mp <| hf.isUniformInducing.isComplete_range.isClosed.closure_eq ▸
    dense_iff_closure_eq.mp hd
```

Proof chain:
1. `Isometry.isUniformInducing` - isometry is uniform inducing
2. `IsUniformInducing.isComplete_range` - range is complete (source is complete)
3. `IsComplete.isClosed` - complete sets are closed
4. Dense + closed = univ

---

## Files Modified This Session

- Modified: `AfTests/GNS/Main/UniquenessExtension.lean` (175 → 197 lines)
- Modified: `docs/GNS/learnings/completion-topology.md` (added isometry surjectivity section)
- Modified: `HANDOFF.md` (this file)

---

## Learnings

### Isometry Surjectivity from Dense Range
An isometry `f : X → Y` with dense range is surjective when `X` is complete.
The key is that uniform inducing maps preserve completeness, so the range is complete,
hence closed, and dense + closed = whole space.

Key Mathlib lemmas (not found as a single theorem):
- `Isometry.isUniformInducing`
- `IsUniformInducing.isComplete_range`
- `IsComplete.isClosed`
- `dense_iff_closure_eq`
