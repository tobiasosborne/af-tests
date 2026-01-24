# Handoff: GNS Uniqueness Step 4 Complete

**Date:** 2026-01-24
**Session Focus:** Implement GNS-U4 (Extend intertwiner to Hilbert space)

---

## Completed This Session

1. **Implemented GNS-U4 (af-tests-hqt): Extend intertwiner to Hilbert space**
   - Created `Main/UniquenessExtension.lean` (107 lines, no sorries)
   - `gnsIntertwinerFun` - extended function via `UniformSpace.Completion.extension`
   - `gnsIntertwiner` - wrapped as `ContinuousLinearMap` H_φ →L[ℂ] H
   - Proved linearity via density argument using `induction_on₂`/`induction_on`

---

## Current State

- **GNS existence theorem (`gns_theorem`):** Proven
- **GNS uniqueness theorem (`gns_uniqueness`):** In Progress (4/12 steps)
- **Build status:** Passing (zero sorries)
- **Next ready issue:** `af-tests-ywt` (GNS-U5: Prove extension is isometry)

---

## GNS Uniqueness Progress

| Step | ID | Description | Status |
|------|----|-------------|--------|
| 1 | af-tests-aov | Linearity of U₀ | Done |
| 2 | af-tests-6tj | LinearMap structure | Done |
| 3 | af-tests-rb9 | LinearIsometry on quotient | Done |
| 4 | af-tests-hqt | Extension to Hilbert space | Done |
| 5 | af-tests-ywt | Extension is isometry | Ready |
| 6 | af-tests-5nd | Dense range | Blocked by 5 |
| 7 | af-tests-usd | Surjectivity | Blocked by 6 |
| 8 | af-tests-7hr | LinearIsometryEquiv | Blocked by 7 |
| 9 | af-tests-7em | Cyclic vector mapping | Blocked by 8 |
| 10 | af-tests-2dx | Intertwining on quotient | Blocked by 8 |
| 11 | af-tests-5xr | Full intertwining | Blocked by 10 |
| 12 | af-tests-4f9 | Final theorem | Blocked by 9,11 |

---

## Next Steps

Start with `af-tests-ywt` (GNS-U5):
```bash
bd show af-tests-ywt           # View details
bd update af-tests-ywt --status=in_progress  # Claim it
```

Implement in `Main/UniquenessExtension.lean`:
- `gnsIntertwiner_norm` - prove ‖U(x)‖ = ‖x‖ using `Isometry.completion_extension`
- `gnsIntertwinerLinearIsometry` - wrap as LinearIsometry

---

## Key Implementation Details

### Extension Pattern
Used `UniformSpace.Completion.extension` which extends uniformly continuous functions:
```lean
noncomputable def gnsIntertwinerFun ... : φ.gnsHilbertSpace → H :=
  UniformSpace.Completion.extension (gnsIntertwinerQuotientFun ...)
```

### Linearity by Density
Proved `map_add'` and `map_smul'` using completion induction:
```lean
refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
· -- IsClosed proof
· -- Proof on dense quotient
```

---

## Files Modified This Session

- Created: `AfTests/GNS/Main/UniquenessExtension.lean` (107 lines)
- Modified: `HANDOFF.md` (this file)

---

## Learning: Extension via Completion

The key mathlib API for extending isometries to completions:
- `UniformSpace.Completion.extension f` - extends uniformly continuous `f : α → β` to `Completion α → β`
- `UniformSpace.Completion.extension_coe hf a` - proves extension agrees on embedded elements
- `UniformSpace.Completion.continuous_extension` - extension is continuous

For linearity, must prove manually via `induction_on`/`induction_on₂` with `isClosed_eq`.
