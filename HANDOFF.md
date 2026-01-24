# Handoff: GNS Uniqueness Step 8 Complete

**Date:** 2026-01-24
**Session Focus:** Implement GNS-U7 and GNS-U8 (Surjectivity + LinearIsometryEquiv)

---

## Completed This Session

1. **Implemented GNS-U7 (af-tests-usd): Prove intertwiner is surjective**
   - `Isometry.surjective_of_completeSpace_denseRange` - general theorem
   - `gnsIntertwiner_surjective` - applied to GNS intertwiner

2. **Implemented GNS-U8 (af-tests-7hr): Construct LinearIsometryEquiv**
   - `gnsIntertwiner_injective` - isometries are injective
   - `gnsIntertwiner_bijective` - combine injective + surjective
   - `gnsIntertwinerLinearEquiv` - construct via `LinearEquiv.ofBijective`
   - `gnsIntertwinerEquiv` - wrap as `LinearIsometryEquiv H_φ ≃ₗᵢ[ℂ] H`

---

## Current State

- **GNS existence theorem (`gns_theorem`):** Proven
- **GNS uniqueness theorem (`gns_uniqueness`):** In Progress (8/12 steps)
- **Build status:** Passing (zero sorries)
- **Files:**
  - `Main/UniquenessExtension.lean` (197 lines)
  - `Main/UniquenessEquiv.lean` (80 lines) - NEW
- **Next ready issues:** `af-tests-7em` (GNS-U9), `af-tests-2dx` (GNS-U10)

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
| 8 | af-tests-7hr | LinearIsometryEquiv | Done |
| 9 | af-tests-7em | Cyclic vector mapping | Ready |
| 10 | af-tests-2dx | Intertwining on quotient | Ready |
| 11 | af-tests-5xr | Full intertwining | Blocked by 10 |
| 12 | af-tests-4f9 | Final theorem | Blocked by 9,11 |

---

## Next Steps

Two issues are now ready (can be done in either order):

**GNS-U9 (af-tests-7em):** Cyclic vector mapping
- Prove `gnsIntertwinerEquiv φ.gnsCyclicVector = ξ`
- File: `Main/UniquenessEquiv.lean` (append)

**GNS-U10 (af-tests-2dx):** Intertwining on quotient
- Prove `U([ab]) = π(a)(U[b])` on quotient elements
- File: `Main/UniquenessIntertwine.lean` (new)

---

## Key Implementation Details

### LinearIsometryEquiv Construction
```lean
noncomputable def gnsIntertwinerEquiv ... : φ.gnsHilbertSpace ≃ₗᵢ[ℂ] H where
  toLinearEquiv := LinearEquiv.ofBijective (gnsIntertwiner ...).toLinearMap
    (gnsIntertwiner_bijective ...)
  norm_map' := gnsIntertwiner_norm ...
```

Key insight: `LinearEquiv.ofBijective` constructs a `LinearEquiv` from a bijective `LinearMap`.

---

## Files Modified This Session

- Modified: `AfTests/GNS/Main/UniquenessExtension.lean` (175 → 197 lines)
- Created: `AfTests/GNS/Main/UniquenessEquiv.lean` (80 lines)
- Modified: `docs/GNS/learnings/completion-topology.md`
- Modified: `HANDOFF.md` (this file)

---

## Learnings

### Isometry Surjectivity from Dense Range
See `docs/GNS/learnings/completion-topology.md` for full details.

### LinearIsometryEquiv Construction
To construct `LinearIsometryEquiv` from a bijective norm-preserving linear map:
1. Use `LinearEquiv.ofBijective` with the underlying `LinearMap` and bijectivity proof
2. Wrap with `LinearIsometryEquiv.mk` (or structure syntax) with norm preservation proof
