# Handoff: GNS Uniqueness Step 11 Complete

**Date:** 2026-01-24
**Session Focus:** Implement GNS-U9, U10, U11 (Cyclic vector + Intertwining)

---

## Completed This Session

1. **Implemented GNS-U9 (af-tests-7em): Prove cyclic vector mapping**
   - `gnsIntertwinerEquiv_cyclic` - Proves `U(Ω_φ) = ξ`

2. **Implemented GNS-U10 (af-tests-2dx): Prove intertwining on quotient**
   - `gnsIntertwiner_intertwines_quotient` - Proves `U(π_φ(a)[b]) = π(a)(U[b])`

3. **Implemented GNS-U11 (af-tests-5xr): Prove full intertwining**
   - `gnsIntertwiner_intertwines` - Proves `U(π_φ(a)x) = π(a)(Ux)` for all x ∈ H_φ
   - Proof by completion induction: continuity + dense quotient agreement

---

## Current State

- **GNS existence theorem (`gns_theorem`):** Proven
- **GNS uniqueness theorem (`gns_uniqueness`):** In Progress (11/12 steps)
- **Build status:** Passing (zero sorries)
- **Files:**
  - `Main/UniquenessExtension.lean` (197 lines)
  - `Main/UniquenessEquiv.lean` (100 lines)
  - `Main/UniquenessIntertwine.lean` (79 lines)
- **Next ready issue:** `af-tests-4f9` (GNS-U12) - Final theorem!

---

## GNS Uniqueness Progress

| Step | ID | Description | Status |
|------|----|-------------|--------|
| 1-8 | various | Foundation steps | Done |
| 9 | af-tests-7em | Cyclic vector mapping | Done |
| 10 | af-tests-2dx | Intertwining on quotient | Done |
| 11 | af-tests-5xr | Full intertwining | Done |
| 12 | af-tests-4f9 | Final theorem | Ready |

---

## Next Steps

**GNS-U12 (af-tests-4f9):** State final `gns_uniqueness` theorem
- Combine all components into the final existence statement
- File: `Main/UniquenessTheorem.lean` (new)

---

## Key Implementation Details

### Full Intertwining Proof Pattern
```lean
theorem gnsIntertwiner_intertwines ... (x : φ.gnsHilbertSpace) :
    gnsIntertwinerEquiv ... (φ.gnsRep a x) = π a (gnsIntertwinerEquiv ... x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    apply isClosed_eq
    · exact (gnsIntertwinerEquiv ...).continuous.comp (φ.gnsRep a).continuous
    · exact (π a).continuous.comp (gnsIntertwinerEquiv ...).continuous
  | ih y =>
    simp only [gnsIntertwinerEquiv_apply]
    rw [gnsRep_coe]
    exact gnsIntertwiner_intertwines_quotient ...
```

Key insight: Completion induction separates:
1. **Closure condition** (`hp`): Both sides continuous → equal on closure
2. **Dense set** (`ih`): Reduce to quotient case via `gnsRep_coe`

---

## Files Modified This Session

- Modified: `AfTests/GNS/Main/UniquenessEquiv.lean` (80 → 100 lines)
- Created: `AfTests/GNS/Main/UniquenessIntertwine.lean` (79 lines)
- Modified: `HANDOFF.md` (this file)

---

## Learnings

### Completion Induction Pattern
For extending properties from quotient to completion:
```lean
induction x using UniformSpace.Completion.induction_on with
| hp => apply isClosed_eq <cont_lhs> <cont_rhs>  -- closedness
| ih y => <reduce to quotient case>              -- dense set
```

### Key Lemmas Used
- `gnsRep_coe`: `φ.gnsRep a (x : H_φ) = (φ.gnsPreRep a x : H_φ)` on quotient
- `gnsIntertwinerEquiv_apply`: reduces equiv to underlying intertwiner
- `gnsIntertwiner_intertwines_quotient`: quotient-level intertwining

### What Was Removed
The alternative formulation `gnsIntertwinerEquiv_comp_gnsRep` using `∘L` composition
had issues with `FiniteDimensional` requirements. The point-wise formulation in
`gnsIntertwiner_intertwines` is sufficient for the final theorem.
