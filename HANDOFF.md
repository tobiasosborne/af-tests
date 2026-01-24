# Handoff: GNS Uniqueness Step 1 Complete

**Date:** 2026-01-24
**Session Focus:** Implement GNS-U1 (linearity of intertwiner on quotient)

---

## Completed This Session

1. **Implemented GNS-U1 (af-tests-aov): Linearity of intertwiner**
   - `gnsIntertwinerQuotient_add` - preserves addition
   - `gnsIntertwinerQuotient_smul` - preserves scalar multiplication
   - `gnsIntertwinerQuotient_zero` - maps zero to zero
   - All proofs complete, no sorries
   - File: `Main/Uniqueness.lean` (176 lines, under 200 limit)

2. **Documented learning**
   - Added section on "Scalar Multiplication with StarAlgHom" to
     `docs/GNS/learnings/quotient-construction.md`
   - Key insight: `map_smul` doesn't work directly; use `Algebra.smul_def`
     and `AlgHomClass.commutes` instead

---

## Current State

- **GNS existence theorem (`gns_theorem`):** ✅ Proven
- **GNS uniqueness theorem (`gns_uniqueness`):** ⏳ In Progress (1/12 steps)
- **Build status:** Passing (zero sorries)
- **Next ready issue:** `af-tests-6tj` (GNS-U2: LinearMap structure)

---

## GNS Uniqueness Progress

| Step | ID | Description | Status |
|------|----|-------------|--------|
| 1 | af-tests-aov | Linearity of U₀ | ✅ Done |
| 2 | af-tests-6tj | LinearMap structure | Ready |
| 3 | af-tests-rb9 | LinearIsometry on quotient | Blocked by 2 |
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

Start with `af-tests-6tj` (GNS-U2):
```bash
bd show af-tests-6tj           # View details
bd update af-tests-6tj --status=in_progress  # Claim it
```

Then implement in `Main/Uniqueness.lean`:
- `gnsIntertwinerQuotientLinearMap` - wrap the function as a LinearMap using
  the three lemmas proven in U1

---

## Files Modified This Session

- Modified: `AfTests/GNS/Main/Uniqueness.lean` (+53 lines: 3 linearity theorems)
- Modified: `docs/GNS/learnings/quotient-construction.md` (+27 lines: StarAlgHom smul pattern)
- Modified: `HANDOFF.md` (this file)

---

## Key Learning

**StarAlgHom scalar multiplication pattern:**
```lean
-- To prove: π(c • a) = c • π(a)
rw [Algebra.smul_def, _root_.map_mul, ContinuousLinearMap.mul_apply]
rw [AlgHomClass.commutes]
simp only [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply,
  ContinuousLinearMap.one_apply]
```

The `map_smul` lemma doesn't unify directly for StarAlgHom because the scalar
actions on source and target types are different. Decompose via `Algebra.smul_def`.
