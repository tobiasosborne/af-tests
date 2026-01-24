# Handoff: 2026-01-24

## Session Summary
Attempted AC-P2.3 (NonEmptiness) and discovered a **critical blocking issue**:
the FreeAlgebra star structure breaks the scalar extraction approach.

---

## Completed This Session

1. **AC-P2.3: S_M non-emptiness** (beads: af-tests-dlx) - BLOCKED
   - Created `AfTests/ArchimedeanClosure/State/NonEmptiness.lean` (103 LOC)
   - `scalarExtraction` - defined using `FreeAlgebra.algebraMapInv` ✓
   - `scalarExtraction_one` - proven ✓
   - `scalarExtraction_generator` - proven ✓
   - `scalarExtraction_algebraMap` - proven ✓
   - `scalarExtraction_star_mul_self_nonneg` - BLOCKED (counter-example!)
   - `MPositiveStateSet_nonempty` - sorry (blocked by above)

2. **Critical Learning Documented**
   - The star structure on `FreeAlgebra ℂ X` does NOT conjugate scalars
   - For `a = algebraMap I`, we get `star a * a = algebraMap(-1)` in M
   - But `scalarExtraction(algebraMap(-1)) = -1` has NEGATIVE real part!
   - This breaks the standard proof that scalar extraction gives M-positive state

---

## Current State

### Archimedean Closure: Phase 2 BLOCKED

| File | Status | LOC | Sorries |
|------|--------|-----|---------|
| Algebra/FreeStarAlgebra.lean | ✅ Done | 53 | 0 |
| Algebra/QuadraticModule.lean | ✅ Done | 93 | 0 |
| Algebra/Archimedean.lean | ✅ Done | 46 | 0 |
| State/MPositiveState.lean | ✅ Done | 92 | 0 |
| State/MPositiveStateProps.lean | ⚠️ Sorries | 69 | 2 |
| State/NonEmptiness.lean | ⛔ BLOCKED | 103 | 2 |

**Total: 456 LOC** (4 sorries)

### GNS Construction: COMPLETE
- No changes this session

---

## Critical Issue: Star Structure

The star structure from `Mathlib.Algebra.Star.Free` satisfies:
```
star (algebraMap c) = algebraMap c    -- scalars FIXED, not conjugated!
```

This means `star(I·1) * (I·1) = -1·1 ∈ M`, but scalar extraction gives `-1 < 0`.

**Resolution paths documented in LEARNINGS.md:**
1. Work over ℝ instead of ℂ
2. Quotient algebra to enforce conjugation
3. Restrict M definition
4. Axiomatize non-emptiness
5. Use different base state construction

---

## Next Steps

1. **Architectural decision needed**: How to resolve the star structure issue?
   - Option A: Rebuild Phase 1 over ℝ (significant refactor)
   - Option B: Add `StarModule ℂ` via quotient (complex)
   - Option C: Axiomatize `MPositiveStateSet_nonempty` (pragmatic)
   - Option D: Restrict M to exclude pure scalar squares (changes semantics)

2. **Phase 3+ can proceed** if we axiomatize non-emptiness:
   - af-tests-03l: AC-P3.1: Cauchy-Schwarz
   - af-tests-fjy: AC-P3.3: Generating cone lemma
   - af-tests-il1: AC-P4.1: State space topology

---

## Files Modified This Session

- `AfTests/ArchimedeanClosure/State/NonEmptiness.lean` (NEW - 103 LOC)
- `docs/ArchimedeanClosure/LEARNINGS.md` (updated with critical finding)
- `HANDOFF.md` (this file)

---

## Open Sorries to Track

| File | Theorem | Reason |
|------|---------|--------|
| MPositiveStateProps.lean | `apply_real_of_isSelfAdjoint` | Needs polarization identity |
| MPositiveStateProps.lean | `map_star` | Needs polarization from positivity |
| NonEmptiness.lean | `scalarExtraction_star_mul_self_nonneg` | **BLOCKED**: Counter-example exists |
| NonEmptiness.lean | `MPositiveStateSet_nonempty` | Blocked by above |

---

## Open Issues

```
bd ready
```
- Phase 2: af-tests-dlx (NonEmptiness) - IN PROGRESS but BLOCKED
- Phase 3: af-tests-03l (Cauchy-Schwarz), af-tests-fjy (GeneratingCone)
- Phase 4+: Multiple issues ready
