# Handoff: GNS Construction Progress

**Date:** 2026-01-24
**Session Focus:** Refactor - Move null_space_left_ideal out of CauchySchwarz

---

## Completed This Session

1. **Fixed P1: Misplaced theorem** (af-tests-op0)
   - Removed `null_space_left_ideal` from CauchySchwarz.lean
   - It belongs in NullSpace/LeftIdeal.lean (uses boundedness, not C-S)
   - Added note pointing to correct location
   - CauchySchwarz.lean: 95 → 92 LOC

2. **Closed related sorry issue** (af-tests-wmn)
   - The sorry was for the misplaced theorem
   - Will be re-added properly in NullSpace/LeftIdeal.lean

3. **Corrected proof strategy documentation**
   - docs/GNS/phases/02_nullspace.md: "C-S applied cleverly" → "boundedness"

4. **Updated LOC target**
   - docs/GNS/phases/01_states.md: ~100 → ~90 for CauchySchwarz.lean

5. **Documented learning**
   - Added entry in docs/GNS/LEARNINGS.md about boundedness vs C-S distinction

---

## Current State

- **Build status:** Passing
- **Sorry count:** 3 total (was 4)
  - State/Positivity.lean:57 - `sesqForm_conj_symm`
  - State/CauchySchwarz.lean:48 - `inner_mul_le_norm_mul_norm_weak`
  - State/CauchySchwarz.lean:62 - `inner_mul_le_norm_mul_norm`

---

## GNS Issue Summary

### Phase 1: States (3 files)
| Issue ID | File | Status | Notes |
|----------|------|--------|-------|
| `af-tests-li5` | State/Basic.lean | **DONE** | No sorries |
| `af-tests-dor` | State/Positivity.lean | **DONE** | 1 sorry (af-tests-uo6) |
| `af-tests-s50` | State/CauchySchwarz.lean | **DONE** | 2 sorries (03g, bgs) |

### Phase 2: Null Space (Next)
| Issue ID | File | Status | Notes |
|----------|------|--------|-------|
| `af-tests-aqa` | NullSpace/Basic.lean | **READY** | Unblocked |

### Audit Issues
| Issue ID | Priority | Status |
|----------|----------|--------|
| af-tests-7kl | P0 | **CLOSED** |
| af-tests-9u6 | P2 | **CLOSED** |
| af-tests-op0 | P1 | **CLOSED** |
| af-tests-wmn | P3 | **CLOSED** |
| af-tests-aea | P1 | OPEN |
| af-tests-pzj | P2 | OPEN |

---

## Next Steps (Priority Order)

1. **af-tests-aea** (P1) - Define status semantics in CLAUDE.md
2. **af-tests-pzj** (P2) - Fix stale line numbers in HANDOFF
3. **af-tests-aqa** (P2) - NullSpace/Basic.lean implementation
4. Sorry elimination (P3): uo6, 03g, bgs

---

## Files Modified This Session

- Edited: `AfTests/GNS/State/CauchySchwarz.lean` (removed misplaced theorem)
- Updated: `docs/GNS/phases/01_states.md` (LOC target)
- Updated: `docs/GNS/phases/02_nullspace.md` (proof strategy correction)
- Updated: `docs/GNS/LEARNINGS.md` (new entry)
- Updated: `HANDOFF.md` (this file)

---

## Commands for Next Session

```bash
# Check next P1 issue
bd ready
bd show af-tests-aea

# Or work on sorry elimination
bd show af-tests-uo6
```
