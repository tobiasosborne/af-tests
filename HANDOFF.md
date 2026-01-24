# Handoff: GNS Construction Progress

**Date:** 2026-01-24
**Session Focus:** Tight Cauchy-Schwarz helper lemmas (af-tests-dwe)

---

## Completed This Session

1. **Added `expand_star_add_smul` helper** (CauchySchwarz.lean:124-133)
   - Expands star(a + μ•b)*(a + μ•b) for complex μ
   - Uses star_smul, smul_smul, mul_conj, abel

2. **Documented `cross_term_opt_re` proof strategy**
   - Proof WORKS in standalone tests
   - Context-dependent simp issue: fails in CauchySchwarz.lean
   - Working strategy documented in learnings and TODO comment

3. **Updated Learnings**
   - Added "Session 2026-01-24 Progress" to state-and-positivity.md
   - Documented context-dependent simp behavior

4. **Created LOC violation issue** (af-tests-1zf)
   - state-and-positivity.md is 218 lines (limit: 200)

---

## Current State

- **Build status:** Passing (with 1 sorry)
- **Sorry count:** 1 total
  - State/CauchySchwarz.lean:153 - tight C-S case φ(b*b).re > 0 (af-tests-dwe)

---

## GNS Progress Summary

| Phase | Files | Proven | Structure Done | Not Started | Progress |
|-------|-------|--------|----------------|-------------|----------|
| P1: States | 3 | 2 | 1 | 0 | **83%** |
| P2: NullSpace | 3 | 3 | 0 | 0 | **100%** |
| P3: PreHilbert | 3 | 3 | 0 | 0 | **100%** |
| P4: HilbertSpace | 2 | 2 | 0 | 0 | **100%** |
| P5: Representation | 4 | 3 | 0 | 1 | **75%** |
| P6: Main | 3 | 0 | 0 | 3 | 0% |
| **TOTAL** | **18** | **13** | **1** | **4** | **76%** |

---

## Remaining Sorries

| Issue | File | Notes |
|-------|------|-------|
| af-tests-dwe | CauchySchwarz.lean:153 | Tight C-S - helper partially done |

---

## Next Steps (Priority Order)

1. **af-tests-1zf (P0)** - Split state-and-positivity.md to fix LOC violation
2. **af-tests-dwe** - Debug simp context issue or use explicit calc proof
3. **Phase 5** - Representation/Star.lean (af-tests-8r4)
4. **Phase 6** - Main theorems (after P5 complete)

---

## Files Modified This Session

- Modified: `AfTests/GNS/State/CauchySchwarz.lean` (added expand_star_add_smul, TODO)
- Updated: `docs/GNS/learnings/state-and-positivity.md` (added progress section)
- Updated: `HANDOFF.md`

---

## Technical Notes for Next Session

**For af-tests-dwe (tight C-S case 2):**

The `cross_term_opt_re` proof works in standalone but fails in file context:
```lean
-- This works standalone:
rw [neg_div]
simp only [map_neg, map_div₀, Complex.conj_ofReal]
-- Then: c * conj c = normSq c, field_simp, ring

-- In CauchySchwarz.lean: simp reports "no progress" after rw [neg_div]
```

**Debugging options:**
1. Use `set_option trace.simp true` to see what's happening
2. Replace simp with explicit calc proof
3. Check if imports differ between file and standalone test

---

## Commands for Next Session

```bash
bd ready                 # See available work
bd show af-tests-1zf     # LOC violation (P0)
bd show af-tests-dwe     # Tight C-S remaining case
```
