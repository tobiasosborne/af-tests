# Handoff: GNS Construction Progress

**Date:** 2026-01-24
**Session Focus:** Tight Cauchy-Schwarz investigation (af-tests-dwe)

---

## Completed This Session

1. **Investigated af-tests-dwe** - Documented blockers for tight C-S proof
   - Attempted proof using μ = -c/d optimization
   - Identified 3 specific Lean tactic blockers (see learnings)
   - Documented proposed decomposition into helper lemmas

2. **Updated Learnings**
   - Added "Session 2026-01-24 Blockers" to state-and-positivity.md

---

## Current State

- **Build status:** Passing (with 1 sorry)
- **Sorry count:** 1 total
  - State/CauchySchwarz.lean:137 - tight C-S case φ(b*b).re > 0 (af-tests-dwe)

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
| af-tests-dwe | CauchySchwarz.lean:137 | Tight C-S - needs helper lemmas |

---

## Next Steps (Priority Order)

1. **af-tests-dwe** - Create helper lemmas for tight C-S (see technical notes)
2. **Phase 5** - Representation/Star.lean (af-tests-8r4)
3. **Phase 6** - Main theorems (after P5 complete)

---

## Files Modified This Session

- Updated: `docs/GNS/learnings/state-and-positivity.md` (added blockers section)
- Updated: `HANDOFF.md`

---

## Technical Notes for Next Session

**For af-tests-dwe (tight C-S case 2) - BLOCKING ISSUES:**

1. **Term structure mismatch:** After `simp [star_add, add_mul, ...]`:
   - Result: `star a * a + conj(μ) • (star b * a) + μ • (star a * b + conj(μ) • (star b * b))`
   - Problem: Nested, not flat. `smul_smul` can't rewrite

2. **simp recursion limit:** When μ = -c/d, `simp` with division lemmas hits max recursion

3. **Rewrite mismatch:** After `Complex.mul_re` simp, terms become real arithmetic
   - `μ.re * (conj c).re - μ.im * (conj c).im`
   - Can't rewrite with complex-level equation `μ * conj c = -|c|²/d`

**Proposed solution:** Write helper lemmas that work entirely in ℝ:
- `tight_cs_cross_re`: Compute `(μ*conj(c) + conj(μ)*c + |μ|²*d).re` when d real
- Avoid passing complex division through simp

---

## Commands for Next Session

```bash
bd ready                 # See available work
bd show af-tests-dwe     # Tight C-S remaining case
```
