# Handoff: GNS Construction Progress

**Date:** 2026-01-24
**Session Focus:** PreHilbert/Seminorm.lean implementation

---

## Completed This Session

1. **Implemented P3: PreHilbert/Seminorm.lean** (af-tests-q9f)
   - Created `State.gnsNorm : gnsQuotient φ → ℝ` (96 LOC, no sorries)
   - Defined `PreInnerProductSpace.Core` instance for mathlib compatibility
   - Key discovery: Physics vs Math inner product convention mismatch
   - Defined: `gnsNorm`, `gnsNorm_mk`, `gnsInner_self_nonneg`, `gnsInner_self_im`
   - Added: `gnsInner_smul_right` for mathlib convention compatibility

---

## Current State

- **Build status:** Passing
- **Sorry count:** 3 total (unchanged)
  - State/Positivity.lean:57 - `sesqForm_conj_symm`
  - State/CauchySchwarz.lean:48 - `inner_mul_le_norm_mul_norm_weak`
  - State/CauchySchwarz.lean:62 - `inner_mul_le_norm_mul_norm`

---

## GNS Issue Summary

### Phase 1: States (3 files)
| Issue ID | File | Status | Notes |
|----------|------|--------|-------|
| `af-tests-li5` | State/Basic.lean | **Proven** | No sorries |
| `af-tests-dor` | State/Positivity.lean | **Structure Done** | 1 sorry (uo6) |
| `af-tests-s50` | State/CauchySchwarz.lean | **Structure Done** | 2 sorries (03g, bgs) |

### Phase 2: Null Space (3 files)
| Issue ID | File | Status | Notes |
|----------|------|--------|-------|
| `af-tests-aqa` | NullSpace/Basic.lean | **Proven** | No sorries |
| `af-tests-y0u` | NullSpace/LeftIdeal.lean | **Proven** | No sorries |
| `af-tests-ei1` | NullSpace/Quotient.lean | **Proven** | No sorries |

### Phase 3: PreHilbert (in progress)
| Issue ID | File | Status | Notes |
|----------|------|--------|-------|
| `af-tests-ec1` | PreHilbert/InnerProduct.lean | **Proven** | No sorries |
| `af-tests-q9f` | PreHilbert/Seminorm.lean | **Proven** | No sorries |
| `af-tests-9me` | PreHilbert/Positive.lean | **Not Started** | Now ready |

---

## Next Steps (Priority Order)

1. **Phase 3** - PreHilbert/Positive.lean (af-tests-9me) - now unblocked
2. Sorry elimination (P3): uo6, 03g, bgs
3. Refactor LEARNINGS.md (exceeds 200 LOC at 231 lines)

---

## Key Learning This Session

**Inner Product Convention Mismatch:** The GNS inner product `⟨[a], [b]⟩ = φ(b*a)`
uses physics convention (linear in first arg), but mathlib expects math convention
(conjugate-linear in first arg). Resolution: define `Inner` with swapped arguments.

See `docs/GNS/LEARNINGS.md` for full details.

---

## Files Modified This Session

- Created: `AfTests/GNS/PreHilbert/Seminorm.lean` (96 LOC, no sorries)
- Updated: `docs/GNS/LEARNINGS.md` (added convention mismatch entry)
- Updated: `HANDOFF.md`

---

## Commands for Next Session

```bash
bd ready
bd show af-tests-9me  # PreHilbert/Positive.lean
```
