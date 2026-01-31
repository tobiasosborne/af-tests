# Handoff: 2026-01-31 (Session 69)

## ⚠️ CRITICAL: primitive_dichotomy Theorem May Be Incorrect

Session 69 discovered that the proof strategy for `primitive_dichotomy` is flawed.
**Issue af-xp4b created to track investigation.**

### The Problem
The handoff claimed: "If `jmul e f ≠ 0`, then `jmul e f ∈ P₁(e) ∩ P₁(f)`."
But this requires the P₁₂(e) component of f to be 0, which is NOT true in general.

### Potential Counterexample
In 2×2 symmetric matrices:
- e = diag(1,0), f = [[1/2,1/2],[1/2,1/2]]
- Both are primitive (rank-1 projections)
- jmul e f ≠ 0, jmul e f ≠ e, jmul e f ≠ f, e ≠ f

### Current State of primitive_dichotomy
- **Case jmul e f = 0:** PROVEN (orthogonal)
- **Case jmul e f = e:** PROVEN (e = f via primitivity of f)
- **Case jmul e f = f:** PROVEN (e = f via primitivity of e)
- **Case jmul e f ∉ {0, e, f}:** SORRY (may be impossible to prove as stated)

### Possible Resolutions
1. Add hypotheses (e.g., e, f from same spectral family)
2. Require JB-algebra completeness (not just formally real)
3. Change statement to "orthogonal or unitarily equivalent"

---

## ⚠️ AXIOM GAPS (Deferred, P0 tracked)

| Issue | Problem | Status |
|-------|---------|--------|
| af-5zpv | `JordanTrace` needs concrete instances | P0, deferred |
| af-2dzb | `trace_L_selfadjoint` needs proof | P0, blocked by af-5zpv |
| af-pxqu | `FormallyRealTrace` needs instances | P0, blocked by af-5zpv |

---

## Completed This Session (69)

### 1. Partial Proof of primitive_dichotomy
- **File:** `AfTests/Jordan/Primitive.lean`
- 3 of 4 cases proven (jmul e f = 0, e, or f)
- Remaining case documented with potential counterexample

### 2. Issue Created: af-xp4b
- Documents the theorem statement concern
- P1 priority for investigation

---

## Current State

| Metric | Value |
|--------|-------|
| Total LOC | ~25,600 |
| Total Sorries | 25 |
| Axiom Gaps | 3 (P0, deferred) |
| Issues Open | ~24 |

---

## Blocking Sorries in Primitive.lean (3 sorries)

| Line | Theorem | Status |
|------|---------|--------|
| 116 | `primitive_dichotomy` | 3/4 cases proven, 1 case blocked (af-xp4b) |
| 129 | `exists_primitive_decomp` | Blocked by dichotomy resolution |
| 136 | `csoi_refine_primitive` | Blocked by exists_primitive_decomp |

---

## 🎯 NEXT SESSION: Investigate primitive_dichotomy

### Option A: Prove the Remaining Case
Search literature (H-O, McCrimmon) for correct proof of primitive dichotomy.
May need additional machinery (JB-algebra structure, lattice of projections).

### Option B: Weaken the Theorem
Change to "orthogonal or unitarily equivalent" which is the standard JB-algebra result.

### Option C: Add Hypotheses
Require e, f to come from the same CSOI refinement (spectral family).

### Key Question
Is the theorem as stated actually true for finite-dimensional formally real Jordan algebras?
The 2×2 matrix example needs verification in Lean.

---

## Files Modified This Session

- `AfTests/Jordan/Primitive.lean` — Partial proof of primitive_dichotomy, documented issue
- `HANDOFF.md` — Updated with critical finding

