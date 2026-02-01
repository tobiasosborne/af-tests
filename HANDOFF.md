# Handoff: 2026-02-01 (Session 103)

## Session Summary

Attempted to add IsScalarTower/IsArtinianRing/IsReduced for P1PowerSubmodule.
**Result:** Reverted - typeclass threading too complex for remaining context.

---

## Current State

| Metric | Value |
|--------|-------|
| Total Sorries | **5** (Primitive.lean) |
| Build Status | **PASSING** |
| Session Work | Research on instance threading |

---

## 🎯 NEXT STEP: P1PowerSubmodule Instances

### The Challenge

`P1PowerSubmodule_commRing` is a `def` (not `instance`) because it requires:
- `he : IsIdempotent e`
- `hx : x ∈ PeirceSpace e 1`

When defining dependent instances (IsScalarTower, IsArtinianRing, IsReduced),
Lean can't automatically find the CommRing. Must use explicit `@` notation or `letI`.

### Key Insight: Ring Power vs Jordan Power

For `a ∈ P1PowerSubmodule e x` with ring identity `e`:
- Ring `a^0 = e` (NOT `jone`)
- Ring `a^n = jpow a.val n` for n ≥ 1

Need lemma `P1PowerSubmodule_npow_eq_jpow` relating these.

### Required Lemmas (in order)

```lean
-- 1. Power relationship (needed for IsReduced)
theorem P1PowerSubmodule_npow_eq_jpow (e x : J) (he : IsIdempotent e)
    (hx : x ∈ PeirceSpace e 1) (a : ↥(P1PowerSubmodule e x)) (n : ℕ) (hn : n ≥ 1) :
    letI := P1PowerSubmodule_commRing e x he hx
    (a ^ n).val = jpow a.val n

-- 2. Scalar tower (needed for of_finite)
def P1PowerSubmodule_isScalarTower (e x : J) (he : IsIdempotent e)
    (hx : x ∈ PeirceSpace e 1) :
    letI := P1PowerSubmodule_commRing e x he hx
    IsScalarTower ℝ ↥(P1PowerSubmodule e x) ↥(P1PowerSubmodule e x)

-- 3. Artinian (uses of_finite)
def P1PowerSubmodule_isArtinianRing [FinDimJordanAlgebra J] (e x : J) ...

-- 4. Reduced (uses npow_eq_jpow + no_nilpotent_of_formallyReal)
def P1PowerSubmodule_isReduced [FormallyRealJordan J] (e x : J) ...
```

### Pattern from PowerSubmodule

See lines 400-438 for working pattern. Key differences:
- PowerSubmodule uses `instance` (no constraints)
- P1PowerSubmodule needs `def` with explicit constraints
- Must use `letI := P1PowerSubmodule_commRing e x he hx` in proofs

### Issue: SMul Instance Threading

The `IsScalarTower` definition requires explicit SMul instances:
```lean
@IsScalarTower ℝ S S inst_R_S inst_S_S
```

For P1PowerSubmodule:
- `inst_R_S` comes from Submodule.module (automatic)
- `inst_S_S` must come from CommRing multiplication

The `Algebra.toSMul` path didn't work (`Submodule.algebra'` doesn't exist).
Try `instSMulOfMul` instead (deprecated warning showed this).

---

## Dependency Chain

```
P1PowerSubmodule_commRing    ✓ - Session 102
    ↓
P1PowerSubmodule_npow_eq_jpow  ← NEXT (for IsReduced)
    ↓
P1PowerSubmodule_isScalarTower ← NEXT (for of_finite)
    ↓
P1PowerSubmodule_isArtinianRing
    ↓
P1PowerSubmodule_isReduced
    ↓
primitive_peirce_one_dim_one (line 722 sorry)
```

---

## Files

- `AfTests/Jordan/Primitive.lean` - No changes this session

