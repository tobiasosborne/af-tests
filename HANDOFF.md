# Handoff: 2026-01-31 (Session 82)

## Completed This Session

### FiniteDimensional Instance for PeirceOne (af-n2e3)

Added `peirceOneFiniteDimensional` instance to `Peirce.lean`:

```lean
/-- PeirceOne is finite-dimensional when J is. -/
instance peirceOneFiniteDimensional {e : J} [FinDimJordanAlgebra J] :
    FiniteDimensional ℝ (PeirceOne e) :=
  inferInstanceAs (FiniteDimensional ℝ (PeirceSpace e 1))
```

This uses mathlib's `FiniteDimensional.finiteDimensional_submodule` which automatically
provides FiniteDimensional for subtypes of submodules.

### Issues Closed

- **af-n2e3**: FiniteDimensional instance for PeirceOne - DONE

---

## Current State

| Metric | Value |
|--------|-------|
| Total Sorries in Jordan/ | **26** (unchanged) |
| Build Status | PASSING |
| New instances added | 1 (peirceOneFiniteDimensional) |

---

## Next Session Recommendations

### Prove primitive_peirce_one_dim_one (af-fbx8, ~50-100 LOC)

This is the key blocker for:
- `orthogonal_primitive_peirce_sq` (H-O 2.9.4(iv))
- `exists_primitive_decomp`
- Spectral theory completion

Now that we have `no_nilpotent_of_formallyReal` and `peirceOneFiniteDimensional`,
the Artinian structure theorem approach is more feasible.

### Alternative: Address JordanTrace axiom gap (af-5zpv, P0)

The `JordanTrace` class has axioms but no concrete instances, making theorems
vacuously true. However, this is orthogonal to the spectral theory chain.

---

## Files Modified This Session

- `AfTests/Jordan/Peirce.lean` — Added import for FiniteDimensional and `peirceOneFiniteDimensional` instance (~4 LOC)
- `HANDOFF.md` — This file

---

## Key Learnings

1. **Submodule finite-dimensionality:** Mathlib's `FiniteDimensional.finiteDimensional_submodule`
   automatically provides FiniteDimensional for subtypes of submodules when the parent
   module is finite-dimensional. Use `inferInstanceAs` to pick it up.

2. **Instance hierarchy:** `FinDimJordanAlgebra J` wraps `FiniteDimensional ℝ J` with an
   attribute instance, so the FiniteDimensional instance is available for submodules.
