# Handoff: 2026-01-24

## Completed This Session
- **AC-P6.4 STRUCTURE**: Created `Dual/RieszApplication.lean` (147 LOC, 2 sorries)
  - `separatingPMap`: Converts separatingOnSpan to a LinearPMap
  - `separatingPMap_nonneg_on_M`: Verifies nonneg condition for Riesz
  - `generating_condition_from_decomp`: Helper showing M generates (A₀)_sa
  - `riesz_extension_exists`: Main theorem (sorry) - extends ψ₀ to full algebra
  - **KEY CHALLENGE IDENTIFIED**: Mathlib's `riesz_extension` has generating condition
    `∀ y, ∃ x ∈ domain, x + y ∈ M` which is not directly satisfied for 1-dim domain

---

## Current State

### Phase 1-2: COMPLETE

| File | Status | LOC | Sorries |
|------|--------|-----|---------|
| Algebra/FreeStarAlgebra.lean | ✅ | 56 | 0 |
| Algebra/QuadraticModule.lean | ✅ | 93 | 0 |
| Algebra/Archimedean.lean | ✅ | 46 | 0 |
| State/MPositiveState.lean | ✅ | 100 | 0 |
| State/MPositiveStateProps.lean | ✅ | 63 | 0 |
| State/NonEmptiness.lean | ✅ | 149 | 0 |

### Phase 3: COMPLETE

| File | Status | LOC | Sorries |
|------|--------|-----|---------|
| Boundedness/CauchySchwarzM.lean | ✅ | 104 | 0 |
| Boundedness/ArchimedeanBound.lean | ✅ | 73 | 0 |
| Boundedness/GeneratingCone.lean | ✅ | 134 | 0 |

---

### Phase 4: COMPLETE

| File | Status | LOC | Sorries |
|------|--------|-----|---------|
| Topology/StateTopology.lean | ✅ | 50 | 0 |
| Topology/Closedness.lean | ✅ | 138 | 0 |
| Topology/Compactness.lean | ✅ | 171 | 0 |
| Topology/Continuity.lean | Skipped | - | - |

**Phase 4 complete for compactness. Continuity optional (skipped to Phase 5).**

---

### Phase 5: COMPLETE

| File | Status | LOC | Sorries |
|------|--------|-----|---------|
| Seminorm/StateSeminorm.lean | ✅ | 89 | 0 |
| Seminorm/SeminormProps.lean | ✅ | 80 | 0 |
| Seminorm/Closure.lean | ✅ | 95 | 0 |

---

### Phase 6: IN PROGRESS

| File | Status | LOC | Sorries |
|------|--------|-----|---------|
| Dual/Forward.lean | ✅ | 67 | 0 |
| Dual/SpanIntersection.lean | ✅ | 104 | 0 |
| Dual/SeparatingFunctional.lean | ✅ | 114 | 0 |
| Dual/RieszApplication.lean | Structure | 147 | 2 |
| Dual/ComplexExtension.lean | Not Started | - | - |
| Dual/Normalization.lean | Not Started | - | - |

---

## Critical Issue: Riesz Extension Generating Condition

**Problem**: Mathlib's `riesz_extension` requires:
```
∀ y, ∃ x ∈ domain, x + y ∈ s  (where s = cone, domain = span{A})
```

This asks if M + span{A} = E, which is false for 1-dimensional span{A}.

**What we have**: `quadraticModule_selfAdjoint_generating` proves M - M = (A₀)_sa

**What we need**: Either:
1. Custom Riesz extension using our generating property
2. Separation theorem (requires inner product)
3. Direct Zorn's lemma argument

See `LEARNINGS_misc.md` for detailed analysis.

---

## Next Steps

1. **AC-P6.4 COMPLETE**: Fill sorries in RieszApplication.lean (requires mathematical work)
2. **AC-P6.5**: ComplexExtension.lean - Extend real functional to complex
3. **AC-P6.6**: Normalization.lean - Normalize to get M-positive state

---

## Key Learnings Reference

See `docs/ArchimedeanClosure/LEARNINGS.md` for index, including:
- `LEARNINGS_misc.md`: Riesz extension challenge (NEW), `ofFunction` pattern, closedness proofs
- `LEARNINGS_states.md`: Cauchy-Schwarz, Archimedean bounds

---

## Files Modified This Session

- `AfTests/ArchimedeanClosure/Dual/RieszApplication.lean` (NEW, 147 LOC, 2 sorries)
- `docs/ArchimedeanClosure/LEARNINGS_misc.md` (updated with Riesz extension analysis)
- `HANDOFF.md` (this file)

---

## Known Issues

- `LEARNINGS_misc.md` is 442 lines (exceeds 200 LOC limit) - needs split
