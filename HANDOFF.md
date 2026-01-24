# Handoff: 2026-01-24

## Completed This Session
- **AC-P6.3 COMPLETE**: Created `Dual/SeparatingFunctional.lean` (114 LOC, 0 sorries)
  - `not_in_closure_ne_zero`: A ∉ M̄ implies A ≠ 0 (since 0 ∈ M ⊆ M̄)
  - `separatingOnSpan`: Linear map ψ₀ : span{A} →ₗ[ℝ] ℝ with ψ₀(A) = -1
  - `separatingOnSpan_apply_A`: ψ₀(A) = -1 < 0
  - `separatingOnSpan_apply_smul`: ψ₀(c • A) = -c
  - `separatingOnSpan_nonneg_on_M_cap_span`: ψ₀ ≥ 0 on M ∩ span{A}
  - **Key Pattern**: Used `LinearPMap.mkSpanSingleton` to define linear map on span

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
| Dual/RieszApplication.lean | Not Started | - | - |
| Dual/ComplexExtension.lean | Not Started | - | - |
| Dual/Normalization.lean | Not Started | - | - |

---

## Next Steps

1. **AC-P6.4**: RieszApplication.lean - Apply Riesz extension theorem
2. **AC-P6.5**: ComplexExtension.lean - Extend real functional to complex
3. **AC-P6.6**: Normalization.lean - Normalize to get M-positive state

---

## Key Learnings Reference

See `docs/ArchimedeanClosure/LEARNINGS.md` for index, including:
- `LEARNINGS_misc.md`: `ofFunction` pattern, closedness proofs, ciSup patterns, **seminorm closure pattern**
- `LEARNINGS_states.md`: Cauchy-Schwarz, Archimedean bounds

### LinearPMap.mkSpanSingleton Pattern (NEW)
To define a linear map on span{A} for A ≠ 0:
```lean
noncomputable def myLinearMap (hA : A ≠ 0) : Submodule.span ℝ {A} →ₗ[ℝ] ℝ :=
  (LinearPMap.mkSpanSingleton (K := ℝ) A (targetValue : ℝ) hA).toFun

-- Apply formula: ⟨c • A, _⟩ = c • ⟨A, _⟩ in submodule, then use LinearMap.map_smul
-- Result: myLinearMap(c • A) = c * targetValue
```

Key lemmas:
- `LinearPMap.mkSpanSingleton_apply`: f(A) = targetValue
- `Submodule.mem_span_singleton`: x ∈ span{A} ↔ ∃ c, c • A = x

---

## Files Modified This Session

- `AfTests/ArchimedeanClosure/Dual/SeparatingFunctional.lean` (NEW, 114 LOC, 0 sorries)
- `HANDOFF.md` (this file)

