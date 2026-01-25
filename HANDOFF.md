# Handoff: 2026-01-25 (Session 27)

## Completed This Session

### Added Cyclic Vector Identity (CyclicIdentity.lean)

Created new file with the key GNS identity:

```lean
theorem gnsRep_cyclicVector (a : FreeStarAlgebra n) :
    φ.gnsRep a φ.gnsCyclicVector = coe'(Submodule.Quotient.mk a)

theorem gnsRep_inner_cyclicVector (a : FreeStarAlgebra n) :
    ⟨Ω, π(a)Ω⟩_ℝ = φ a
```

This proves **Step 4** of what was needed for `gns_representation_exists`:
- `φ(a) = ⟨Ω, π(a)Ω⟩_ℝ` in the real Hilbert space

Key insight: `gnsInner [1] [a] = φ(star a * 1)`, so need `sesqForm_symm` to get `φ(a)`.

---

## Current State

### Phase 1-6: COMPLETE (0 sorries)

### Phase 7-8: **1 sorry remaining**

| File | Status | LOC | Sorries | Notes |
|------|--------|-----|---------|-------|
| Representation/Constrained.lean | Done | 87 | 0 | |
| Representation/VectorState.lean | Done | 143 | 0 | |
| Representation/GNSConstrained.lean | In Progress | 126 | **1** | `gns_representation_exists` |
| GNS/NullSpace.lean | Done | 142 | 0 | |
| GNS/Quotient.lean | Done | 182 | 0 | |
| GNS/PreRep.lean | Done | 65 | 0 | |
| GNS/Completion.lean | Done | 118 | 0 | |
| GNS/Complexify.lean | Done | 232 | 0 | Exceeds 200 (tracked) |
| GNS/ComplexifyInner.lean | Done | 160 | 0 | |
| GNS/ComplexifyGNS.lean | Done | 76 | 0 | |
| GNS/Bounded.lean | Done | 148 | 0 | |
| GNS/Extension.lean | Done | 242 | 0 | Exceeds 200 (tracked) |
| GNS/Star.lean | Done | ~326 | 0 | Exceeds 200 (tracked) |
| GNS/Constrained.lean | Done | 138 | 0 | Generator positivity PROVEN |
| GNS/CyclicIdentity.lean | **NEW** | 76 | 0 | Cyclic vector identity |

---

## What's Next

**Only 1 sorry remains:** `gns_representation_exists` in `GNSConstrained.lean:107`

This requires building a `ConstrainedStarRep n` from the GNS construction. Checklist:

1. ✅ CompleteSpace for `gnsHilbertSpaceComplex`
2. ✅ Generator positivity: `gnsRepComplex_generator_isPositive`
3. ✅ **StarAlgHom for gnsRepComplex** - ALL DONE
4. ✅ **Cyclic vector identity (real)**: ⟨Ω, π(a)Ω⟩_ℝ = φ(a) - DONE in CyclicIdentity.lean
5. ❌ **Cyclic vector identity (complex)**: Re⟨Ω_ℂ, π_ℂ(a)Ω_ℂ⟩ = φ(a)

For Step 5, need to show:
- `π_ℂ(a)(Ω, 0) = (π(a)Ω, 0)` (componentwise action on embedded vector)
- `Re⟨(Ω, 0), (π(a)Ω, 0)⟩_ℂ = ⟨Ω, π(a)Ω⟩_ℝ` (by Complexification.inner_re)
- Then use `gnsRep_inner_cyclicVector`

---

## Known Issues

- **Star.lean exceeds 200 LOC** (~326 LOC) - tracked by af-tests-kq0q
- **Extension.lean exceeds 200 LOC** (242 LOC) - tracked by af-tests-qlhz
- **completion-topology.md exceeds 200 LOC** (~490 LOC) - tracked by af-tests-8oaj
- **LEARNINGS_misc.md exceeds 200 LOC** (316 LOC) - tracked by af-tests-2d6o
- **Complexify.lean exceeds 200 LOC** (232 LOC) - tracked by af-tests-muey

---

## Files Modified This Session

- `AfTests/ArchimedeanClosure/GNS/CyclicIdentity.lean` (NEW - cyclic vector identity)
- `docs/ArchimedeanClosure/LEARNINGS_states.md` (added cyclic vector identity docs)
- `HANDOFF.md` (this file)
