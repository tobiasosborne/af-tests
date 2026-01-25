# Handoff: 2026-01-25 (Session 14)

## Completed This Session

### Complexification Norm Preservation
Added infrastructure for embedding norm preservation:

- `Complexification.embed_inner` - ⟪embed x, embed y⟫_ℂ = (⟪x, y⟫_ℝ : ℂ)
- `Complexification.embed_norm` - ‖embed x‖_ℂ = ‖x‖_ℝ
- `MPositiveState.gnsCyclicVectorComplex_norm` - ‖Ω_ℂ‖ = 1

This establishes that the complex cyclic vector has unit norm, which is one
requirement for `gns_representation_exists`.

---

## Current State

### Phase 1-6: COMPLETE (0 sorries)

### Phase 7: STRUCTURE DONE (1 sorry remaining)

| File | Status | LOC | Sorries | Notes |
|------|--------|-----|---------|-------|
| Representation/Constrained.lean | Done | 87 | 0 | |
| Representation/VectorState.lean | Done | 143 | 0 | |
| Representation/GNSConstrained.lean | In Progress | 126 | 1 | `gns_representation_exists` |
| GNS/NullSpace.lean | Done | 142 | 0 | |
| GNS/Quotient.lean | Done | 182 | 0 | |
| GNS/PreRep.lean | Done | 65 | 0 | |
| GNS/Completion.lean | Done | 113 | 0 | |
| GNS/Complexify.lean | Done | 193 | 0 | Module + Inner |
| GNS/ComplexifyInner.lean | Done | 160 | 0 | Full InnerProductSpace + embed_norm |
| GNS/ComplexifyGNS.lean | Done | 76 | 0 | Complexified GNS + Ω_ℂ norm |
| GNS/Bounded.lean | Done | 148 | 0 | Archimedean boundedness |

---

## What's Needed for `gns_representation_exists`

The sorry requires constructing a `ConstrainedStarRep` from an M-positive state.

**What we have:**
- ✅ Complex Hilbert space: `gnsHilbertSpaceComplex`
- ✅ Cyclic vector with unit norm: `gnsCyclicVectorComplex_norm`
- ✅ Pre-representation on quotient: `gnsLeftAction`
- ✅ Boundedness: `gnsLeftAction_bounded`

**What's missing:**
1. **Extension to completion**: Need to extend `gnsLeftAction` from quotient to
   the completed Hilbert space as a `ContinuousLinearMap`
2. **Extension to complexification**: Then extend to the complexified space
3. **Star algebra homomorphism**: Package as `→⋆ₐ[ℝ]` preserving star/mult/identity
4. **Generator positivity**: Prove `π(gⱼ).IsPositive` for each generator
5. **Vector state formula**: Prove φ(a) = Re⟨Ω, π(a)Ω⟩

This is substantial work - each step requires careful typeclass management.

---

## Known Issues

- **completion-topology.md exceeds 200 LOC** (~271 LOC)
- **LEARNINGS_misc.md exceeds 200 LOC** (316 LOC) - tracked by af-tests-2d6o

---

## Learnings (from this session)

**Inner product lemmas require InnerProductSpace:**
The lemmas `inner_zero_left` and `inner_zero_right` require `InnerProductSpace`,
not just `Inner`. When working with complexification infrastructure split across
files, place theorems requiring the full `InnerProductSpace` instance in files
where it's already defined (e.g., ComplexifyInner.lean after instInnerProductSpace).

**Norm preservation via squared norms:**
To prove `‖embed x‖ = ‖x‖`, use:
```lean
have hsq : ‖embed x‖^2 = ‖x‖^2 := by
  rw [sq, sq, ← inner_self_eq_norm_mul_norm (𝕜 := ℂ), embed_inner]
  have hre : RCLike.re ((⟪x, x⟫_ℝ : ℝ) : ℂ) = ⟪x, x⟫_ℝ := Complex.ofReal_re _
  rw [hre, ← inner_self_eq_norm_mul_norm (𝕜 := ℝ), RCLike.re_to_real]
exact sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp hsq
```

The key is using `inner_self_eq_norm_mul_norm` which says `Re⟪x, x⟫ = ‖x‖ * ‖x‖`.

---

## Files Modified This Session

- `AfTests/ArchimedeanClosure/GNS/ComplexifyInner.lean` (+21 LOC: embed_inner, embed_norm)
- `AfTests/ArchimedeanClosure/GNS/ComplexifyGNS.lean` (+4 LOC: gnsCyclicVectorComplex_norm)
- `HANDOFF.md` (this file)
