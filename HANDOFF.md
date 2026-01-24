# Handoff: GNS Construction Progress

**Date:** 2026-01-24
**Session Focus:** Implemented Main/Uniqueness.lean - GNS intertwiner construction

---

## Completed This Session

1. **Created `AfTests/GNS/Main/Uniqueness.lean`** (123 lines)
   - `gnsIntertwinerQuotientFun` - The intertwiner U₀([a]) = π(a)ξ on the quotient
   - `gnsIntertwinerQuotient_isometry` - Proves ‖U₀([a])‖ = ‖[a]‖
   - `gnsIntertwinerQuotient_cyclic` - Proves U₀([1]) = ξ

2. **Key proof techniques:**
   - Well-definedness via `Quotient.liftOn` with `Submodule.quotientRel_def`
   - Isometry via `inner_self_eq_zero` and `ContinuousLinearMap.adjoint_inner_right`
   - The *-representation star property: π(a)† = π(a*)
   - Using `change` instead of `show` to handle quotient definitional equalities

3. **Updated documentation:**
   - `docs/GNS/phases/06_main.md` - Marked Uniqueness.lean as Proven
   - `docs/GNS/learnings/inner-product-conventions.md` - Added intertwiner technique

---

## Current State

- **Build status:** Passing (zero sorries!)
- **Sorry count:** 0 total in GNS
- **LOC violations:** 0

---

## GNS Progress Summary

| Phase | Files | Proven | Structure Done | Not Started | Progress |
|-------|-------|--------|----------------|-------------|----------|
| P1: States | 4 | 4 | 0 | 0 | **100%** |
| P2: NullSpace | 3 | 3 | 0 | 0 | **100%** |
| P3: PreHilbert | 3 | 3 | 0 | 0 | **100%** |
| P4: HilbertSpace | 2 | 2 | 0 | 0 | **100%** |
| P5: Representation | 4 | 4 | 0 | 0 | **100%** |
| P6: Main | 3 | 2 | 0 | 1 | 67% |
| **TOTAL** | **19** | **18** | **0** | **1** | **95%** |

---

## Remaining Sorries

None! All sorries eliminated in Phases 1-5 and now VectorState + Uniqueness in Phase 6.

---

## Next Steps (Priority Order)

1. **Phase 6** - Final main theorem:
   - `Main/Theorem.lean` - Main GNS theorem bundle (existence statement)

---

## Files Modified This Session

- Created: `AfTests/GNS/Main/Uniqueness.lean` (123 lines)
- Updated: `docs/GNS/phases/06_main.md`
- Updated: `docs/GNS/learnings/inner-product-conventions.md`
- Updated: `HANDOFF.md`

---

## Technical Notes

**Uniqueness Intertwiner Construction:**

Given another cyclic *-representation (H, π, ξ) with ⟨ξ, π(a)ξ⟩ = φ(a):

1. Define U₀ : gnsQuotient → H by U₀([a]) = π(a)ξ
2. Well-defined: [a] = [b] implies a - b ∈ N_φ, so φ((a-b)*(a-b)) = 0,
   hence ‖π(a-b)ξ‖² = ⟨ξ, π((a-b)*(a-b))ξ⟩ = 0
3. Isometric: ‖π(a)ξ‖² = ⟨ξ, π(a*a)ξ⟩ = φ(a*a) = ‖[a]‖²
4. Cyclic: U₀([1]) = π(1)ξ = ξ

The key lemma pattern uses:
- `Submodule.quotientRel_def` to convert a ≈ b to a - b ∈ N_φ
- `inner_self_eq_zero` to reduce π(a-b)ξ = 0 to inner product = 0
- `ContinuousLinearMap.adjoint_inner_right` for the adjoint identity

---

## Commands for Next Session

```bash
bd ready                 # See available work
bd show af-tests-t09     # Review Main/Theorem.lean task
```
