# Handoff: 2026-01-25 (Session 17)

## Completed This Session

### Fixed gnsQuotientNormedSpace Type Error
The `gnsQuotientNormedSpace` definition in `Completion.lean` had a bug: Lean couldn't
synthesize `SeminormedAddCommGroup φ.gnsQuotient` because `NormedSpace` requires it but
`InnerProductSpace.Core.toNormedSpace` provides its own instance internally.

**Fix applied:** Made the return type explicit with @:
```lean
noncomputable def gnsQuotientNormedSpace :
    @NormedSpace ℝ φ.gnsQuotient _ φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup :=
  @InnerProductSpace.Core.toNormedSpace ℝ φ.gnsQuotient _ _ _ φ.gnsPreInnerProductCore
```

### Discovered Extension.lean Was Never Compiling
Attempted to add `gnsRepComplex` to extend the representation to the complexified space.
Discovered that `Extension.lean` has pre-existing compilation errors due to typeclass
resolution failures around `UniformSpace` and `ContinuousLinearMap.uniformContinuous`.

**Root cause:** The explicit @ types in `gnsBoundedPreRep` create ContinuousLinearMaps
with specific topology instances that don't match what `.uniformContinuous` expects.
Calling `(gnsBoundedPreRep a).uniformContinuous` fails because Lean can't unify the
topologies.

**Status:** Extension.lean is blocked and needs more careful typeclass management.

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
| GNS/Completion.lean | Done | 118 | 0 | Fixed type error |
| GNS/Complexify.lean | Done | 193 | 0 | Module + Inner |
| GNS/ComplexifyInner.lean | Done | 160 | 0 | Full InnerProductSpace + embed_norm |
| GNS/ComplexifyGNS.lean | Done | 76 | 0 | Complexified GNS + norm |
| GNS/Bounded.lean | Done | 148 | 0 | Archimedean boundedness |
| GNS/Extension.lean | **BLOCKED** | 101 | 0 | Typeclass issues |

---

## What's Needed for `gns_representation_exists`

The sorry requires constructing a `ConstrainedStarRep` from an M-positive state.

**What we have:**
- Complex Hilbert space: `gnsHilbertSpaceComplex`
- Cyclic vector with unit norm: `gnsCyclicVectorComplex_norm`
- Pre-representation on quotient: `gnsLeftAction`
- Boundedness: `gnsLeftAction_bounded`

**What's blocked:**
1. **gnsBoundedPreRep**: Defined but `.uniformContinuous` fails (typeclass issue)
2. **gnsRep**: Depends on gnsBoundedPreRep_uniformContinuous
3. **Extension to complexification**: Blocked by above

**Next step:** Resolve the typeclass mismatch in `gnsBoundedPreRep_uniformContinuous`.

The issue is that `gnsBoundedPreRep` uses explicit @ with specific topology instances,
but `ContinuousLinearMap.uniformContinuous` expects to synthesize instances via typeclass.

---

## Known Issues

- **completion-topology.md exceeds 200 LOC** (~312 LOC) - needs refactoring
- **LEARNINGS_misc.md exceeds 200 LOC** (316 LOC) - tracked by af-tests-2d6o
- **Extension.lean blocked** - typeclass resolution failures

---

## Learnings (from this session)

### NormedSpace Requires Explicit SeminormedAddCommGroup

When defining `NormedSpace` via `InnerProductSpace.Core.toNormedSpace`, the return type
must use explicit @ to specify which `SeminormedAddCommGroup` to use:

```lean
-- WRONG: Lean can't find SeminormedAddCommGroup
def foo : NormedSpace ℝ X := @InnerProductSpace.Core.toNormedSpace ...

-- RIGHT: Explicit SeminormedAddCommGroup in return type
def foo : @NormedSpace ℝ X _ myNormedAddCommGroup.toSeminormedAddCommGroup :=
  @InnerProductSpace.Core.toNormedSpace ...
```

### Explicit @ Types Break Downstream Methods

When you use explicit @ in a definition's type (like `gnsBoundedPreRep`), calling
methods like `.uniformContinuous` may fail because:
- The method tries to synthesize instances via typeclass resolution
- But your type uses specific instances that aren't in the typeclass system
- Result: "failed to synthesize" errors

**Possible solutions (not yet tested):**
1. Add `haveI`/`letI` to provide the instances before calling the method
2. Use explicit @ calls for the method too (e.g., `@ContinuousLinearMap.uniformContinuous`)
3. Restructure to avoid explicit @ in the type (use attributes/instances instead)

---

## Files Modified This Session

- `AfTests/ArchimedeanClosure/GNS/Completion.lean` (fixed gnsQuotientNormedSpace type)
- `HANDOFF.md` (this file)
