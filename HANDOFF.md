# Handoff: 2026-01-25 (Session 18, Part 2)

## Completed This Session

### Added gnsRep Algebraic Properties

Added key theorems to PreRep.lean and Extension.lean:

**PreRep.lean:**
- `gnsPreRep_add` - Pre-representation is additive in algebra element
- `gnsPreRep_mul` - Pre-representation preserves multiplication
- `gnsPreRep_one` - Pre-representation sends 1 to id

**Extension.lean:**
- `gnsRep_coe` - gnsRep agrees with gnsBoundedPreRep on embedded quotient
- `gnsRep_add` - Representation is additive (uses completion induction)
- `gnsRep_one` - Representation sends 1 to identity

### Fixed Extension.lean Typeclass Resolution (earlier)

**Problem:** `gnsBoundedPreRep_uniformContinuous` and `gnsRep` failed to compile with errors:
- "failed to synthesize UniformSpace φ.gnsQuotient"
- "failed to synthesize IsUniformAddGroup φ.gnsQuotient"

**Root cause:** The `gnsBoundedPreRep` definition uses explicit `@` instances to resolve
the topology diamond. But when calling `.uniformContinuous` as a method, Lean uses normal
typeclass synthesis which doesn't see those explicit instances.

**Solution:** Use `letI` to establish `SeminormedAddCommGroup` before calling methods:
```lean
letI : SeminormedAddCommGroup φ.gnsQuotient :=
  φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
exact (φ.gnsBoundedPreRep a).uniformContinuous
```

This works because `SeminormedAddCommGroup` brings:
- `UniformSpace` (via `PseudoMetricSpace`)
- `IsUniformAddGroup` (via `SeminormedAddCommGroup.to_isUniformAddGroup`)

**Extension.lean now compiles with 0 errors.**

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
| GNS/Completion.lean | Done | 118 | 0 | |
| GNS/Complexify.lean | Done | 193 | 0 | Module + Inner |
| GNS/ComplexifyInner.lean | Done | 160 | 0 | Full InnerProductSpace |
| GNS/ComplexifyGNS.lean | Done | 76 | 0 | Complexified GNS + norm |
| GNS/Bounded.lean | Done | 148 | 0 | Archimedean boundedness |
| GNS/Extension.lean | **FIXED** | 109 | 0 | `gnsRep` now compiles |

---

## What's Needed for `gns_representation_exists`

The sorry requires constructing a `ConstrainedStarRep` from an M-positive state.

**What we have (now working):**
- Complex Hilbert space: `gnsHilbertSpaceComplex`
- Cyclic vector with unit norm: `gnsCyclicVectorComplex_norm`
- Pre-representation on quotient: `gnsLeftAction`
- Boundedness: `gnsLeftAction_bounded`
- **Bounded pre-rep as CLM: `gnsBoundedPreRep`** ✓ Fixed
- **Extension to completion: `gnsRep`** ✓ Fixed
- **Additivity: `gnsRep_add`** ✓ NEW
- **Unit: `gnsRep_one`** ✓ NEW

**What's still needed:**
1. Prove `gnsRep_mul` - multiplicativity (needs completion induction pattern)
2. Extend `gnsRep` (real) to the complexified Hilbert space
3. Prove generator positivity constraint
4. Package into `ConstrainedStarRep` structure

---

## Known Issues

- **completion-topology.md exceeds 200 LOC** (~352 LOC) - tracked by af-tests-8oaj
- **LEARNINGS_misc.md exceeds 200 LOC** (316 LOC) - tracked by af-tests-2d6o

---

## Learnings (from this session)

### letI Bridges Explicit @ Types and Method Calls

When a definition uses explicit `@` instances but methods use typeclass synthesis:
```lean
-- Definition uses explicit @
def foo : @ContinuousLinearMap ... := ...

-- Method call fails: can't synthesize instances
(foo).uniformContinuous  -- ERROR

-- Solution: letI establishes instances for synthesis
letI : SeminormedAddCommGroup X := ...
(foo).uniformContinuous  -- Works!
```

**Key insight:** `SeminormedAddCommGroup` is better than just `UniformSpace` because
it brings `IsUniformAddGroup` with it (via the instance `SeminormedAddCommGroup.to_isUniformAddGroup`).

---

## Files Modified This Session

- `AfTests/ArchimedeanClosure/GNS/Extension.lean` (fixed typeclass resolution)
- `docs/GNS/learnings/completion-topology.md` (added solution section)
- `HANDOFF.md` (this file)
