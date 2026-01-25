# Completion and Topology Learnings

Technical discoveries related to extending maps to completions and typeclass diamonds.

---

## Extending ContinuousLinearMap to Completion

**Discovery:** Mathlib doesn't have a `ContinuousLinearMap.completion` in the current version.
Must construct the extension manually using `UniformSpace.Completion.map` and prove linearity.

**Problem:** To extend `π_φ(a) : A/N_φ →L[ℂ] A/N_φ` to the Hilbert space completion, we need
to show the extended function is still a ContinuousLinearMap.

**Resolution:** Constructed manually:
1. Use `UniformSpace.Completion.map f` for the underlying function
2. Prove `map_add'` and `map_smul'` using `UniformSpace.Completion.induction_on₂`
3. Prove continuity via `UniformSpace.Completion.continuous_map`
4. Package into a `ContinuousLinearMap` structure

Key lemmas used:
- `UniformSpace.Completion.map_coe huc` - map agrees on dense subspace
- `UniformSpace.Completion.coe_add`, `coe_smul` - embedding preserves operations
- `UniformSpace.Completion.induction_on₂` with `| hp => isClosed_eq ...` pattern

**Lesson:** When extending to completions, use the induction principle with explicit
closedness proofs. The pattern `| hp => isClosed_eq <cont1> <cont2>` handles the
closure condition, then `| ih x => ...` proves the property on the dense subspace.

---

## Typeclass Diamond in GNS Quotient Topology

**Discovery:** The GNS quotient `A/N_φ` has two incompatible TopologicalSpace instances:
- `QuotientModule.Quotient.topologicalSpace` (from quotient construction)
- `PseudoMetricSpace.toUniformSpace.toTopologicalSpace` (from seminormed structure)

**Problem:** When defining `gnsPreRepContinuous`, Lean picks the quotient topology
but `LinearMap.mkContinuous` expects the seminormed topology. Type mismatch error.

**Resolution:** Use explicit `@` syntax to specify the correct topology:
```lean
noncomputable def gnsPreRepContinuous (a : A) :
    @ContinuousLinearMap ℂ ℂ _ _ (RingHom.id ℂ) φ.gnsQuotient
      (@UniformSpace.toTopologicalSpace _ φ.gnsQuotientSeminormedAddCommGroup.toUniformSpace)
      ...
```

Similarly for `gnsPreRepContinuous_uniformContinuous`:
```lean
@UniformContinuous _ _ φ.gnsQuotientSeminormedAddCommGroup.toUniformSpace
    φ.gnsQuotientSeminormedAddCommGroup.toUniformSpace (φ.gnsPreRepContinuous a)
```

**Lesson:** When quotients carry both algebraic and metric structures, the topologies
may differ. Use explicit `@` application with the correct instance to avoid ambiguity.

---

## Dense Range via Set Equality (Avoiding Continuity Requirements)

**Discovery:** `DenseRange.comp` requires continuity of the outer function, which can
trigger the topology diamond issue. However, for surjective inner functions, we can
avoid this entirely.

**Problem:** To show `DenseRange (coe' ∘ Submodule.Quotient.mk)` using `DenseRange.comp`
requires `Continuous coe'` with matching topologies. The quotient topology doesn't match.

**Resolution:** Instead of using `DenseRange.comp`, prove set equality directly:

```lean
have h_range_eq : Set.range (f ∘ g) = Set.range f := by
  ext x
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨g a, ha⟩
  · rintro ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := surjective_g b
    exact ⟨a, hb⟩
rw [DenseRange, h_range_eq]
exact denseRange_f
```

When `g` is surjective, `Set.range (f ∘ g) = Set.range f`. This avoids all
continuity considerations.

**Lesson:** When composing a function with a surjective map, prove `DenseRange` via
set equality rather than `DenseRange.comp`. This sidesteps topology issues entirely.

---

## ContinuousLinearMap Requires Explicit Instance Selection

**Discovery:** When wrapping a LinearMap in `LinearMap.mkContinuous` to create a
`ContinuousLinearMap`, Lean cannot synthesize the required `TopologicalSpace` instance
because multiple incompatible sources exist.

**Problem:** The GNS quotient `A₀/N_φ` has:
1. A quotient module topology (from `Submodule.Quotient`)
2. A seminormed topology (from `InnerProductSpace.Core.toNormedAddCommGroup`)

When you write `φ.gnsQuotient →L[ℝ] φ.gnsQuotient`, Lean needs `TopologicalSpace φ.gnsQuotient`
but finds conflicting instances. Error: "failed to synthesize TopologicalSpace φ.gnsQuotient"

**Resolution:** Use explicit `@` syntax:
```lean
noncomputable def gnsBoundedPreRep (a : FreeStarAlgebra n) :
    @ContinuousLinearMap ℝ ℝ _ _ (RingHom.id ℝ) φ.gnsQuotient
      φ.gnsQuotientNormedAddCommGroup.toUniformSpace.toTopologicalSpace
      ... -- many more explicit instances
```

This requires explicitly specifying:
- The TopologicalSpace (from the normed structure)
- The AddCommMonoid (from the normed structure's AddCommGroup)
- The Module instance (from NormedSpace.toModule)

**Lesson:** When building ContinuousLinearMaps on quotient spaces with induced norms:
1. Identify ALL instances that ContinuousLinearMap requires
2. Derive them ALL from the same root instance
3. Use explicit `@` application with full instance specification

---

## Solution: letI with SeminormedAddCommGroup

**Discovery:** When calling methods like `.uniformContinuous` on a `ContinuousLinearMap`
that was defined with explicit `@` instances, Lean fails to synthesize `UniformSpace`
and `IsUniformAddGroup` via normal typeclass resolution.

**Problem:** The definition `gnsBoundedPreRep` uses explicit @ to select the seminormed
topology. But calling `(φ.gnsBoundedPreRep a).uniformContinuous` fails with:
```
failed to synthesize UniformSpace φ.gnsQuotient
failed to synthesize IsUniformAddGroup φ.gnsQuotient
```

**Resolution:** Use `letI` to establish `SeminormedAddCommGroup` before method calls:
```lean
theorem gnsBoundedPreRep_uniformContinuous (a : FreeStarAlgebra n) :
    @UniformContinuous _ _ φ.gnsQuotientNormedAddCommGroup.toUniformSpace
      φ.gnsQuotientNormedAddCommGroup.toUniformSpace (φ.gnsBoundedPreRep a) := by
  letI : SeminormedAddCommGroup φ.gnsQuotient :=
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
  exact (φ.gnsBoundedPreRep a).uniformContinuous
```

The `SeminormedAddCommGroup` instance brings:
- `UniformSpace` (from `PseudoMetricSpace`)
- `IsUniformAddGroup` (from `SeminormedAddCommGroup.to_isUniformAddGroup`)

**Key insight:** `letI` makes instances available to typeclass synthesis within its scope.
This bridges the gap between explicit @ types and method calls that use synthesis.

**Lesson:** When you have explicit @ types that don't match synthesis expectations:
1. Use `letI` to establish the needed instances in scope
2. Prefer `SeminormedAddCommGroup` over `UniformSpace` alone - it brings more instances
3. This pattern is simpler than using explicit @ for every method call
