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

## Extension vs Map for Completions

**Discovery:** Mathlib has two ways to extend functions to completions:
- `UniformSpace.Completion.map f` - for `f : α → β` where target is also a completion
- `UniformSpace.Completion.extension f` - for `f : α → β` where target is complete

**Problem:** When extending an isometry `U₀ : A/N_φ → H` to `H_φ → H`, we need
`extension` because `H` is complete but not a completion of something.

**Resolution:** Use `UniformSpace.Completion.extension`:
```lean
noncomputable def gnsIntertwinerFun ... : φ.gnsHilbertSpace → H :=
  UniformSpace.Completion.extension (gnsIntertwinerQuotientFun ...)
```

Key lemmas:
- `extension_coe hf a` - extension agrees on embedded elements (requires `UniformContinuous f`)
- `continuous_extension` - extension is continuous
- `Isometry.completion_extension` - extension of isometry is an isometry

**Lesson:** Use `extension` when the target is a complete space. Use `map` when the
target is itself a completion (e.g., extending `f : α → β` to `Completion α → Completion β`).

---

## Isometry Norm Preservation for Extensions

**Discovery:** `Isometry` in Mathlib is defined in terms of `edist`, not norm. To prove
norm preservation, you need `Isometry.norm_map_of_map_zero`.

**Problem:** When extending a linear isometry to a completion via `Isometry.completion_extension`,
the resulting `Isometry` doesn't directly provide `‖f x‖ = ‖x‖`. The `Isometry` type only
guarantees `edist (f x) (f y) = edist x y`.

**Resolution:** Use `Isometry.norm_map_of_map_zero`:
```lean
theorem Isometry.norm_map_of_map_zero {f : E → F}
    (hf : Isometry f) (h0 : f 0 = 0) (x : E) : ‖f x‖ = ‖x‖
```

For linear maps, `f 0 = 0` is automatic via `LinearMap.map_zero` or `ContinuousLinearMap.map_zero`.

**Lesson:** The isometry → norm preservation chain is:
1. Get `Isometry f` from `LinearIsometry.isometry` or `Isometry.completion_extension`
2. Prove `f 0 = 0` (trivial for linear maps)
3. Apply `Isometry.norm_map_of_map_zero` to get `‖f x‖ = ‖x‖`
