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

---

## Isometry Surjectivity from Dense Range

**Discovery:** An isometry from a complete space with dense range is surjective. This is
a general topological fact that doesn't seem to be in Mathlib directly.

**Problem:** For GNS uniqueness, we need `gnsIntertwiner : H_φ → H` to be surjective.
We have that it's an isometry with dense range.

**Resolution:** The proof chain uses these Mathlib lemmas:
1. `Isometry.isUniformInducing` - isometry is uniform inducing
2. `IsUniformInducing.isComplete_range [CompleteSpace α]` - range of uniform inducing from complete space is complete
3. `IsComplete.isClosed [T0Space]` - complete sets are closed in T0 spaces
4. `dense_iff_closure_eq` - dense means closure = univ
5. `IsClosed.closure_eq` - closed set equals its closure
6. `Set.range_eq_univ` - range = univ iff surjective

Combined proof (compact form):
```lean
theorem Isometry.surjective_of_completeSpace_denseRange
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace X] [CompleteSpace Y]
    {f : X → Y} (hf : Isometry f) (hd : DenseRange f) : Function.Surjective f :=
  Set.range_eq_univ.mp <| hf.isUniformInducing.isComplete_range.isClosed.closure_eq ▸
    dense_iff_closure_eq.mp hd
```

**Lesson:** Isometry surjectivity follows from: complete source → complete range → closed range.
Dense + closed = whole space. The key insight is that `IsUniformInducing` preserves completeness.

---

## Real vs Complex Hilbert Space Gap (Architectural Issue)

**Discovery:** The GNS construction produces a REAL Hilbert space, but `ConstrainedStarRep`
expects a COMPLEX Hilbert space.

**Problem:** The chain of types:
1. `MPositiveState n` has `toLinearMap : FreeStarAlgebra n →ₗ[ℝ] ℝ` (maps to ℝ)
2. Inner product `⟨[a], [b]⟩ = φ(star b * a)` is ℝ-valued
3. `InnerProductSpace.Core ℝ gnsQuotient` is over ℝ
4. Completion gives `InnerProductSpace ℝ gnsHilbertSpaceReal`

But `ConstrainedStarRep.instInnerProductSpace : InnerProductSpace ℂ H` requires complex!

**Resolution Options:**
1. **Complexify the Hilbert space**: H_ℂ = H_ℝ ⊗ ℂ with standard complexification structure
2. **Change MPositiveState**: Make φ : A₀ → ℂ with Im = 0 (effectively still ℝ, but compatible)
3. **Modify ConstrainedStarRep**: Allow real Hilbert spaces (changes the theorem statement)

Mathlib doesn't have direct "complexify real Hilbert space" support. Manual construction:
- H_ℂ = H_ℝ × H_ℝ as sets
- (a + bi)·(x, y) = (ax - by, ay + bx)
- ⟪(x₁, y₁), (x₂, y₂)⟫_ℂ = ⟪x₁, x₂⟫_ℝ + ⟪y₁, y₂⟫_ℝ + i(⟪x₁, y₂⟫_ℝ - ⟪y₁, x₂⟫_ℝ)

**Lesson:** When designing algebraic structures for representation theory, decide early
whether to work over ℝ or ℂ. The current architecture chose ℝ for MPositiveState
(to ensure φ(c*c) ≥ 0 for scalars), but this creates friction with complex Hilbert spaces.

---

## Proving Norm from InnerProductSpace.Core

**Discovery:** When you have a custom `InnerProductSpace.Core` (or `PreInnerProductSpace.Core`)
and want to prove `‖x‖ = 1` for a specific element, you need to carefully match norm instances.

**Problem:** The goal `‖x‖ = 1` may use a different norm instance than the one from your Core.
Direct rewriting with `InnerProductSpace.Core.norm_eq_sqrt_re_inner` may not work.

**Resolution:** Explicitly construct the chain:
```lean
-- Get the Core norm = sqrt(re⟨x,x⟩) equation
have h := @InnerProductSpace.Core.norm_eq_sqrt_re_inner ℝ E _ _ _
    myPreInnerProductCore x
-- Show the Core inner equals your custom inner
have h_inner : @inner ℝ _ myCore.toInner x x = myCustomInner x x := rfl
-- Then rewrite
rw [h, h_inner, RCLike.re_to_real, ...]
```

For ℝ, `RCLike.re_to_real` simplifies `re : ℝ → ℝ` to identity.

**Lesson:** When norms come from parametric Core instances (like `φ.gnsInnerProductCore`),
use explicit `@` application and connect inner products explicitly via `rfl` proofs.

---

## Complexification Implementation (Started)

**Discovery:** Building complexification requires careful handling of definitional equality
between `Complexification H` (a type alias) and `H × H` (the underlying type).

**Problem:** When defining `embed : H → Complexification H` as `x ↦ (x, 0)`, the addition
`embed x + embed y` uses the `AddCommGroup (Complexification H)` instance which is
`inferInstanceAs (AddCommGroup (H × H))`. Simp lemmas like `Prod.mk_add_mk` may not fire
directly because the types don't match syntactically.

**Resolution:** Use `change` to convert the goal to the underlying product type:
```lean
theorem embed_add (x y : H) : embed (x + y) = embed x + embed y := by
  change (x + y, (0 : H)) = (x, 0) + (y, 0)
  simp only [Prod.mk_add_mk, add_zero]
```

**Progress (2026-01-25): COMPLEXIFICATION COMPLETE!**
- ✅ `Module ℂ (Complexification H)` instance (Complexify.lean)
- ✅ `Inner ℂ (Complexification H)` instance (Complexify.lean)
- ✅ All 5 axioms proven (ComplexifyInner.lean)
- ✅ `InnerProductSpace.Core ℂ (Complexification H)` instance
- ✅ `NormedAddCommGroup (Complexification H)` instance
- ✅ `InnerProductSpace ℂ (Complexification H)` instance

**Complexification is now a complex Hilbert space!**

**Key techniques:**
- The `module` tactic solves goals involving module scalar multiplication that `ring` cannot.
- Use `Complex.ext` for equality of complex numbers (not generic `ext`).
- `InnerProductSpace.Core.smul_left` expects `(x y : F) (r : 𝕜)` order - use lambda wrapper
  if your theorem has `(r : 𝕜) (x y : F)` order: `smul_left := fun p q c => inner_smul_left' c p q`
- When using `InnerProductSpace.Core.toNormedAddCommGroup` and `InnerProductSpace.ofCore`,
  use explicit `@` to avoid typeclass resolution getting stuck on metavariables:
  `@InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ instInnerProductSpaceCore`
- Use `real_inner_self_nonneg` (not `inner_self_nonneg`) when the goal is `0 ≤ ⟪x, x⟫_ℝ`.
  The generic `inner_self_nonneg` returns `0 ≤ RCLike.re ⟪x, x⟫_𝕜` which doesn't unify.
- `real_inner_comm` is the mathlib lemma for real inner product symmetry.
- `inner_add_left (𝕜 := ℝ)` explicitly selects the real inner product version.
- `add_eq_zero_iff_of_nonneg` is useful for "sum of nonneg = 0 implies each = 0".
- `inner_self_eq_zero (𝕜 := ℝ)` gives the iff for real inner product definiteness.

**Lesson:** When creating type aliases that inherit instances via `inferInstanceAs`,
use `change` or explicit type annotations to help simp lemmas recognize the structure.

---

## ContinuousLinearMap Requires Explicit Instance Selection (2026-01-25)

**Discovery:** When wrapping a LinearMap in `LinearMap.mkContinuous` to create a
`ContinuousLinearMap`, Lean cannot synthesize the required `TopologicalSpace` instance
because multiple incompatible sources exist.

**Problem:** The GNS quotient `A₀/N_φ` has:
1. A quotient module topology (from `Submodule.Quotient`)
2. A seminormed topology (from `InnerProductSpace.Core.toNormedAddCommGroup`)

When you write `φ.gnsQuotient →L[ℝ] φ.gnsQuotient`, Lean needs `TopologicalSpace φ.gnsQuotient`
but finds conflicting instances. Error: "failed to synthesize TopologicalSpace φ.gnsQuotient"

**Attempted Resolution:** Use explicit `@` syntax like the original GNS code:
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

All instances must derive from the same root (gnsQuotientNormedAddCommGroup) for consistency.

**Additional Complication:** `InnerProductSpace` expects `SeminormedAddCommGroup`, but we have
`NormedAddCommGroup`. Need to use `.toSeminormedAddCommGroup` conversions throughout.

**Current Status:** The original C*-algebra GNS (AfTests/GNS/Representation/Extension.lean)
handles this with ~20 lines of explicit @ syntax. Adapting this for the real-valued
ArchimedeanClosure GNS requires similar careful instance management.

**Lesson:** When building ContinuousLinearMaps on quotient spaces with induced norms:
1. Identify ALL instances that ContinuousLinearMap requires (TopologicalSpace, AddCommMonoid, Module)
2. Derive them ALL from the same root instance (e.g., gnsQuotientNormedAddCommGroup)
3. Use explicit `@` application with full instance specification
4. The pattern from the original GNS Extension.lean is the correct template
