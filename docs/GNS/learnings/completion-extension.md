# Completion Extension Patterns

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

## Real vs Complex Hilbert Space Gap

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
