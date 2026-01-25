# GNS Completion Learnings

## Complexification Implementation (Complete)

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

**Status (2026-01-25): COMPLEXIFICATION COMPLETE!**
- ✅ `Module ℂ (Complexification H)` instance
- ✅ `Inner ℂ (Complexification H)` instance
- ✅ All 5 axioms proven
- ✅ `InnerProductSpace.Core ℂ (Complexification H)` instance
- ✅ `NormedAddCommGroup (Complexification H)` instance
- ✅ `InnerProductSpace ℂ (Complexification H)` instance

**Key techniques:**
- The `module` tactic solves goals involving module scalar multiplication that `ring` cannot.
- Use `Complex.ext` for equality of complex numbers (not generic `ext`).
- `InnerProductSpace.Core.smul_left` expects `(x y : F) (r : 𝕜)` order - use lambda wrapper
  if your theorem has `(r : 𝕜) (x y : F)` order: `smul_left := fun p q c => inner_smul_left' c p q`
- When using `InnerProductSpace.Core.toNormedAddCommGroup` and `InnerProductSpace.ofCore`,
  use explicit `@` to avoid typeclass resolution getting stuck on metavariables
- Use `real_inner_self_nonneg` (not `inner_self_nonneg`) when the goal is `0 ≤ ⟪x, x⟫_ℝ`
- `real_inner_comm` is the mathlib lemma for real inner product symmetry
- `inner_add_left (𝕜 := ℝ)` explicitly selects the real inner product version
- `add_eq_zero_iff_of_nonneg` is useful for "sum of nonneg = 0 implies each = 0"
- `inner_self_eq_zero (𝕜 := ℝ)` gives the iff for real inner product definiteness

**Lesson:** When creating type aliases that inherit instances via `inferInstanceAs`,
use `change` or explicit type annotations to help simp lemmas recognize the structure.

---

## Complexification Norm Identity

**Discovery:** To prove continuity of `mapComplex T` for a CLM `T`, need `‖(x,y)‖² = ‖x‖² + ‖y‖²`.

**Problem:** The norm on `Complexification H` comes from `InnerProductSpace.Core.toNormedAddCommGroup`.
Relating it back to component norms requires explicit instance specification.

**Resolution:**
```lean
private theorem complexification_norm_sq (p : Complexification H) :
    ‖p‖^2 = ‖p.1‖^2 + ‖p.2‖^2 := by
  rw [@norm_sq_eq_re_inner ℂ (Complexification H) _
      Complexification.instNormedAddCommGroup.toSeminormedAddCommGroup
      Complexification.instInnerProductSpace]
  rw [RCLike.re_eq_complex_re]  -- Convert RCLike.re to Complex.re
  rw [Complexification.inner_re, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
```

Key: `RCLike.re_eq_complex_re` bridges `RCLike.re (inner ℂ p p)` to `(⟪p, p⟫_ℂ).re`.

**Lesson:** When dealing with norms from InnerProductSpace.Core:
1. Use `norm_sq_eq_re_inner` with explicit instances
2. Convert between `RCLike.re` and field accessor `.re` using `RCLike.re_eq_complex_re`

---

## Star Property on Real GNS Representation

**Discovery:** The star property `gnsRep (star a) = adjoint (gnsRep a)` can be proven
on the real Hilbert space using `ContinuousLinearMap.eq_adjoint_iff` and density.

**Key Identity:**
```lean
theorem gnsPreRep_inner_star (a b c : FreeStarAlgebra n) :
    φ.gnsInner (φ.gnsPreRep (star a) (Submodule.Quotient.mk b)) (Submodule.Quotient.mk c) =
    φ.gnsInner (Submodule.Quotient.mk b) (φ.gnsPreRep a (Submodule.Quotient.mk c))
```

The proof is just: `simp only [gnsPreRep_mk, gnsInner_mk, star_mul, mul_assoc]`

This works because:
- LHS = φ(star(c) * star(a) * b) (star anti-homomorphism)
- RHS = φ(star(a*c) * b) = φ(star(c) * star(a) * b) (same by star anti-hom)

**Pattern for Extension:**
```lean
theorem gnsRep_star (a : FreeStarAlgebra n) :
    φ.gnsRep (star a) = ContinuousLinearMap.adjoint (φ.gnsRep a) := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => -- closedness via continuous_inner.comp
  | ih qb qc => -- use gnsPreRep_inner_star after extracting representatives
```

**Lesson:** The adjoint characterization `⟪Ax, y⟫ = ⟪x, By⟫` + density pattern
works well for extending star properties from quotient to completion.

---

## Generator Positivity: Key Insight

**Discovery:** The GNS representation maps generators to positive operators because of
M-positivity and the structure of the quadratic module.

**Key Identity (Proven):**
```lean
theorem gnsPreRep_generator_inner (j : Fin n) (b : FreeStarAlgebra n) :
    φ.gnsInner (Submodule.Quotient.mk b)
      (φ.gnsPreRep (generator j) (Submodule.Quotient.mk b)) =
    φ (star b * generator j * b)
```

**Why It's Nonnegative:**
1. `star b * gⱼ * b ∈ M` by the `star_generator_mul_mem` constructor in QuadraticModule
2. φ is M-positive: `φ(m) ≥ 0` for all `m ∈ M`
3. Therefore `φ(star b * gⱼ * b) ≥ 0`

**Proof Pattern:**
```lean
theorem gnsPreRep_generator_inner_nonneg (j : Fin n) (b : FreeStarAlgebra n) :
    0 ≤ φ.gnsInner (Submodule.Quotient.mk b)
      (φ.gnsPreRep (generator j) (Submodule.Quotient.mk b)) := by
  rw [gnsPreRep_generator_inner]
  exact φ.apply_m_nonneg (star_generator_mul_mem j b)
```

**Extension to Hilbert Space (COMPLETED):**
```lean
theorem gnsRep_generator_inner_nonneg (j : Fin n) (x : φ.gnsHilbertSpaceReal) :
    0 ≤ @inner ℝ _ _ x (φ.gnsRep (generator j) x) := by
  letI seminorm : SeminormedAddCommGroup φ.gnsQuotient := ...
  letI ips : InnerProductSpace ℝ φ.gnsQuotient :=
    @InnerProductSpace.ofCore ℝ _ _ _ _ φ.gnsInnerProductCore.toCore
  induction x using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_le continuous_const (Continuous.inner ...)
  | ih y => rw [gnsRep_coe, inner_coe, inner_eq_gnsInner, ...]; exact ...
```

**Critical Pattern: InnerProductSpace.ofCore for inner_coe**

To use `UniformSpace.Completion.inner_coe`, you need `InnerProductSpace 𝕜 E` on the
pre-completion space. If you only have `InnerProductSpace.Core`, convert it:

```lean
letI ips : InnerProductSpace ℝ φ.gnsQuotient :=
  @InnerProductSpace.ofCore ℝ _ _ _ _ φ.gnsInnerProductCore.toCore
```

**Lesson:** The quadratic module `M` was designed exactly to make generators map to
positive operators. The `star_generator_mul_mem` constructor is the algebraic reason
why constrained representations work.
