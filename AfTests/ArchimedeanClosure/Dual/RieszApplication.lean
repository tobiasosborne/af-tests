/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.ArchimedeanClosure.Dual.SeparatingFunctional
import AfTests.ArchimedeanClosure.Boundedness.GeneratingCone
import Mathlib.Analysis.Convex.Cone.Extension

/-! # Applying Riesz Extension to Get Separating Functional

This file extends the separating functional from `span{A}` to all of `(A₀)_sa`.

## Main results

* `riesz_extension_exists` - For A ∉ M̄, there exists ψ : (A₀)_sa → ℝ with ψ ≥ 0 on M and ψ(A) < 0

## Mathematical Background

The Riesz Extension Theorem (`riesz_extension` in mathlib) states:
Given a convex cone s and a partial linear map f on domain D with f ≥ 0 on s ∩ D,
if the "generating" condition `∀ y, ∃ x ∈ D, x + y ∈ s` holds, then f extends to
the whole space while preserving nonnegativity on s.

### The Generating Condition Challenge

For our setup:
- Cone s = QuadraticModule n (or its intersection with selfAdjointPart)
- Domain D = Submodule.span ℝ {A}
- We have: ψ₀ ≥ 0 on M ∩ span{A} (from `separatingOnSpan_nonneg_on_M_cap_span`)

The generating condition requires: ∀ y, ∃ c ∈ ℝ, cA + y ∈ M.
This is NOT directly satisfied for a 1-dimensional domain.

### Key Insight: The Generating Property of M

From `quadraticModule_selfAdjoint_generating`:
Every self-adjoint x can be written as x = (1/4)m₁ - (1/4)m₂ for m₁, m₂ ∈ M ∩ (A₀)_sa.

This shows M ∩ (A₀)_sa generates (A₀)_sa as differences, which is related to but
different from mathlib's generating condition.

### Mathematical Resolution

The mathematical argument proceeds:
1. Define ψ₀ on span{A} with ψ₀(A) = -1 < 0
2. M ∩ (A₀)_sa generates (A₀)_sa (our `quadraticModule_selfAdjoint_generating`)
3. Apply the Riesz extension principle (via Zorn's lemma) to extend ψ₀
4. The generating property ensures the extension can be done while preserving M-nonnegativity

The direct application of mathlib's `riesz_extension` requires additional work
to verify the specific generating condition format.

## References

* Schmüdgen, "The Moment Problem" (2017), Chapter 3
* Blekherman, Parrilo, Thomas, "Semidefinite Optimization and Convex Algebraic Geometry"
-/

namespace FreeStarAlgebra

variable {n : ℕ} [IsArchimedean n]

/-! ### Converting separatingOnSpan to a LinearPMap -/

/-- The separating functional as a LinearPMap on the full algebra.
This is the starting point for Riesz extension. -/
noncomputable def separatingPMap {A : FreeStarAlgebra n}
    (hA_not : A ∉ quadraticModuleClosure) :
    (FreeStarAlgebra n) →ₗ.[ℝ] ℝ :=
  ⟨Submodule.span ℝ {A}, separatingOnSpan hA_not⟩

omit [IsArchimedean n] in
theorem separatingPMap_domain {A : FreeStarAlgebra n}
    (hA_not : A ∉ quadraticModuleClosure) :
    (separatingPMap hA_not).domain = Submodule.span ℝ {A} := rfl

omit [IsArchimedean n] in
/-- The separating PMap is nonnegative on M ∩ domain. -/
theorem separatingPMap_nonneg_on_M {A : FreeStarAlgebra n}
    (hA_not : A ∉ quadraticModuleClosure)
    (x : (separatingPMap hA_not).domain)
    (hx : (x : FreeStarAlgebra n) ∈ QuadraticModule n) :
    0 ≤ (separatingPMap hA_not) x := by
  have hx_span : (x : FreeStarAlgebra n) ∈ Submodule.span ℝ {A} := x.property
  exact separatingOnSpan_nonneg_on_M_cap_span hA_not hx hx_span

/-! ### The Main Extension Theorem -/

omit [IsArchimedean n] in
/-- **Key Lemma**: M ∩ (A₀)_sa satisfies a form of the generating condition.

For any y ∈ (A₀)_sa, there exist m ∈ M ∩ (A₀)_sa such that m + y' ∈ M for some y'
related to y. This follows from `quadraticModule_selfAdjoint_generating`. -/
theorem generating_condition_from_decomp {y : FreeStarAlgebra n}
    (hy : IsSelfAdjoint y) :
    ∃ m₁ : FreeStarAlgebra n, m₁ ∈ QuadraticModule n ∧
    ∃ m₂ : FreeStarAlgebra n, m₂ ∈ QuadraticModule n ∧
      IsSelfAdjoint m₁ ∧ IsSelfAdjoint m₂ ∧
      y = (1/4 : ℝ) • m₁ - (1/4 : ℝ) • m₂ := by
  obtain ⟨m₁, ⟨hm₁_M, hm₁_sa⟩, m₂, ⟨hm₂_M, hm₂_sa⟩, h_eq⟩ :=
    quadraticModule_selfAdjoint_generating y hy
  exact ⟨m₁, hm₁_M, m₂, hm₂_M, hm₁_sa, hm₂_sa, h_eq⟩

/-- **Main Extension Theorem**: For A ∉ M̄ (self-adjoint), there exists a linear
functional on the self-adjoint part that is nonnegative on M and negative on A.

This is the core result needed for the backward direction of the dual characterization.
The proof uses the Riesz extension principle combined with:
1. The separating functional `separatingOnSpan` with ψ₀(A) = -1 < 0
2. The generating property of M ∩ (A₀)_sa for (A₀)_sa -/
theorem riesz_extension_exists {A : FreeStarAlgebra n}
    (hA : IsSelfAdjoint A) (hA_not : A ∉ quadraticModuleClosure) :
    ∃ ψ : FreeStarAlgebra n →ₗ[ℝ] ℝ,
      (∀ m ∈ QuadraticModule n, 0 ≤ ψ m) ∧ ψ A < 0 := by
  /-
  Proof sketch:
  1. Start with separatingOnSpan on span{A} where ψ₀(A) = -1 < 0
  2. By `separatingOnSpan_nonneg_on_M_cap_span`, ψ₀ ≥ 0 on M ∩ span{A}
  3. By `quadraticModule_selfAdjoint_generating`, M generates the self-adjoint part
  4. Apply Riesz extension principle to extend ψ₀ to all of FreeStarAlgebra n
  5. The extension maintains ψ ≥ 0 on M and ψ(A) = -1 < 0

  The main technical challenge is verifying the generating condition in the
  specific format required by mathlib's `riesz_extension`. This requires
  showing that for the cone M, the condition `∀ y, ∃ x ∈ domain, x + y ∈ M`
  is satisfied when we consider the full extension process.

  Alternative approach: Use separation theorem for convex cones
  (`ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem`)
  but this requires an inner product space structure.
  -/
  sorry

/-- Corollary: The extended functional preserves the value at A. -/
theorem riesz_extension_apply_A {A : FreeStarAlgebra n}
    (hA : IsSelfAdjoint A) (hA_not : A ∉ quadraticModuleClosure) :
    ∃ ψ : FreeStarAlgebra n →ₗ[ℝ] ℝ,
      (∀ m ∈ QuadraticModule n, 0 ≤ ψ m) ∧
      ψ A = separatingOnSpan hA_not ⟨A, Submodule.mem_span_singleton_self A⟩ := by
  obtain ⟨ψ, hψ_nonneg, hψ_A_neg⟩ := riesz_extension_exists hA hA_not
  refine ⟨ψ, hψ_nonneg, ?_⟩
  -- The extension should agree with ψ₀ on span{A}
  -- This is guaranteed by the Riesz extension theorem
  sorry

end FreeStarAlgebra
