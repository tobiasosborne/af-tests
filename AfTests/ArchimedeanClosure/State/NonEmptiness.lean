/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.ArchimedeanClosure.State.MPositiveState
import Mathlib.Algebra.FreeAlgebra

/-! # Non-emptiness of S_M

This file addresses the non-emptiness of the state space S_M.

## Main definitions

* `scalarExtraction` - Linear functional extracting scalar coefficient

## Mathematical Issue (Critical)

The FreeAlgebra star structure from mathlib does NOT conjugate scalars:
  star (algebraMap c) = algebraMap c  (NOT algebraMap (conj c))

This means for a = algebraMap I (the imaginary unit):
  star a * a = algebraMap (I * I) = algebraMap (-1) ∈ M

But scalarExtraction (algebraMap (-1)) = -1, which has NEGATIVE real part!

This breaks the standard "scalar extraction gives M-positive state" argument.

## Possible Resolutions

1. Work over ℝ: Use FreeAlgebra ℝ (Fin n), extend to ℂ-valued functionals
2. Quotient: Take quotient by star(c·1) = conj(c)·1 relations
3. Axiomatize: Add existence of M-positive states as hypothesis

See LEARNINGS.md for full discussion.
-/

namespace FreeStarAlgebra

variable {n : ℕ}

/-- Scalar extraction: the algebra map inverse, extracting coefficient of 1.

This is `FreeAlgebra.algebraMapInv`, which maps generators to 0 and
extracts the scalar part. Note: This is an AlgHom, hence ℂ-linear. -/
noncomputable def scalarExtraction : FreeStarAlgebra n →ₐ[ℂ] ℂ :=
  FreeAlgebra.algebraMapInv

/-- scalarExtraction as a linear map. -/
noncomputable def scalarExtractionLinear : FreeStarAlgebra n →ₗ[ℂ] ℂ :=
  scalarExtraction.toLinearMap

/-- Scalar extraction maps 1 to 1. -/
@[simp]
theorem scalarExtraction_one : scalarExtraction (1 : FreeStarAlgebra n) = 1 := by
  simp [scalarExtraction, FreeAlgebra.algebraMapInv]

/-- Scalar extraction maps generators to 0. -/
@[simp]
theorem scalarExtraction_generator (j : Fin n) : scalarExtraction (generator j) = 0 := by
  simp only [scalarExtraction, generator, FreeAlgebra.algebraMapInv]
  rw [FreeAlgebra.lift_ι_apply]
  rfl

/-- Scalar extraction extracts the scalar part.

For a = algebraMap c + (terms with generators), we have scalarExtraction a = c. -/
theorem scalarExtraction_algebraMap (c : ℂ) :
    scalarExtraction (algebraMap (R := ℂ) (A := FreeStarAlgebra n) c) = c := by
  exact FreeAlgebra.algebraMap_leftInverse c

/-! ## The Obstacle

The following theorem would be needed for M-positivity, but it FAILS due to
the star structure not conjugating scalars.

For a = algebraMap I, we have:
  star a * a = algebraMap (-1)
  scalarExtraction (star a * a) = -1

So the real part is NEGATIVE, not nonnegative!
-/

/-- BLOCKED: This fails due to star structure not conjugating scalars.

Counter-example: a = algebraMap I gives scalarExtraction (star a * a) = -1.

For this to work, we would need star (c • 1) = conj(c) • 1, but the
FreeAlgebra star structure has star (c • 1) = c • 1. -/
theorem scalarExtraction_star_mul_self_nonneg_BLOCKED (a : FreeStarAlgebra n) :
    0 ≤ (scalarExtraction (star a * a)).re := by
  sorry -- BLOCKED: Counter-example exists, see docstring

/-- S_M is nonempty.

APPROACH NEEDED: The standard scalar extraction approach fails (see above).
Alternative approaches:
1. Restrict to subalgebra where star conjugates properly
2. Use Hahn-Banach/Riesz extension with different base functional
3. Add as hypothesis that n ≥ 1 and use generator-based construction

For now, this is axiomatized pending resolution of the star structure issue. -/
theorem MPositiveStateSet_nonempty : (MPositiveStateSet n).Nonempty := by
  sorry -- BLOCKED: Requires resolution of star structure issue

end FreeStarAlgebra
