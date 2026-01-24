/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.GNS.Representation.PreRep
import AfTests.GNS.HilbertSpace.Completion
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# GNS Representation Boundedness

This file proves the pre-representation is bounded with ‖π(a)‖ ≤ ‖a‖.

## Main results

* `State.gnsPreRep_norm_le` - ‖π(a)x‖ ≤ ‖a‖ * ‖x‖

## Mathematical Background

The key inequality: In C*-algebras, a*a ≤ ‖a‖² · 1 (from spectral theory).
Using positivity of states, this gives the operator norm bound.

## Status

Structure complete. The key sorry in `gnsPreRep_norm_le` requires proving
that states respect the spectral ordering on positive elements.
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)

/-! ### Boundedness of the pre-representation -/

/-- The norm squared on the quotient equals the inner product with itself. -/
theorem gnsQuotient_norm_sq (x : φ.gnsQuotient) :
    ‖x‖ * ‖x‖ = (φ.gnsInner x x).re := by
  have h := @InnerProductSpace.norm_sq_eq_re_inner ℂ _ _ _ φ.gnsQuotientInnerProductSpace x
  simp only [sq] at h
  convert h using 1

/-- Key boundedness lemma: ‖π(a)x‖ ≤ ‖a‖ * ‖x‖.

    Proof strategy:
    1. ‖[ab]‖² = φ((ab)*(ab)) = φ(b* a* a b)
    2. By `CStarAlgebra.star_mul_le_algebraMap_norm_sq`: a*a ≤ ‖a‖² · 1
    3. By `conjugate_le_conjugate`: b*(a*a)b ≤ ‖a‖² · b*b
    4. States preserve this ordering (key step requiring proof)
    5. Hence: ‖[ab]‖² ≤ ‖a‖² · ‖[b]‖²

    The main sorry is in step 4: showing states respect the spectral ordering.
    This requires proving that for x ≤ y in the spectral order,
    (φ x).re ≤ (φ y).re. While states map a*a to non-negative reals,
    extending this to the full positive cone requires additional work.
-/
theorem gnsPreRep_norm_le (a : A) (x : φ.gnsQuotient) :
    ‖φ.gnsPreRep a x‖ ≤ ‖a‖ * ‖x‖ := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal x
  rw [gnsPreRep_mk]
  by_cases ha : a = 0
  · simp [ha]
  · -- Main case: a ≠ 0
    -- Express norms via inner products
    have h_lhs : ‖(Submodule.Quotient.mk (a * b) : φ.gnsQuotient)‖ *
        ‖(Submodule.Quotient.mk (a * b) : φ.gnsQuotient)‖ =
        (φ (star (a * b) * (a * b))).re := by
      rw [gnsQuotient_norm_sq, gnsInner_mk]
    have h_rhs : ‖(Submodule.Quotient.mk b : φ.gnsQuotient)‖ *
        ‖(Submodule.Quotient.mk b : φ.gnsQuotient)‖ = (φ (star b * b)).re := by
      rw [gnsQuotient_norm_sq, gnsInner_mk]
    -- Expand (ab)*(ab) = b* a* a b
    have h_expand : star (a * b) * (a * b) = star b * (star a * a) * b := by
      simp only [star_mul, mul_assoc]
    -- Key inequality: φ(b* a* a b).re ≤ ‖a‖² · φ(b* b).re
    -- Requires: states respect spectral ordering
    sorry

end State
