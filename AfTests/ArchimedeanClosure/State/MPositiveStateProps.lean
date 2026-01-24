/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.ArchimedeanClosure.State.MPositiveState
import Mathlib.Data.Complex.Basic

/-! # Properties of M-Positive States

This file proves additional properties of M-positive states.

## Main results

* `MPositiveState.apply_real_of_isSelfAdjoint` - φ(a) is real when a is self-adjoint
* `MPositiveState.map_star` - Conjugate symmetry: φ(a*) = conj(φ(a))

## Implementation Notes

The conjugate symmetry property requires careful treatment due to the star structure
on FreeAlgebra ℂ (Fin n). See LEARNINGS.md for discussion of star structure issues.
-/

namespace FreeStarAlgebra

variable {n : ℕ}

namespace MPositiveState

variable (φ : MPositiveState n)

/-- φ(star a * a) is real (imaginary part is zero). -/
theorem apply_star_mul_self_real (a : FreeStarAlgebra n) :
    (φ (star a * a)).im = 0 :=
  φ.apply_m_real (star_mul_self_mem a)

/-- φ(a) is real when a is self-adjoint.

For self-adjoint a, we use that a can be written as differences of squares
(polarization), and elements of M map to reals. -/
theorem apply_real_of_isSelfAdjoint {a : FreeStarAlgebra n}
    (ha : IsSelfAdjoint a) : (φ a).im = 0 := by
  -- TODO: This requires showing self-adjoint elements can be expressed
  -- via M elements. The standard approach uses:
  -- a = 1/4 * (1+a)*(1+a) - 1/4 * (1-a)*(1-a) for self-adjoint a
  -- But we need to verify this identity in FreeStarAlgebra.
  sorry

/-- Conjugate symmetry: φ(star a) = conj(φ(a)).

This is the standard property of states on *-algebras. The proof uses
polarization of the positivity condition. -/
theorem map_star (a : FreeStarAlgebra n) :
    φ (star a) = starRingEnd ℂ (φ a) := by
  -- TODO: Standard proof uses polarization:
  -- From φ((a + λb)*(a + λb)) ≥ 0 for all λ ∈ ℂ,
  -- derive φ(b*a) = conj(φ(a*b)), then set b = 1.
  -- This requires careful handling of the FreeAlgebra star structure.
  sorry

/-- Consequence of conjugate symmetry: φ(star a) + φ(a) is real. -/
theorem apply_add_star_real (a : FreeStarAlgebra n) :
    (φ (star a) + φ a).im = 0 := by
  rw [map_star]
  simp [Complex.add_im, Complex.conj_im]

end MPositiveState

end FreeStarAlgebra
