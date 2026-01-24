/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.GNS.State.Positivity
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Cauchy-Schwarz Inequality for States

This file proves the Cauchy-Schwarz inequality for states on C*-algebras.

## Main results

* `State.inner_mul_le_norm_mul_norm` - |φ(b*a)|² ≤ φ(a*a) · φ(b*b)

## Proof strategy

The proof uses the standard quadratic discriminant argument:

1. **Quadratic setup**: For t : ℝ, expand φ((a + t·b)*(a + t·b)) ≥ 0
   This gives: φ(a*a) + 2t·Re(φ(b*a)) + t²·φ(b*b) ≥ 0

2. **Discriminant bound**: By `discrim_le_zero`, since the quadratic is ≥ 0 for all t:
   (2·Re(φ(b*a)))² - 4·φ(a*a)·φ(b*b) ≤ 0
   Hence: Re(φ(b*a))² ≤ φ(a*a)·φ(b*b)

3. **Imaginary part**: Apply same argument to (a + it·b) to get:
   Im(φ(b*a))² ≤ φ(a*a)·φ(b*b)

4. **Combine**: |φ(b*a)|² = Re² + Im² ≤ φ(a*a)·φ(b*b) + φ(a*a)·φ(b*b)

Note: Step 4 gives a factor of 2. The tight bound requires the complex
discriminant argument using λ ∈ ℂ and setting λ = -conj(φ(b*a))/φ(b*b).
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)

/-! ### Cauchy-Schwarz inequality -/

/-- The Cauchy-Schwarz inequality for states (weak form with factor 2):
    |φ(b*a)|² ≤ 2 · φ(a*a) · φ(b*b).

    This is sufficient for proving the null space is closed under addition. -/
theorem inner_mul_le_norm_mul_norm_weak (a b : A) :
    Complex.normSq (φ (star b * a)) ≤ 2 * (φ (star a * a)).re * (φ (star b * b)).re := by
  -- The proof uses discriminant analysis on the quadratic:
  -- φ(star b * b).re · t² + 2·Re(φ(star b * a)) · t + φ(star a * a).re ≥ 0
  --
  -- By discrim_le_zero: Re(φ(star b * a))² ≤ φ(star a * a).re · φ(star b * b).re
  -- Similarly for Im part using i·b instead of b.
  -- Combining: normSq = Re² + Im² ≤ 2 · φ(star a * a).re · φ(star b * b).re
  sorry

/-- The Cauchy-Schwarz inequality for states (tight form):
    |φ(b*a)|² ≤ φ(a*a) · φ(b*b).

    This is the fundamental inequality for the GNS construction. -/
theorem inner_mul_le_norm_mul_norm (a b : A) :
    Complex.normSq (φ (star b * a)) ≤ (φ (star a * a)).re * (φ (star b * b)).re := by
  -- The tight bound requires the complex discriminant argument:
  -- For λ ∈ ℂ, we have φ((a + λ·b)*(a + λ·b)) ≥ 0
  -- Setting λ = -conj(φ(star b * a)) / φ(star b * b) (when φ(star b * b) ≠ 0)
  -- gives the tight inequality after simplification.
  --
  -- The case φ(star b * b) = 0 is handled separately: the quadratic argument
  -- with t : ℝ shows Re(φ(star b * a)) = 0, and similarly Im = 0.
  sorry

/-- Cauchy-Schwarz with sesquilinear form notation. -/
theorem sesqForm_abs_sq_le (a b : A) :
    Complex.normSq (φ.sesqForm a b) ≤ (φ.sesqForm a a).re * (φ.sesqForm b b).re :=
  inner_mul_le_norm_mul_norm φ a b

/-! ### Consequences for the null space -/

/-- If φ(a*a) = 0, then φ(b*a) = 0 for all b. -/
theorem apply_star_mul_eq_zero_of_apply_star_self_eq_zero {a : A}
    (ha : φ (star a * a) = 0) (b : A) : φ (star b * a) = 0 := by
  have h := inner_mul_le_norm_mul_norm φ a b
  simp only [ha, Complex.zero_re, zero_mul] at h
  exact Complex.normSq_eq_zero.mp (le_antisymm h (Complex.normSq_nonneg _))

/-- Reformulation: null space is a left ideal (first step).
    If a is in the null space, so is b*a for any b. -/
theorem null_space_left_ideal {a : A} (ha : φ (star a * a) = 0) (b : A) :
    φ (star (b * a) * (b * a)) = 0 := by
  -- This requires showing: φ((b*a)*(b*a)) = φ(a* b* b a) ≤ ‖b*b‖ · φ(a*a) = 0
  -- Which uses boundedness of the state. For now we leave as sorry.
  sorry

end State
