/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Jordan Product on Matrices

The Jordan product on matrices is defined as `A ∘ B = (AB + BA) / 2`. This makes the
self-adjoint (Hermitian) matrices into a Jordan algebra.

## Main definitions

* `Matrix.jordanMul` - The Jordan product on matrices

## Main results

* `Matrix.jordanMul_comm` - Jordan product is commutative
* `Matrix.IsHermitian.jordanMul` - Hermitian matrices are closed under Jordan product
-/

open Matrix

namespace Matrix

section Basic

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [Field R] [CharZero R]

/-! ### Jordan Product -/

/-- The Jordan product on matrices: A ∘ B = (AB + BA) / 2 -/
def jordanMul (A B : Matrix n n R) : Matrix n n R :=
  (2 : R)⁻¹ • (A * B + B * A)

omit [DecidableEq n] [CharZero R] in
theorem jordanMul_def (A B : Matrix n n R) :
    jordanMul A B = (2 : R)⁻¹ • (A * B + B * A) := rfl

omit [DecidableEq n] [CharZero R] in
/-- Jordan product is commutative. -/
theorem jordanMul_comm (A B : Matrix n n R) : jordanMul A B = jordanMul B A := by
  simp only [jordanMul_def, add_comm]

/-- Jordan product with identity. -/
theorem jordanMul_one (A : Matrix n n R) : jordanMul A 1 = A := by
  simp only [jordanMul_def, mul_one, one_mul, ← two_smul R A,
    inv_smul_smul₀ (two_ne_zero : (2 : R) ≠ 0)]

theorem one_jordanMul (A : Matrix n n R) : jordanMul 1 A = A := by
  rw [jordanMul_comm, jordanMul_one]

omit [DecidableEq n] [CharZero R] in
/-- Jordan product with zero. -/
theorem jordanMul_zero (A : Matrix n n R) : jordanMul A 0 = 0 := by
  simp [jordanMul_def]

omit [DecidableEq n] in
theorem zero_jordanMul (A : Matrix n n R) : jordanMul 0 A = 0 := by
  rw [jordanMul_comm, jordanMul_zero]

omit [DecidableEq n] in
/-- The Jordan square equals the matrix square. -/
theorem jordanMul_self (A : Matrix n n R) : jordanMul A A = A * A := by
  simp only [jordanMul_def, ← two_smul R (A * A),
    inv_smul_smul₀ (two_ne_zero : (2 : R) ≠ 0)]

end Basic

/-! ### Hermitian Matrices -/

section Hermitian

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [Field R] [StarRing R] [CharZero R]

/-- Hermitian matrices are closed under Jordan product for complex-like scalars. -/
theorem IsHermitian.jordanMul {A B : Matrix n n R}
    (hA : IsHermitian A) (hB : IsHermitian B) : IsHermitian (jordanMul A B) := by
  have hAB : (A * B)ᴴ = B * A := by rw [conjTranspose_mul, hA.eq, hB.eq]
  have hBA : (B * A)ᴴ = A * B := by rw [conjTranspose_mul, hB.eq, hA.eq]
  rw [IsHermitian, jordanMul_def]
  ext i j
  simp only [conjTranspose_apply, smul_apply, add_apply, mul_apply, Algebra.id.smul_eq_mul]
  rw [star_mul', star_inv₀, star_ofNat, star_add, star_sum, star_sum]
  -- Now goal is: 2⁻¹ * (∑ star(A j x * B x i) + ∑ star(B j x * A x i)) = ...
  have eq1 : ∀ x, star (A j x * B x i) = B i x * A x j := fun x => by
    rw [star_mul', hA.apply, hB.apply, mul_comm]
  have eq2 : ∀ x, star (B j x * A x i) = A i x * B x j := fun x => by
    rw [star_mul', hB.apply, hA.apply, mul_comm]
  simp only [eq1, eq2, add_comm]

end Hermitian

end Matrix
