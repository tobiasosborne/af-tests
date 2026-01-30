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

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [Field R] [Star R] [CharZero R]

namespace Matrix

/-! ### Jordan Product -/

/-- The Jordan product on matrices: A ∘ B = (AB + BA) / 2 -/
def jordanMul (A B : Matrix n n R) : Matrix n n R :=
  (2 : R)⁻¹ • (A * B + B * A)

theorem jordanMul_def (A B : Matrix n n R) :
    jordanMul A B = (2 : R)⁻¹ • (A * B + B * A) := rfl

/-- Jordan product is commutative. -/
theorem jordanMul_comm (A B : Matrix n n R) : jordanMul A B = jordanMul B A := by
  simp only [jordanMul_def, add_comm]

/-- Jordan product with identity. -/
theorem jordanMul_one (A : Matrix n n R) : jordanMul A 1 = A := by
  simp only [jordanMul_def, mul_one, one_mul, ← two_smul R A,
    inv_smul_smul₀ (two_ne_zero : (2 : R) ≠ 0)]

theorem one_jordanMul (A : Matrix n n R) : jordanMul 1 A = A := by
  rw [jordanMul_comm, jordanMul_one]

/-- Jordan product with zero. -/
theorem jordanMul_zero (A : Matrix n n R) : jordanMul A 0 = 0 := by
  simp [jordanMul_def]

theorem zero_jordanMul (A : Matrix n n R) : jordanMul 0 A = 0 := by
  rw [jordanMul_comm, jordanMul_zero]

/-- The Jordan square equals the matrix square. -/
theorem jordanMul_self (A : Matrix n n R) : jordanMul A A = A * A := by
  simp only [jordanMul_def, ← two_smul R (A * A),
    inv_smul_smul₀ (two_ne_zero : (2 : R) ≠ 0)]

/-! ### Hermitian Matrices -/

/-- Hermitian matrices are closed under Jordan product for complex-like scalars. -/
theorem IsHermitian.jordanMul [StarRing R] {A B : Matrix n n R}
    (hA : IsHermitian A) (hB : IsHermitian B) : IsHermitian (jordanMul A B) := by
  -- The proof uses: (r • M)ᴴ = star(r) • Mᴴ, (M + N)ᴴ = Mᴴ + Nᴴ, (M * N)ᴴ = Nᴴ * Mᴴ
  -- And star(2⁻¹) = 2⁻¹ for star rings over CharZero
  sorry

end Matrix
