/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Quaternion.Hermitian
import AfTests.Jordan.Matrix.JordanProduct

/-!
# Jordan Product for Quaternionic Hermitian Matrices

This file defines the Jordan product on quaternionic Hermitian matrices and proves
that it preserves the Hermitian property.

## Main definitions

* `QuaternionHermitianMatrix.jordanMul` - The Jordan product `A ∘ B = (AB + BA) / 2`

## Main results

* `hermitian_jordanMul` - Jordan product of Hermitian matrices is Hermitian

## Implementation notes

The Jordan product uses real scalar multiplication by `(2 : ℝ)⁻¹` rather than
quaternion scalar multiplication. This is because:
1. Real scalars commute with the star operation: `star(r • q) = r • star(q)`
2. Real scalars are central in quaternions: `r * q = q * r`

For quaternion scalars, star is anti-multiplicative, which would complicate
the Hermitian property proof.
-/

noncomputable section

open Matrix QuaternionHermitianMatrix

namespace QuaternionHermitianMatrix

variable {n : Type*} [DecidableEq n] [Fintype n]

/-! ### Jordan Product Definition -/

/-- The Jordan product on quaternionic matrices: `A ∘ B = (2)⁻¹ • (AB + BA)`.

We use real scalar multiplication to ensure the Hermitian property is preserved. -/
def jordanMul (A B : Matrix n n (Quaternion ℝ)) : Matrix n n (Quaternion ℝ) :=
  (2 : ℝ)⁻¹ • (A * B + B * A)

omit [DecidableEq n] in
theorem jordanMul_def (A B : Matrix n n (Quaternion ℝ)) :
    jordanMul A B = (2 : ℝ)⁻¹ • (A * B + B * A) := rfl

/-! ### Jordan Product Properties -/

omit [DecidableEq n] in
/-- Jordan product is commutative. -/
theorem jordanMul_comm (A B : Matrix n n (Quaternion ℝ)) :
    jordanMul A B = jordanMul B A := by
  simp only [jordanMul_def, add_comm]

/-- Jordan product with identity. -/
theorem jordanMul_one (A : Matrix n n (Quaternion ℝ)) : jordanMul A 1 = A := by
  simp only [jordanMul_def, Matrix.mul_one, Matrix.one_mul]
  rw [← two_smul ℝ A, smul_smul]
  simp

theorem one_jordanMul (A : Matrix n n (Quaternion ℝ)) : jordanMul 1 A = A := by
  rw [jordanMul_comm, jordanMul_one]

omit [DecidableEq n] in
/-- Jordan product with zero. -/
theorem jordanMul_zero (A : Matrix n n (Quaternion ℝ)) : jordanMul A 0 = 0 := by
  simp [jordanMul_def]

omit [DecidableEq n] in
theorem zero_jordanMul (A : Matrix n n (Quaternion ℝ)) : jordanMul 0 A = 0 := by
  rw [jordanMul_comm, jordanMul_zero]

omit [DecidableEq n] in
/-- The Jordan square equals the matrix square. -/
theorem jordanMul_self (A : Matrix n n (Quaternion ℝ)) : jordanMul A A = A * A := by
  simp only [jordanMul_def]
  rw [← two_smul ℝ (A * A), smul_smul]
  simp

/-! ### Hermitian Preservation -/

omit [DecidableEq n] in
/-- Quaternionic Hermitian matrices are closed under Jordan product.

For Hermitian A, B: `(A ∘ B)ᴴ = ((AB + BA)/2)ᴴ = (BA + AB)/2 = A ∘ B`. -/
theorem hermitian_jordanMul {A B : Matrix n n (Quaternion ℝ)}
    (hA : IsHermitian A) (hB : IsHermitian B) :
    IsHermitian (jordanMul A B) := by
  have hAB : (A * B).conjTranspose = B * A := conjTranspose_mul_hermitian hA hB
  have hBA : (B * A).conjTranspose = A * B := conjTranspose_mul_hermitian hB hA
  rw [IsHermitian, jordanMul_def, conjTranspose_smul_real, Matrix.conjTranspose_add,
      hAB, hBA, add_comm]

/-! ### Jordan Product on QuaternionHermitianMatrix -/

/-- The Jordan product on quaternionic Hermitian matrices. -/
def jmul (A B : QuaternionHermitianMatrix n) : QuaternionHermitianMatrix n :=
  ⟨jordanMul A.val B.val,
   (hermitian_jordanMul A.prop.isHermitian B.prop.isHermitian).isSelfAdjoint⟩

theorem jmul_val (A B : QuaternionHermitianMatrix n) :
    (jmul A B).val = jordanMul A.val B.val := rfl

/-- Jordan product on QuaternionHermitianMatrix is commutative. -/
theorem jmul_comm (A B : QuaternionHermitianMatrix n) : jmul A B = jmul B A := by
  apply Subtype.ext
  exact jordanMul_comm A.val B.val

/-- Jordan product with identity. -/
theorem jmul_one (A : QuaternionHermitianMatrix n) : jmul A one = A := by
  apply Subtype.ext
  simp only [jmul_val, one, jordanMul_one]

theorem one_jmul (A : QuaternionHermitianMatrix n) : jmul one A = A := by
  rw [jmul_comm, jmul_one]

end QuaternionHermitianMatrix

end
