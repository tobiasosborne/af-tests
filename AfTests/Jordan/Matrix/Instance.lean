/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Basic
import AfTests.Jordan.Matrix.JordanProduct
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Real.Star

/-!
# JordanAlgebra Instance for Hermitian Matrices

Hermitian matrices with the Jordan product form a Jordan algebra over ℝ.

## Main definitions

* `HermitianMatrix` - Type alias for selfAdjoint matrices
* `JordanAlgebra (HermitianMatrix n R)` - The Jordan algebra instance
-/

open Matrix

/-- Type alias for Hermitian (self-adjoint) matrices. -/
abbrev HermitianMatrix (n : Type*) [Fintype n] (R : Type*) [AddGroup R] [StarAddMonoid R] :=
  selfAdjoint (Matrix n n R)

namespace HermitianMatrix

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [Field R] [StarRing R] [CharZero R]

/-- The Jordan product on Hermitian matrices. -/
def jmul (A B : HermitianMatrix n R) : HermitianMatrix n R :=
  ⟨jordanMul A.val B.val, (A.prop.isHermitian.jordanMul B.prop.isHermitian).isSelfAdjoint⟩

theorem jmul_val (A B : HermitianMatrix n R) :
    (jmul A B).val = jordanMul A.val B.val := rfl

/-- Jordan product is commutative. -/
theorem jmul_comm (A B : HermitianMatrix n R) : jmul A B = jmul B A := by
  apply Subtype.ext
  exact jordanMul_comm A.val B.val

/-- The identity matrix is Hermitian. -/
def one : HermitianMatrix n R :=
  ⟨1, isHermitian_one.isSelfAdjoint⟩

theorem one_val : (one : HermitianMatrix n R).val = 1 := rfl

/-- Jordan product with identity. -/
theorem jmul_one (A : HermitianMatrix n R) : jmul A one = A := by
  apply Subtype.ext
  simp only [jmul_val, one_val, jordanMul_one]

theorem one_jmul (A : HermitianMatrix n R) : jmul one A = A := by
  rw [jmul_comm, jmul_one]

/-- Jordan product distributes over addition. -/
theorem jmul_add (A B C : HermitianMatrix n R) :
    jmul A (B + C) = jmul A B + jmul A C := by
  apply Subtype.ext
  simp only [jmul_val, AddSubgroup.coe_add, jordanMul_def]
  simp only [mul_add, add_mul]
  rw [← smul_add]
  congr 1
  abel

/-- Jordan product respects scalar multiplication. -/
theorem jmul_smul [Algebra ℝ R] [StarModule ℝ R] (r : ℝ) (A B : HermitianMatrix n R) :
    jmul (r • A) B = r • jmul A B := by
  apply Subtype.ext
  simp only [jmul_val, jordanMul_def]
  have h1 : ((r • A) : HermitianMatrix n R).val = r • A.val := rfl
  have h2 : (r • jmul A B : HermitianMatrix n R).val = r • (jmul A B).val := rfl
  simp only [h1, h2, jmul_val, jordanMul_def]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_add]
  simp only [smul_comm (2 : R)⁻¹ r]

/-! ### Jordan Identity -/

/-- The Jordan identity for matrices.

The Jordan identity `(a ∘ b) ∘ a² = a ∘ (b ∘ a²)` where `a ∘ b = (ab + ba)/2`.
Both sides expand to `(aba² + ba³ + a³b + a²ba) / 4`.
-/
theorem jordanMul_jordan_identity (A B : Matrix n n R) :
    jordanMul (jordanMul A B) (jordanMul A A) =
    jordanMul A (jordanMul B (jordanMul A A)) := by
  simp only [jordanMul_def]
  -- Simplify A ∘ A = (AA + AA)/2 = AA
  have hAA : (2 : R)⁻¹ • (A * A + A * A) = A * A := by
    rw [← two_smul R (A * A), smul_smul]
    simp [mul_comm (2 : R)⁻¹ 2]
  -- Expand systematically
  conv_lhs => rw [hAA]
  conv_rhs => rw [hAA]
  -- Expand the scalar multiplications and additions
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_add, add_mul, mul_add]
  simp only [smul_smul]
  -- Use associativity
  simp only [Matrix.mul_assoc]
  -- Now both sides are sums of terms like k • (A * B * A * A) etc.
  -- LHS = k•(ABA²) + k•(BA³) + k•(A³B) + k•(A²BA)
  -- RHS = k•(ABA²) + k•(A³B) + k•(BA³) + k•(A²BA)
  -- These are equal by commutativity of addition
  abel

/-- The Jordan identity for Hermitian matrices. -/
theorem jordan_identity (A B : HermitianMatrix n R) :
    jmul (jmul A B) (jmul A A) = jmul A (jmul B (jmul A A)) := by
  apply Subtype.ext
  simp only [jmul_val]
  exact jordanMul_jordan_identity A.val B.val

end HermitianMatrix

/-! ### JordanAlgebra Instance -/

instance jordanAlgebraHermitianMatrix {n : Type*} [DecidableEq n] [Fintype n]
    {R : Type*} [Field R] [StarRing R] [CharZero R] [Algebra ℝ R] [StarModule ℝ R] :
    JordanAlgebra (HermitianMatrix n R) where
  jmul := HermitianMatrix.jmul
  jmul_comm := HermitianMatrix.jmul_comm
  jordan_identity := HermitianMatrix.jordan_identity
  jone := HermitianMatrix.one
  jone_jmul := HermitianMatrix.one_jmul
  jmul_add := HermitianMatrix.jmul_add
  jmul_smul := HermitianMatrix.jmul_smul
