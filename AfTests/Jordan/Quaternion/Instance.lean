/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Quaternion.JordanProduct

/-!
# JordanAlgebra Instance for Quaternionic Hermitian Matrices

## Main results

* `jordanAlgebraQuaternionHermitianMatrix` - JordanAlgebra instance
-/

noncomputable section

open Matrix QuaternionHermitianMatrix

namespace QuaternionHermitianMatrix

variable {n : Type*} [DecidableEq n] [Fintype n]

/-! ### Additivity at Matrix Level -/

omit [DecidableEq n] in
theorem jordanMul_add (A B C : Matrix n n (Quaternion ℝ)) :
    jordanMul A (B + C) = jordanMul A B + jordanMul A C := by
  simp only [jordanMul_def, Matrix.mul_add, Matrix.add_mul, smul_add]
  abel

omit [DecidableEq n] in
theorem add_jordanMul (A B C : Matrix n n (Quaternion ℝ)) :
    jordanMul (A + B) C = jordanMul A C + jordanMul B C := by
  rw [jordanMul_comm, jordanMul_add, jordanMul_comm C A, jordanMul_comm C B]

/-! ### Scalar Multiplication at Matrix Level -/

omit [DecidableEq n] in
theorem jordanMul_smul (r : ℝ) (A B : Matrix n n (Quaternion ℝ)) :
    jordanMul (r • A) B = r • jordanMul A B := by
  simp only [jordanMul_def, Matrix.smul_mul, Matrix.mul_smul]
  rw [← smul_add, smul_comm]

omit [DecidableEq n] in
theorem smul_jordanMul (r : ℝ) (A B : Matrix n n (Quaternion ℝ)) :
    jordanMul A (r • B) = r • jordanMul A B := by
  rw [jordanMul_comm, jordanMul_smul, jordanMul_comm]

/-! ### Jordan Identity at Matrix Level -/

omit [DecidableEq n] in
/-- The Jordan identity for quaternion matrices. -/
theorem jordanMul_jordan_identity (A B : Matrix n n (Quaternion ℝ)) :
    jordanMul (jordanMul A B) (jordanMul A A) =
    jordanMul A (jordanMul B (jordanMul A A)) := by
  simp only [jordanMul_def]
  have hAA : (2 : ℝ)⁻¹ • (A * A + A * A) = A * A := by
    rw [← two_smul ℝ (A * A), smul_smul]; simp
  conv_lhs => rw [hAA]
  conv_rhs => rw [hAA]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_add, add_mul, mul_add]
  simp only [smul_smul, Matrix.mul_assoc]
  abel

/-! ### Lifted Properties for QuaternionHermitianMatrix -/

theorem jmul_add (A B C : QuaternionHermitianMatrix n) :
    jmul A (B + C) = jmul A B + jmul A C := by
  apply Subtype.ext
  simp only [jmul_val]
  change jordanMul A.val (B.val + C.val) = jordanMul A.val B.val + jordanMul A.val C.val
  exact jordanMul_add A.val B.val C.val

theorem add_jmul (A B C : QuaternionHermitianMatrix n) :
    jmul (A + B) C = jmul A C + jmul B C := by
  apply Subtype.ext
  simp only [jmul_val]
  change jordanMul (A.val + B.val) C.val = jordanMul A.val C.val + jordanMul B.val C.val
  exact add_jordanMul A.val B.val C.val

theorem jmul_smul (r : ℝ) (A B : QuaternionHermitianMatrix n) :
    jmul (r • A) B = r • jmul A B := by
  apply Subtype.ext
  simp only [jmul_val]
  change jordanMul (r • A.val) B.val = r • jordanMul A.val B.val
  exact jordanMul_smul r A.val B.val

theorem smul_jmul (r : ℝ) (A B : QuaternionHermitianMatrix n) :
    jmul A (r • B) = r • jmul A B := by
  rw [jmul_comm, jmul_smul, jmul_comm]

/-! ### Jordan Identity -/

/-- The Jordan identity for quaternionic Hermitian matrices. -/
theorem jordan_identity (A B : QuaternionHermitianMatrix n) :
    jmul (jmul A B) (jmul A A) = jmul A (jmul B (jmul A A)) := by
  apply Subtype.ext
  simp only [jmul_val]
  exact jordanMul_jordan_identity A.val B.val

end QuaternionHermitianMatrix

/-! ### JordanAlgebra Instance -/

/-- Explicit Module ℝ instance for QuaternionHermitianMatrix to avoid typeclass loop.

This is needed because JordanAlgebra extends Module ℝ, and typeclass search can enter
an infinite loop trying to find Module ℝ via JordanAlgebra.toModule. -/
instance moduleQuaternionHermitianMatrix {n : Type*} [DecidableEq n] [Fintype n] :
    Module ℝ (QuaternionHermitianMatrix n) :=
  selfAdjoint.instModuleSubtypeMemAddSubgroupOfStarModule

instance jordanAlgebraQuaternionHermitianMatrix {n : Type*} [DecidableEq n] [Fintype n] :
    JordanAlgebra (QuaternionHermitianMatrix n) where
  jmul := QuaternionHermitianMatrix.jmul
  jmul_comm := QuaternionHermitianMatrix.jmul_comm
  jordan_identity := QuaternionHermitianMatrix.jordan_identity
  jone := QuaternionHermitianMatrix.one
  jone_jmul := QuaternionHermitianMatrix.one_jmul
  jmul_add := QuaternionHermitianMatrix.jmul_add
  jmul_smul := QuaternionHermitianMatrix.jmul_smul

end
