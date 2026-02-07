/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Macdonald.FJOperators
import AfTests.Jordan.Macdonald.OperatorId

/-!
# Bridge Lemmas: JordanAlgebra operators ↔ FreeJordanAlg operators

FreeJordanAlg has a JordanAlgebra instance (FJOperators.lean), so all
JordanAlgebra theorems (operator identities, etc.) apply. These bridge
lemmas relate the JordanAlgebra-level operators to the FreeJordanAlg-level
operators used in M_op and the equation (2.58) proofs.

## Main results

* `FJ_U_eq` — `JordanAlgebra.U a v = FreeJordanAlg.U a v`
* `FJ_U_linear_apply` — `JordanAlgebra.U_linear a v = FreeJordanAlg.U a v`
* `FJ_U_bilinear_eq` — `JordanAlgebra.U_bilinear_linear a b v = FreeJordanAlg.U_bilinear a b v`
-/

/-- JordanAlgebra.U on FreeJordanAlg equals FreeJordanAlg.U.
    The only difference is nsmul 2 vs (2:ℝ) •, which agree in ℝ-modules. -/
theorem FJ_U_eq (a v : FreeJordanAlg) :
    JordanAlgebra.U a v = FreeJordanAlg.U a v := by
  simp only [JordanAlgebra.U_def, FreeJordanAlg.U, FJ_jmul_eq_mul, JordanAlgebra.jsq_def]
  congr 1
  rw [two_smul, two_smul]

/-- JordanAlgebra.U_linear on FreeJordanAlg equals FreeJordanAlg.U. -/
theorem FJ_U_linear_apply (a v : FreeJordanAlg) :
    JordanAlgebra.U_linear a v = FreeJordanAlg.U a v := by
  rw [JordanAlgebra.U_linear_apply]; exact FJ_U_eq a v

/-- JordanAlgebra.U_bilinear_linear on FreeJordanAlg equals
    FreeJordanAlg.U_bilinear. Proof uses commutativity of FreeJordanAlg.mul
    to match the different argument orderings. -/
theorem FJ_U_bilinear_eq (a b v : FreeJordanAlg) :
    JordanAlgebra.U_bilinear_linear a b v =
    FreeJordanAlg.U_bilinear a b v := by
  simp only [JordanAlgebra.U_bilinear_linear_apply, JordanAlgebra.triple_def,
    FreeJordanAlg.U_bilinear_apply, FJ_jmul_eq_mul]
  rw [FreeJordanAlg.mul_comm (FreeJordanAlg.mul a v) b,
      FreeJordanAlg.mul_comm v b,
      FreeJordanAlg.mul_comm v (FreeJordanAlg.mul a b)]
  abel
