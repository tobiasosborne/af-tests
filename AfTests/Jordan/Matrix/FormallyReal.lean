/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.FormallyReal.Def
import AfTests.Jordan.Matrix.Instance
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.RCLike.Basic

/-!
# Hermitian Matrices are Formally Real

For an RCLike scalar type 𝕜 (such as ℝ or ℂ), Hermitian matrices form a formally real
Jordan algebra: if a sum of squares vanishes, each summand must be zero.

## Main results

* `HermitianMatrix.formallyRealJordan` - The `FormallyRealJordan` instance

## Implementation notes

The proof uses the matrix partial order from `Mathlib.Analysis.Matrix.Order`, where
`A ≤ B ↔ (B - A).PosSemidef`. Key steps:
1. For Hermitian A, `jsq A = A * A = Aᴴ * A` is positive semidefinite
2. If sum of PSD matrices = 0, each must be 0 (using the ordered structure)
3. `Aᴴ * A = 0 ↔ A = 0` (from `conjTranspose_mul_self_eq_zero`)
-/

open Matrix Finset BigOperators

-- ComplexOrder gives PartialOrder and StarOrderedRing for RCLike types
-- MatrixOrder gives the matrix partial order
open scoped ComplexOrder MatrixOrder

namespace HermitianMatrix

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Jordan square as matrix square -/

/-- The Jordan square of a Hermitian matrix equals its matrix square. -/
theorem jsq_val (A : HermitianMatrix n 𝕜) :
    (JordanAlgebra.jsq A).val = A.val * A.val := by
  change (JordanAlgebra.jmul A A).val = A.val * A.val
  rw [show JordanAlgebra.jmul A A = jmul A A from rfl]
  rw [jmul_val, jordanMul_self]

/-- For Hermitian A, A * A = Aᴴ * A. -/
theorem sq_eq_conjTranspose_mul (A : HermitianMatrix n 𝕜) :
    A.val * A.val = A.val.conjTranspose * A.val := by
  rw [A.prop.isHermitian.eq]

/-- The matrix square of a Hermitian matrix is positive semidefinite. -/
theorem sq_posSemidef (A : HermitianMatrix n 𝕜) : (A.val * A.val).PosSemidef := by
  rw [sq_eq_conjTranspose_mul]
  exact posSemidef_conjTranspose_mul_self A.val

/-- Jordan square is nonneg in the matrix order. -/
theorem jsq_nonneg (A : HermitianMatrix n 𝕜) : 0 ≤ (JordanAlgebra.jsq A).val := by
  rw [jsq_val]
  exact (sq_posSemidef A).nonneg

/-! ### Zero characterization -/

/-- For Hermitian matrices, square = 0 implies the matrix is 0. -/
theorem sq_eq_zero_imp_zero {A : HermitianMatrix n 𝕜}
    (h : A.val * A.val = 0) : A = 0 := by
  apply Subtype.ext
  rw [sq_eq_conjTranspose_mul] at h
  simp only [AddSubgroup.coe_zero]
  exact conjTranspose_mul_self_eq_zero.mp h

/-- In Hermitian matrices, jsq a = 0 implies a = 0. -/
theorem jsq_eq_zero_imp_zero {A : HermitianMatrix n 𝕜}
    (h : JordanAlgebra.jsq A = 0) : A = 0 := by
  apply sq_eq_zero_imp_zero
  have h' : (JordanAlgebra.jsq A).val = (0 : HermitianMatrix n 𝕜).val := by rw [h]
  rw [jsq_val] at h'
  simpa using h'

/-! ### Sum of squares characterization -/

/-- Sum of Jordan squares corresponds to sum of matrix squares. -/
theorem sum_jsq_val {m : ℕ} (a : Fin m → HermitianMatrix n 𝕜) :
    (∑ i, JordanAlgebra.jsq (a i)).val = ∑ i, (a i).val * (a i).val := by
  simp only [← jsq_val]
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [AddSubgroup.coe_add, ih]

/-- Each matrix square in a sum is nonneg. -/
theorem each_sq_nonneg {m : ℕ} (a : Fin m → HermitianMatrix n 𝕜) (i : Fin m) :
    0 ≤ (a i).val * (a i).val :=
  (sq_posSemidef (a i)).nonneg

/-- If a sum of squares of Hermitian matrices is zero, each term is zero.

This is the key property making Hermitian matrices formally real. -/
theorem sum_sq_eq_zero_imp_all_zero {m : ℕ} (a : Fin m → HermitianMatrix n 𝕜)
    (hsum : ∑ i, (a i).val * (a i).val = 0) : ∀ i, a i = 0 := by
  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ (a i).val * (a i).val :=
    fun i _ => each_sq_nonneg a i
  rw [sum_eq_zero_iff_of_nonneg h_nonneg] at hsum
  intro i
  exact sq_eq_zero_imp_zero (hsum i (mem_univ i))

end HermitianMatrix

/-! ### FormallyRealJordan Instance -/

/-- Hermitian matrices over RCLike form a formally real Jordan algebra. -/
instance formallyRealJordanHermitianMatrix {n : Type*} [DecidableEq n] [Fintype n]
    {𝕜 : Type*} [RCLike 𝕜] : FormallyRealJordan (HermitianMatrix n 𝕜) where
  sum_sq_eq_zero m a hsum := by
    have h : (∑ i, JordanAlgebra.jsq (a i)).val = 0 := by
      simp only [hsum, AddSubgroup.coe_zero]
    rw [HermitianMatrix.sum_jsq_val] at h
    exact HermitianMatrix.sum_sq_eq_zero_imp_all_zero a h
