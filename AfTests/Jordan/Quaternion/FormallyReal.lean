/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Quaternion.Instance
import AfTests.Jordan.FormallyReal.Def

/-!
# Quaternionic Hermitian Matrices are Formally Real

Quaternionic Hermitian matrices form a formally real Jordan algebra:
if A² = 0 then A = 0.

## Main results

* `QuaternionHermitianMatrix.sq_eq_zero_imp_zero` - If A² = 0 then A = 0
* `QuaternionHermitianMatrix.formallyReal` - The FormallyRealJordan' instance

## Mathematical approach

For a Hermitian matrix A (satisfying Aᴴ = A):
1. A² = A * A (since jordanMul A A = A * A for Hermitian matrices)
2. If A * A = 0, then diagonal entries (A * A)ᵢᵢ = 0
3. (A * A)ᵢᵢ = Σⱼ Aᵢⱼ * star(Aᵢⱼ) = Σⱼ normSq(Aᵢⱼ) (by Hermitian property)
4. Since normSq ≥ 0 and the sum is 0, all normSq(Aᵢⱼ) = 0
5. Therefore all Aᵢⱼ = 0, so A = 0
-/

noncomputable section

open Matrix Finset BigOperators QuaternionHermitianMatrix

namespace QuaternionHermitianMatrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Auxiliary Lemmas -/

/-- Coercion from ℝ to Quaternion ℝ is injective. -/
private theorem quaternion_coe_injective :
    Function.Injective (Quaternion.coe : ℝ → Quaternion ℝ) := by
  intro x y h
  have : (x : Quaternion ℝ).re = (y : Quaternion ℝ).re := by rw [h]
  simp only [Quaternion.re_coe] at this
  exact this

/-- Sum of coercions equals coercion of sum. -/
private theorem quaternion_sum_coe_eq_coe_sum (f : n → ℝ) :
    (∑ k : n, (↑(f k) : Quaternion ℝ)) = ↑(∑ k : n, f k) := by
  have : (fun k => (↑(f k) : Quaternion ℝ)) = (fun k => algebraMap ℝ (Quaternion ℝ) (f k)) := rfl
  rw [this, ← map_sum (algebraMap ℝ (Quaternion ℝ))]
  rfl

/-! ### Key Lemmas -/

/-- For a Hermitian quaternion matrix, diagonal entries of A*A equal sum of normSq. -/
theorem diag_mul_self_hermitian (A : Matrix n n (Quaternion ℝ)) (hA : A.IsHermitian) (i : n) :
    (A * A) i i = ∑ j, (↑(Quaternion.normSq (A i j)) : Quaternion ℝ) := by
  simp only [Matrix.mul_apply]
  congr 1
  funext j
  have hji : A j i = star (A i j) := by
    have h := congrFun (congrFun hA.eq j) i
    simp only [conjTranspose_apply] at h
    exact h.symm
  rw [hji]
  exact Quaternion.self_mul_star (A i j)

/-- Sum of normSq is zero iff all entries in that row are zero. -/
theorem sum_normSq_eq_zero_iff (A : Matrix n n (Quaternion ℝ)) (i : n) :
    (∑ j : n, Quaternion.normSq (A i j)) = 0 ↔ ∀ j, A i j = 0 := by
  constructor
  · intro h j
    have hnonneg : ∀ k ∈ univ, 0 ≤ Quaternion.normSq (A i k) := fun _ _ => Quaternion.normSq_nonneg
    have hj_zero := Finset.sum_eq_zero_iff_of_nonneg hnonneg
    rw [h] at hj_zero
    simp only [true_iff, mem_univ, forall_true_left] at hj_zero
    exact Quaternion.normSq_eq_zero.mp (hj_zero j)
  · intro h
    have : ∀ j, Quaternion.normSq (A i j) = 0 := fun j => by rw [h j]; simp [map_zero]
    simp [this]

/-- For Hermitian quaternion matrices, if A*A = 0 then A = 0. -/
theorem matrix_sq_eq_zero_imp_zero (A : Matrix n n (Quaternion ℝ)) (hA : A.IsHermitian)
    (h : A * A = 0) : A = 0 := by
  funext i j
  have hii : (A * A) i i = 0 := by simp [h]
  rw [diag_mul_self_hermitian A hA i] at hii
  have hsum : (∑ k : n, Quaternion.normSq (A i k)) = 0 := by
    rw [quaternion_sum_coe_eq_coe_sum] at hii
    exact quaternion_coe_injective hii
  exact (sum_normSq_eq_zero_iff A i).mp hsum j

/-! ### Connection to Jordan Algebra -/

/-- The Jordan square of a quaternionic Hermitian matrix equals the matrix square. -/
theorem jsq_val_eq_mul_self (A : QuaternionHermitianMatrix n) :
    (JordanAlgebra.jsq A).val = A.val * A.val := by
  simp only [JordanAlgebra.jsq, JordanAlgebra.jmul, jmul_val, jordanMul_self]

/-- If A² = 0 as a Jordan element, then A = 0. -/
theorem sq_eq_zero_imp_zero (A : QuaternionHermitianMatrix n)
    (h : JordanAlgebra.jsq A = 0) : A = 0 := by
  have hval : A.val * A.val = 0 := by
    have heq := congrArg Subtype.val h
    rw [jsq_val_eq_mul_self] at heq
    exact heq
  have hA_zero : A.val = 0 := matrix_sq_eq_zero_imp_zero A.val A.prop.isHermitian hval
  exact Subtype.ext hA_zero

/-! ### Formally Real Instance -/

/-- Quaternionic Hermitian matrices form a formally real Jordan algebra. -/
instance formallyReal : FormallyRealJordan' (QuaternionHermitianMatrix n) where
  sq_eq_zero_imp_zero := sq_eq_zero_imp_zero

end QuaternionHermitianMatrix

end
