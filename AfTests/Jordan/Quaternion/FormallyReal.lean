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
if a sum of squares equals zero, each term is zero.

## Main results

* `QuaternionHermitianMatrix.sq_eq_zero_imp_zero` - If A² = 0 then A = 0
* `QuaternionHermitianMatrix.formallyReal` - The FormallyRealJordan instance

## Mathematical approach

For a Hermitian matrix A (satisfying Aᴴ = A):
1. A² = A * A (since jordanMul A A = A * A for Hermitian matrices)
2. (A * A)ᵢᵢ = Σⱼ Aᵢⱼ * star(Aᵢⱼ) = Σⱼ normSq(Aᵢⱼ) (by Hermitian property)
3. Since normSq ≥ 0, the diagonal (A * A)ᵢᵢ is a sum of non-negative reals
4. For sum of squares Σₖ Aₖ², diagonal = Σₖ Σⱼ normSq(Aₖᵢⱼ) ≥ 0
5. If sum = 0, by sum_eq_zero_iff_of_nonneg, each Aₖ = 0

## Implementation

We prove `FormallyRealJordan` directly by verifying the sum-of-squares property.
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

/-! ### Sum of Squares Properties -/

/-- The normSq sum across all matrices at a given diagonal position. -/
private def totalNormSq {m : ℕ} (A : Fin m → QuaternionHermitianMatrix n) (i : n) : ℝ :=
  ∑ k, ∑ j, Quaternion.normSq ((A k).val i j)

/-- Total normSq is non-negative. -/
private theorem totalNormSq_nonneg {m : ℕ} (A : Fin m → QuaternionHermitianMatrix n) (i : n) :
    0 ≤ totalNormSq A i :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Quaternion.normSq_nonneg

/-- Diagonal of sum of Jordan squares equals sum of diagonals (as quaternions). -/
theorem sum_jsq_diag {m : ℕ} (A : Fin m → QuaternionHermitianMatrix n) (i : n) :
    (∑ k, JordanAlgebra.jsq (A k)).val i i =
    ∑ k, ((A k).val * (A k).val) i i := by
  induction m with
  | zero => simp [Matrix.zero_apply]
  | succ p ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [AddSubgroup.coe_add, Matrix.add_apply, jsq_val_eq_mul_self]
    congr 1
    exact ih (fun k => A k.succ)

/-- Diagonal of sum expressed as total normSq. -/
theorem sum_jsq_diag_eq_totalNormSq {m : ℕ} (A : Fin m → QuaternionHermitianMatrix n) (i : n) :
    (∑ k, JordanAlgebra.jsq (A k)).val i i = ↑(totalNormSq A i) := by
  rw [sum_jsq_diag]
  unfold totalNormSq
  rw [← quaternion_sum_coe_eq_coe_sum]
  congr 1
  funext k
  rw [← quaternion_sum_coe_eq_coe_sum]
  exact diag_mul_self_hermitian (A k).val (A k).prop.isHermitian i

/-- If sum of squares is zero, total normSq at each diagonal is zero. -/
theorem sum_jsq_zero_imp_totalNormSq_zero {m : ℕ} (A : Fin m → QuaternionHermitianMatrix n)
    (hsum : ∑ k, JordanAlgebra.jsq (A k) = 0) (i : n) : totalNormSq A i = 0 := by
  have h : (∑ k, JordanAlgebra.jsq (A k)).val i i = 0 := by simp [hsum]
  rw [sum_jsq_diag_eq_totalNormSq] at h
  exact quaternion_coe_injective h

/-- If sum of squares is zero, each matrix is zero. -/
theorem sum_sq_eq_zero_imp_all_zero {m : ℕ} (A : Fin m → QuaternionHermitianMatrix n)
    (hsum : ∑ k, JordanAlgebra.jsq (A k) = 0) : ∀ k, A k = 0 := by
  intro k
  apply Subtype.ext
  funext i j
  -- Total normSq at row i is zero
  have htotal : totalNormSq A i = 0 := sum_jsq_zero_imp_totalNormSq_zero A hsum i
  -- totalNormSq = Σₖ Σⱼ normSq(Aₖᵢⱼ), a sum of non-negative reals
  unfold totalNormSq at htotal
  -- Each inner sum is non-negative
  have h_outer_nonneg : ∀ l ∈ Finset.univ, 0 ≤ ∑ j', Quaternion.normSq ((A l).val i j') :=
    fun l _ => Finset.sum_nonneg fun _ _ => Quaternion.normSq_nonneg
  -- So each inner sum is zero
  have h_inner_zero :=
    Finset.sum_eq_zero_iff_of_nonneg h_outer_nonneg |>.mp htotal k (Finset.mem_univ k)
  -- Now use sum_normSq_eq_zero_iff
  exact (sum_normSq_eq_zero_iff (A k).val i).mp h_inner_zero j

/-! ### Formally Real Instance -/

/-- Quaternionic Hermitian matrices form a formally real Jordan algebra. -/
instance formallyReal : FormallyRealJordan (QuaternionHermitianMatrix n) where
  sum_sq_eq_zero _ A hsum k := sum_sq_eq_zero_imp_all_zero A hsum k

end QuaternionHermitianMatrix

end
