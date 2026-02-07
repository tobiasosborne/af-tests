/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Macdonald.MOperatorProperties

/-!
# Equation (2.58) Base Cases

H-O equation (2.58): For k >= 1, p in X, q in Y:
  T_{x^k}(M_{p,q}(v)) = 1/2 (M_{x^k . p, q}(v) + M_{p, x^k . q}(v))

where "x^k . p" means left multiplication in FA (= prependX).

This file proves base cases where p, q have weight <= 1.
Cases with both p,q starting with x need operator identities
(2.48)/(2.49) applied to FreeJordanAlg; left as future work.

## References

* Hanche-Olsen & Stormer, "Jordan Operator Algebras", (2.58), lines 1326-1377
-/

open FreeJordanAlg FreeAssocMono

/-- (2.58) base case: p = 1, q = 1.
    Both M_op terms reduce to T_{x^{k+1}} v. -/
theorem eq258_one_one (k : ℕ) (v : FreeJordanAlg) :
    T (pow x (k + 1)) (M_op one one v) =
    (1/2 : ℝ) • (M_op (xCons k one) one v + M_op one (xCons k one) v) := by
  simp only [M_op.eq_def, T_apply]
  rw [← two_smul ℝ (mul (pow x (k + 1)) v), smul_smul]; norm_num

/-- (2.58) base case: p = 1, q = y^{j+1}.
    U_bilinear cross terms cancel after mul_comm. -/
theorem eq258_one_yCons (k j : ℕ) (v : FreeJordanAlg) :
    T (pow x (k + 1)) (M_op one (yCons j one) v) =
    (1/2 : ℝ) • (M_op (xCons k one) (yCons j one) v +
                  M_op one (prependX k (yCons j one)) v) := by
  simp only [prependX, M_op.eq_def, U_bilinear_apply, T_apply]
  conv_rhs =>
    rw [show mul (pow y (j + 1)) (pow x (k + 1)) =
      mul (pow x (k + 1)) (pow y (j + 1)) from mul_comm _ _]
  simp only [smul_add, smul_sub, smul_smul]; norm_num; abel

/-- (2.58) base case: p = y^{j+1}, q = 1.
    Symmetric: (2.56) expansion cancels with U_bilinear. -/
theorem eq258_yCons_one (k j : ℕ) (v : FreeJordanAlg) :
    T (pow x (k + 1)) (M_op (yCons j one) one v) =
    (1/2 : ℝ) • (M_op (prependX k (yCons j one)) one v +
                  M_op (yCons j one) (xCons k one) v) := by
  simp only [prependX, M_op.eq_def, U_bilinear_apply, T_apply]
  conv_rhs =>
    rw [show mul (pow y (j + 1)) (pow x (k + 1)) =
      mul (pow x (k + 1)) (pow y (j + 1)) from mul_comm _ _]
  simp only [smul_add, smul_sub, smul_smul]; norm_num; try abel

/-- (2.58) weight≤1, i<k case: T_{x^{k+1}} M_{x^{i+1},y^{j+1}} =
    ½(M_{x^{i+k+2},y^{j+1}} + M_{x^{i+1},x^{k}·y^{j+1}}).
    H-O lines 1336-1344. Uses (2.47), eq258_xCons_yCons_ge, and (2.45). -/
theorem eq258_xCons_yCons_lt (k i j : ℕ) (hik : i < k) (v : FreeJordanAlg) :
    T (pow x (k + 1)) (M_op (xCons i one) (yCons j one) v) =
    (1/2 : ℝ) • (M_op (xCons (k + 1 + i) one) (yCons j one) v +
                  M_op (xCons i one) (xCons k (yCons j one)) v) := by
  -- Step 1: Unfold all M_op terms to U_bilinear/U/T expressions
  conv_lhs => rw [show M_op (xCons i one) (yCons j one) v =
    U_bilinear (pow x (i + 1)) (pow y (j + 1)) v from by rw [M_op.eq_def]]
  conv_rhs => rw [show M_op (xCons (k + 1 + i) one) (yCons j one) v =
    U_bilinear (pow x (k + 1 + i + 1)) (pow y (j + 1)) v from by rw [M_op.eq_def]]
  conv_rhs => rw [show M_op (xCons i one) (xCons k (yCons j one)) v =
    U (pow x (i + 1)) (M_op one (xCons (k - i - 1) (yCons j one)) v) from by
    rw [M_op.eq_def]; simp only [ge_iff_le]; rw [dif_neg (by omega : ¬(k ≤ i))]
    simp only [(by omega : ¬(k = i)), ite_false]; congr 2; omega]
  rw [show M_op one (xCons (k - i - 1) (yCons j one)) v =
    (2 : ℝ) • T (pow x (k - i)) (T (pow y (j + 1)) v)
      - U_bilinear (pow y (j + 1)) (pow x (k - i)) v from by
    rw [M_op.eq_def]; congr 2; omega]
  -- Step 2: Apply (2.47) with a=x, m=i+1, n=k+1, b=y^{j+1}
  have h247 := @JordanAlgebra.operator_identity_247 FreeJordanAlg _
    FreeJordanAlg.x (FreeJordanAlg.pow FreeJordanAlg.y (j + 1)) (i + 1) (k + 1)
  have h247v := LinearMap.ext_iff.mp h247 v
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at h247v
  rw [FJ_L_apply, FJ_L_apply, FJ_jpow_eq_pow, FJ_jpow_eq_pow,
      FJ_U_bilinear_eq, FJ_jpow_eq_pow,
      FJ_U_bilinear_eq, FJ_jpow_eq_pow,
      FJ_U_bilinear_eq, FJ_jpow_eq_pow, FJ_jpow_eq_pow,
      FJ_U_bilinear_eq, FJ_jpow_eq_pow] at h247v
  -- Step 3: Apply eq258_xCons_yCons_ge (i≤k case) for T_{x^{i+1}} term
  have hge := eq258_xCons_yCons_ge i k j (by omega : i ≤ k) v
  rw [show M_op (xCons (i + 1 + k) one) (yCons j one) v =
    U_bilinear (pow x (i + 1 + k + 1)) (pow y (j + 1)) v from by rw [M_op.eq_def]] at hge
  rw [show M_op (xCons k one) (yCons j one) v =
    U_bilinear (pow x (k + 1)) (pow y (j + 1)) v from by rw [M_op.eq_def]] at hge
  rw [show M_op (xCons k one) (xCons i (yCons j one)) v =
    U (pow x (i + 1)) (U_bilinear (pow x (k - i)) (pow y (j + 1)) v) from by
    rw [M_op.eq_def]; simp only [ge_iff_le]; rw [dif_pos (by omega : i ≤ k)]
    simp only [(by omega : ¬(k = i)), ite_false]; congr 2; omega] at hge
  simp only [T_apply] at hge ⊢
  -- Step 4: Apply power_formula_245 with l=k-i, m=n=i+1
  have h245 := @JordanAlgebra.power_formula_245 FreeJordanAlg _
    FreeJordanAlg.x (mul (pow y (j + 1)) v) (k - i) (i + 1) (i + 1)
  simp only [JordanAlgebra.triple_def, FJ_jmul_eq_mul, FJ_jpow_eq_pow] at h245
  rw [show i + 1 + (k - i) = k + 1 from by omega] at h245
  -- Step 5: Expand everything to mul and close with linarith
  simp only [U_bilinear_apply, U] at *
  linarith

/-- U_bilinear(1, b)(v) = T_b(v): bilinearized U with 1 on left is just multiplication. -/
theorem U_bilinear_one_left (b v : FreeJordanAlg) :
    U_bilinear 1 b v = T b v := by
  rw [U_bilinear_comm]; exact U_bilinear_one_right b v

/-- (2.58) weight≤1, i≥k case: T_{x^{k+1}} M_{x^{i+1},y^{j+1}} =
    ½(M_{x^{i+k+2},y^{j+1}} + U_{x^{k+1}} M_{x^{i-k},y^{j+1}}).
    H-O lines 1332-1335. Uses operator_identity_249. -/
theorem eq258_xCons_yCons_ge (k i j : ℕ) (hik : k ≤ i) (v : FreeJordanAlg) :
    T (pow x (k + 1)) (M_op (xCons i one) (yCons j one) v) =
    (1/2 : ℝ) • (M_op (xCons (k + 1 + i) one) (yCons j one) v +
                  M_op (xCons i one) (xCons k (yCons j one)) v) := by
  -- Step 1: Unfold LHS M_op (base case 2.52)
  conv_lhs => rw [show M_op (xCons i one) (yCons j one) v =
    U_bilinear (pow x (i + 1)) (pow y (j + 1)) v from by rw [M_op.eq_def]]
  -- Step 2: Unfold first RHS M_op (base case 2.52)
  conv_rhs => rw [show M_op (xCons (k + 1 + i) one) (yCons j one) v =
    U_bilinear (pow x (k + 1 + i + 1)) (pow y (j + 1)) v from by rw [M_op.eq_def]]
  -- Step 3: Unfold second RHS M_op via (2.53a) + reduce to U_bilinear
  conv_rhs => rw [show M_op (xCons i one) (xCons k (yCons j one)) v =
    U (pow x (k + 1)) (U_bilinear (pow x (i - k)) (pow y (j + 1)) v) from by
    rw [M_op.eq_def]; simp only [ge_iff_le]; rw [dif_pos hik]
    by_cases heq : i = k
    · subst heq
      simp only [Nat.sub_self, ite_true, pow_zero, M_op.eq_def, T_apply,
        U_bilinear_apply, one_mul_eq]
      abel
    · rw [if_neg heq, M_op.eq_def]; congr 1; omega]
  -- Step 4: Apply operator_identity_249
  -- (2.49) with a=x, m=k+1, k'=i-k, b=y^{j+1}:
  -- 2 • T(x^{k+1})(U_bilinear(x^{i+1},y^{j+1})(v))
  --   = U(x^{k+1})(U_bilinear(x^{i-k},y^{j+1})(v)) + U_bilinear(x^{k+i+2},y^{j+1})(v)
  have h249 := @JordanAlgebra.operator_identity_249 FreeJordanAlg _
    FreeJordanAlg.x (FreeJordanAlg.pow FreeJordanAlg.y (j + 1)) (k + 1) (i - k)
  have h249v := LinearMap.ext_iff.mp h249 v
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply] at h249v
  rw [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq, FJ_jpow_eq_pow,
      FJ_U_linear_apply, FJ_U_bilinear_eq, FJ_jpow_eq_pow,
      FJ_U_bilinear_eq, FJ_jpow_eq_pow] at h249v
  rw [show k + 1 + (i - k) = i + 1 from by omega,
      show k + 1 + (k + 1 + (i - k)) = k + 1 + i + 1 from by omega] at h249v
  -- h249v: 2 • T(x^{k+1})(U_bilinear(x^{i+1},y^{j+1})(v)) =
  --        U(x^{k+1})(U_bilinear(x^{i-k},y^{j+1})(v)) + U_bilinear(x^{k+1+i+1},y^{j+1})(v)
  -- Step 5: Conclude by halving and reordering
  simp only [T_apply]
  calc mul (pow x (k + 1)) (U_bilinear (pow x (i + 1)) (pow y (j + 1)) v)
      = (1 / 2 : ℝ) • ((2 : ℝ) • mul (pow x (k + 1))
          (U_bilinear (pow x (i + 1)) (pow y (j + 1)) v)) := by
        rw [smul_smul]; norm_num
    _ = (1 / 2 : ℝ) • (U (pow x (k + 1))
          (U_bilinear (pow x (i - k)) (pow y (j + 1)) v) +
        U_bilinear (pow x (k + 1 + i + 1)) (pow y (j + 1)) v) := by
        congr 1; exact h249v
    _ = (1 / 2 : ℝ) • (U_bilinear (pow x (k + 1 + i + 1)) (pow y (j + 1)) v +
          U (pow x (k + 1)) (U_bilinear (pow x (i - k)) (pow y (j + 1)) v)) := by
        congr 1; abel
