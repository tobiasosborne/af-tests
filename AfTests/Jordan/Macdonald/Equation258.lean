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
