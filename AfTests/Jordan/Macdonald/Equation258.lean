/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Macdonald.MOperatorProperties

/-!
# Equation (2.58)

H-O equation (2.58): For k >= 1, p in X, q in Y:
  T_{x^k}(M_{p,q}(v)) = 1/2 (M_{x^k . p, q}(v) + M_{p, x^k . q}(v))

where "x^k . p" means left multiplication in FA (= prependX).

This file proves:
- Base cases where p, q have weight <= 1 (H-O lines 1332-1344)
- Inductive cases where p or q has weight > 1 (H-O lines 1346-1377)

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
      mul (pow x (k + 1)) (pow y (j + 1)) from FreeJordanAlg.mul_comm _ _]
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
      mul (pow x (k + 1)) (pow y (j + 1)) from FreeJordanAlg.mul_comm _ _]
  simp only [smul_add, smul_sub, smul_smul]; norm_num; try abel

/-- U_bilinear(1, b)(v) = T_b(v): bilinearized U with 1 on left is just multiplication. -/
theorem U_bilinear_one_left (b v : FreeJordanAlg) :
    U_bilinear 1 b v = T b v := by
  rw [U_bilinear_comm]; exact U_bilinear_one_right b v

/-- For powers of the same generator with `i < k`, the bilinearized U operator
    factors as `U_{x^{i+1}} T_{x^{k-i}}`. This is the reusable form of the
    `hkey` calculation used in the weight≤1 `i < k` case. -/
theorem U_bilinear_x_pow_lt_as_U_T (i k : ℕ) (hik : i < k) (w : FreeJordanAlg) :
    U_bilinear (pow x (i + 1)) (pow x (k + 1)) w =
      U (pow x (i + 1)) (T (pow x (k - i)) w) := by
  have hLc : ∀ (l m : ℕ) (w : FreeJordanAlg),
      mul (pow x l) (mul (pow x m) w) = mul (pow x m) (mul (pow x l) w) := by
    intro l m w
    have hcomm := @JordanAlgebra.L_jpow_comm_all FreeJordanAlg _ x l m
    have happ := LinearMap.ext_iff.mp hcomm w
    simp only [FJ_jpow_eq_pow] at happ
    exact happ
  have hprod : ∀ (a : ℕ), mul (pow x a) (pow x a) = pow x (a + a) := by
    intro a
    simpa only [FJ_jmul_eq_mul, FJ_jpow_eq_pow] using
      JordanAlgebra.jpow_add x a a
  have hTU : ∀ (l m : ℕ) (w : FreeJordanAlg),
      mul (pow x l) (U (pow x m) w) = U (pow x m) (mul (pow x l) w) := by
    intro l m w
    simp only [FreeJordanAlg.U]
    rw [show (2 : ℝ) • mul (pow x m) (mul (pow x m) w) -
        mul (mul (pow x m) (pow x m)) w =
      (2 : ℝ) • mul (pow x m) (mul (pow x m) w) +
        (-1 : ℝ) • mul (mul (pow x m) (pow x m)) w from by
      simp [sub_eq_add_neg]]
    rw [mul_add_right, smul_mul_right, smul_mul_right]
    rw [hLc l m (mul (pow x m) w)]
    conv_lhs => arg 1; arg 2; arg 2; rw [hLc l m w]
    rw [hprod m]
    rw [hLc l (m + m) w]
    rw [← hprod m]
    simp [sub_eq_add_neg]
  have hkey :
      U_bilinear (pow x (i + 1)) (pow x (k + 1)) w =
        U (pow x (i + 1)) (mul (pow x (k - i)) w) := by
    have h245 := @JordanAlgebra.power_formula_245 FreeJordanAlg _ x w
      (k - i) (i + 1) (i + 1)
    rw [JordanAlgebra.triple_self_right] at h245
    rw [show i + 1 + (k - i) = k + 1 from by omega] at h245
    rw [show JordanAlgebra.triple (JordanAlgebra.jpow x (k + 1)) w
          (JordanAlgebra.jpow x (i + 1)) =
        JordanAlgebra.U_bilinear_linear (JordanAlgebra.jpow x (k + 1))
          (JordanAlgebra.jpow x (i + 1)) w from rfl] at h245
    rw [show JordanAlgebra.triple (JordanAlgebra.jpow x (i + 1)) w
          (JordanAlgebra.jpow x (k + 1)) =
        JordanAlgebra.U_bilinear_linear (JordanAlgebra.jpow x (i + 1))
          (JordanAlgebra.jpow x (k + 1)) w from rfl] at h245
    simp only [FJ_jmul_eq_mul, FJ_jpow_eq_pow, FJ_U_eq, FJ_U_bilinear_eq] at h245
    rw [U_bilinear_comm (pow x (k + 1)) (pow x (i + 1))] at h245
    rw [two_nsmul] at h245
    have h1 : mul (pow x (k - i)) (U (pow x (i + 1)) w) =
        U_bilinear (pow x (i + 1)) (pow x (k + 1)) w := by
      have h2 : (2 : ℝ) • mul (pow x (k - i)) (U (pow x (i + 1)) w) =
          (2 : ℝ) • U_bilinear (pow x (i + 1)) (pow x (k + 1)) w := by
        rw [two_smul, two_smul]
        exact h245
      have h3 := congr_arg ((1 / 2 : ℝ) • ·) h2
      simp only [smul_smul] at h3
      norm_num at h3
      exact h3
    rw [← h1, hTU (k - i) (i + 1) w]
  rw [T_apply]
  exact hkey

/-- Y-version of `U_bilinear_x_pow_lt_as_U_T`. -/
theorem U_bilinear_y_pow_lt_as_U_T (j l : ℕ) (hjl : j < l) (w : FreeJordanAlg) :
    U_bilinear (pow y (j + 1)) (pow y (l + 1)) w =
      U (pow y (j + 1)) (T (pow y (l - j)) w) := by
  have hLc : ∀ (a b : ℕ) (w : FreeJordanAlg),
      mul (pow y a) (mul (pow y b) w) = mul (pow y b) (mul (pow y a) w) := by
    intro a b w
    have hcomm := @JordanAlgebra.L_jpow_comm_all FreeJordanAlg _ y a b
    have happ := LinearMap.ext_iff.mp hcomm w
    simp only [FJ_jpow_eq_pow] at happ
    exact happ
  have hprod : ∀ (a : ℕ), mul (pow y a) (pow y a) = pow y (a + a) := by
    intro a
    simpa only [FJ_jmul_eq_mul, FJ_jpow_eq_pow] using
      JordanAlgebra.jpow_add y a a
  have hTU : ∀ (a b : ℕ) (w : FreeJordanAlg),
      mul (pow y a) (U (pow y b) w) = U (pow y b) (mul (pow y a) w) := by
    intro a b w
    simp only [FreeJordanAlg.U]
    rw [show (2 : ℝ) • mul (pow y b) (mul (pow y b) w) -
        mul (mul (pow y b) (pow y b)) w =
      (2 : ℝ) • mul (pow y b) (mul (pow y b) w) +
        (-1 : ℝ) • mul (mul (pow y b) (pow y b)) w from by
      simp [sub_eq_add_neg]]
    rw [mul_add_right, smul_mul_right, smul_mul_right]
    rw [hLc a b (mul (pow y b) w)]
    conv_lhs => arg 1; arg 2; arg 2; rw [hLc a b w]
    rw [hprod b]
    rw [hLc a (b + b) w]
    rw [← hprod b]
    simp [sub_eq_add_neg]
  have hkey :
      U_bilinear (pow y (j + 1)) (pow y (l + 1)) w =
        U (pow y (j + 1)) (mul (pow y (l - j)) w) := by
    have h245 := @JordanAlgebra.power_formula_245 FreeJordanAlg _ y w
      (l - j) (j + 1) (j + 1)
    rw [JordanAlgebra.triple_self_right] at h245
    rw [show j + 1 + (l - j) = l + 1 from by omega] at h245
    rw [show JordanAlgebra.triple (JordanAlgebra.jpow y (l + 1)) w
          (JordanAlgebra.jpow y (j + 1)) =
        JordanAlgebra.U_bilinear_linear (JordanAlgebra.jpow y (l + 1))
          (JordanAlgebra.jpow y (j + 1)) w from rfl] at h245
    rw [show JordanAlgebra.triple (JordanAlgebra.jpow y (j + 1)) w
          (JordanAlgebra.jpow y (l + 1)) =
        JordanAlgebra.U_bilinear_linear (JordanAlgebra.jpow y (j + 1))
          (JordanAlgebra.jpow y (l + 1)) w from rfl] at h245
    simp only [FJ_jmul_eq_mul, FJ_jpow_eq_pow, FJ_U_eq, FJ_U_bilinear_eq] at h245
    rw [U_bilinear_comm (pow y (l + 1)) (pow y (j + 1))] at h245
    rw [two_nsmul] at h245
    have h1 : mul (pow y (l - j)) (U (pow y (j + 1)) w) =
        U_bilinear (pow y (j + 1)) (pow y (l + 1)) w := by
      have h2 : (2 : ℝ) • mul (pow y (l - j)) (U (pow y (j + 1)) w) =
          (2 : ℝ) • U_bilinear (pow y (j + 1)) (pow y (l + 1)) w := by
        rw [two_smul, two_smul]
        exact h245
      have h3 := congr_arg ((1 / 2 : ℝ) • ·) h2
      simp only [smul_smul] at h3
      norm_num at h3
      exact h3
    rw [← h1, hTU (l - j) (j + 1) w]
  rw [T_apply]
  exact hkey

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
    · rw [if_neg heq]; simp only [M_op.eq_def, show i - k - 1 + 1 = i - k from by omega]]
  -- Step 4: Apply operator_identity_249
  -- (2.49) with a=x, m=k+1, k'=i-k, b=y^{j+1}:
  -- 2 • T(x^{k+1})(U_bilinear(x^{i+1},y^{j+1})(v))
  --   = U(x^{k+1})(U_bilinear(x^{i-k},y^{j+1})(v)) + U_bilinear(x^{k+i+2},y^{j+1})(v)
  have h249 := @JordanAlgebra.operator_identity_249 FreeJordanAlg _
    FreeJordanAlg.x (FreeJordanAlg.pow FreeJordanAlg.y (j + 1)) (k + 1) (i - k)
  have h249v := LinearMap.ext_iff.mp h249 v
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply] at h249v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq, FJ_U_linear_apply] at h249v
  rw [show k + 1 + (i - k) = i + 1 from by omega,
      show k + 1 + (i + 1) = k + 1 + i + 1 from by omega] at h249v
  -- h249v: 2 • T(x^{k+1})(U_bilinear(x^{i+1},y^{j+1})(v)) =
  --        U(x^{k+1})(U_bilinear(x^{i-k},y^{j+1})(v)) + U_bilinear(x^{k+1+i+1},y^{j+1})(v)
  -- Step 5: Conclude by halving and reordering
  simp only [T_apply] at h249v ⊢
  rw [show mul (pow x (k + 1)) (U_bilinear (pow x (i + 1)) (pow y (j + 1)) v)
      = (1 / 2 : ℝ) • ((2 : ℝ) • mul (pow x (k + 1))
          (U_bilinear (pow x (i + 1)) (pow y (j + 1)) v)) from by rw [smul_smul]; norm_num,
    h249v]
  congr 1; abel

/-- Y-direction weight≤1, j≥l case. Symmetric to `eq258_xCons_yCons_ge`. -/
theorem eq258_yCons_xCons_ge (l j i : ℕ) (hlj : l ≤ j) (v : FreeJordanAlg) :
    T (pow y (l + 1)) (M_op (yCons j one) (xCons i one) v) =
    (1 / 2 : ℝ) • (M_op (yCons (l + 1 + j) one) (xCons i one) v +
                  M_op (yCons j one) (yCons l (xCons i one)) v) := by
  conv_lhs => rw [show M_op (yCons j one) (xCons i one) v =
    U_bilinear (pow y (j + 1)) (pow x (i + 1)) v from by rw [M_op.eq_def]]
  conv_rhs => rw [show M_op (yCons (l + 1 + j) one) (xCons i one) v =
    U_bilinear (pow y (l + 1 + j + 1)) (pow x (i + 1)) v from by rw [M_op.eq_def]]
  conv_rhs => rw [show M_op (yCons j one) (yCons l (xCons i one)) v =
    U (pow y (l + 1)) (U_bilinear (pow y (j - l)) (pow x (i + 1)) v) from by
    rw [M_op.eq_def]; simp only [ge_iff_le]; rw [dif_pos hlj]
    by_cases heq : j = l
    · subst heq
      simp only [Nat.sub_self, ite_true, pow_zero, M_op.eq_def, T_apply,
        U_bilinear_apply, one_mul_eq]
      abel
    · rw [if_neg heq]; simp only [M_op.eq_def, show j - l - 1 + 1 = j - l from by omega]]
  have h249 := @JordanAlgebra.operator_identity_249 FreeJordanAlg _
    FreeJordanAlg.y (FreeJordanAlg.pow FreeJordanAlg.x (i + 1)) (l + 1) (j - l)
  have h249v := LinearMap.ext_iff.mp h249 v
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply] at h249v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq, FJ_U_linear_apply] at h249v
  rw [show l + 1 + (j - l) = j + 1 from by omega,
      show l + 1 + (j + 1) = l + 1 + j + 1 from by omega] at h249v
  simp only [T_apply] at h249v ⊢
  rw [show mul (pow y (l + 1)) (U_bilinear (pow y (j + 1)) (pow x (i + 1)) v)
      = (1 / 2 : ℝ) • ((2 : ℝ) • mul (pow y (l + 1))
          (U_bilinear (pow y (j + 1)) (pow x (i + 1)) v)) from by rw [smul_smul]; norm_num,
    h249v]
  congr 1
  abel

/-- Y-direction weight≤1, j<l case. Symmetric to `eq258_xCons_yCons_lt`. -/
theorem eq258_yCons_xCons_lt (l j i : ℕ) (hjl : j < l) (v : FreeJordanAlg) :
    T (pow y (l + 1)) (M_op (yCons j one) (xCons i one) v) =
    (1 / 2 : ℝ) • (M_op (yCons (l + 1 + j) one) (xCons i one) v +
                  M_op (yCons j one) (yCons l (xCons i one)) v) := by
  conv_lhs => rw [show M_op (yCons j one) (xCons i one) v =
    U_bilinear (pow y (j + 1)) (pow x (i + 1)) v from by rw [M_op.eq_def]]
  conv_rhs => rw [show M_op (yCons (l + 1 + j) one) (xCons i one) v =
    U_bilinear (pow y (l + 1 + j + 1)) (pow x (i + 1)) v from by rw [M_op.eq_def]]
  conv_rhs => rw [show M_op (yCons j one) (yCons l (xCons i one)) v =
    U (pow y (j + 1)) (M_op one (yCons (l - j - 1) (xCons i one)) v) from by
    rw [M_op.eq_def]; simp only [ge_iff_le]; rw [dif_neg (by omega : ¬ l ≤ j)]
    simp only [show ¬ l = j from by omega, ↓reduceIte]]
  rw [show M_op one (yCons (l - j - 1) (xCons i one)) v =
    (2 : ℝ) • T (pow y (l - j)) (T (pow x (i + 1)) v)
      - U_bilinear (pow x (i + 1)) (pow y (l - j)) v from by
    simp only [M_op.eq_def, show l - j - 1 + 1 = l - j from by omega]]
  have h247 := @JordanAlgebra.operator_identity_247 FreeJordanAlg _
    FreeJordanAlg.y (FreeJordanAlg.pow FreeJordanAlg.x (i + 1)) (j + 1) (l + 1)
  have h247v := LinearMap.ext_iff.mp h247 v
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at h247v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq] at h247v
  rw [show j + 1 + (l + 1) = l + 1 + j + 1 from by omega] at h247v
  have hge := eq258_yCons_xCons_ge j l i (by omega : j ≤ l) v
  rw [show M_op (yCons (j + 1 + l) one) (xCons i one) v =
    U_bilinear (pow y (j + 1 + l + 1)) (pow x (i + 1)) v from by rw [M_op.eq_def]] at hge
  rw [show M_op (yCons l one) (xCons i one) v =
    U_bilinear (pow y (l + 1)) (pow x (i + 1)) v from by rw [M_op.eq_def]] at hge
  rw [show M_op (yCons l one) (yCons j (xCons i one)) v =
    U (pow y (j + 1)) (U_bilinear (pow y (l - j)) (pow x (i + 1)) v) from by
    rw [M_op.eq_def]; simp only [ge_iff_le]; rw [dif_pos (by omega : j ≤ l)]
    simp only [show ¬ l = j from by omega, ↓reduceIte]
    simp only [M_op.eq_def, show l - j - 1 + 1 = l - j from by omega]] at hge
  simp only [T_apply] at hge ⊢
  have hkey : ∀ w : FreeJordanAlg,
      U_bilinear (pow y (j + 1)) (pow y (l + 1)) w =
      U (pow y (j + 1)) (mul (pow y (l - j)) w) := by
    intro w
    simpa [T_apply] using U_bilinear_y_pow_lt_as_U_T j l hjl w
  simp only [T_apply] at h247v
  rw [hge] at h247v
  rw [show j + 1 + l + 1 = l + 1 + j + 1 from by omega] at h247v
  rw [hkey] at h247v
  have hU_sub : ∀ (a b c : FreeJordanAlg),
      U a (b - c) = U a b - U a c := by
    intro a b c
    simp only [FreeJordanAlg.U]
    rw [show b - c = b + (-1 : ℝ) • c from by simp [sub_eq_add_neg]]
    rw [mul_add_right, smul_mul_right, mul_add_right, smul_mul_right,
        mul_add_right, smul_mul_right]
    simp only [smul_add, smul_smul]
    norm_num
    abel
  have hU_smul : ∀ (a : FreeJordanAlg) (r : ℝ) (b : FreeJordanAlg),
      U a (r • b) = r • U a b := by
    intro a r b
    rw [← FJ_U_eq, ← FJ_U_eq]
    exact JordanAlgebra.U_smul_right a r b
  rw [hU_sub, hU_smul, U_bilinear_comm (pow x (i + 1)) (pow y (l - j))]
  suffices h_suff :
      (1 / 2 : ℝ) • (U_bilinear (pow y (l + 1 + j + 1)) (pow x (i + 1)) v +
          ((2 : ℝ) • U (pow y (j + 1)) (mul (pow y (l - j)) (mul (pow x (i + 1)) v)) -
            U (pow y (j + 1)) (U_bilinear (pow y (l - j)) (pow x (i + 1)) v))) +
        (1 / 2 : ℝ) • (U_bilinear (pow y (l + 1 + j + 1)) (pow x (i + 1)) v +
          U (pow y (j + 1)) (U_bilinear (pow y (l - j)) (pow x (i + 1)) v)) =
      U (pow y (j + 1)) (mul (pow y (l - j)) (mul (pow x (i + 1)) v)) +
        U_bilinear (pow y (l + 1 + j + 1)) (pow x (i + 1)) v by
    exact add_right_cancel (h247v.trans h_suff.symm)
  module

/-- X-direction weight≤1 boundary, `i ≥ k`: the second argument is `1`.
    This is the `b = 1` specialization of H-O (2.49). -/
theorem eq258_xCons_one_ge (k i : ℕ) (hik : k ≤ i) (v : FreeJordanAlg) :
    T (pow x (k + 1)) (M_op (xCons i one) one v) =
    (1 / 2 : ℝ) • (M_op (xCons (k + 1 + i) one) one v +
                  M_op (xCons i one) (xCons k one) v) := by
  conv_lhs => rw [show M_op (xCons i one) one v =
    U_bilinear (pow x (i + 1)) 1 v from by
      rw [M_op.eq_def]
      exact (U_bilinear_one_right (pow x (i + 1)) v).symm]
  conv_rhs => rw [show M_op (xCons (k + 1 + i) one) one v =
    U_bilinear (pow x (k + 1 + i + 1)) 1 v from by
      rw [M_op.eq_def]
      exact (U_bilinear_one_right (pow x (k + 1 + i + 1)) v).symm]
  conv_rhs => rw [show M_op (xCons i one) (xCons k one) v =
    U (pow x (k + 1)) (U_bilinear (pow x (i - k)) 1 v) from by
    rw [M_op.eq_def]
    simp only [ge_iff_le]
    rw [dif_pos hik]
    by_cases heq : i = k
    · subst heq
      simp only [Nat.sub_self, ite_true, pow_zero, M_op.eq_def,
        U_bilinear_apply, one_mul_eq]
      abel
    · rw [if_neg heq]
      rw [show M_op (xCons (i - k - 1) one) one v = T (pow x (i - k)) v from by
        simp only [M_op.eq_def]
        rw [show i - k - 1 + 1 = i - k from by omega]]
      rw [U_bilinear_one_right]]
  have h249 := @JordanAlgebra.operator_identity_249 FreeJordanAlg _
    FreeJordanAlg.x (1 : FreeJordanAlg) (k + 1) (i - k)
  have h249v := LinearMap.ext_iff.mp h249 v
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply] at h249v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq, FJ_U_linear_apply] at h249v
  rw [show k + 1 + (i - k) = i + 1 from by omega,
      show k + 1 + (i + 1) = k + 1 + i + 1 from by omega] at h249v
  simp only [T_apply] at h249v ⊢
  rw [show mul (pow x (k + 1)) (U_bilinear (pow x (i + 1)) 1 v)
      = (1 / 2 : ℝ) • ((2 : ℝ) • mul (pow x (k + 1))
          (U_bilinear (pow x (i + 1)) 1 v)) from by
        rw [smul_smul]
        norm_num,
    h249v]
  congr 1
  abel

/-- X-direction weight≤1 boundary, `i < k`: the second argument is `1`. -/
theorem eq258_xCons_one_lt (k i : ℕ) (hik : i < k) (v : FreeJordanAlg) :
    T (pow x (k + 1)) (M_op (xCons i one) one v) =
    (1 / 2 : ℝ) • (M_op (xCons (k + 1 + i) one) one v +
                  M_op (xCons i one) (xCons k one) v) := by
  conv_lhs => rw [show M_op (xCons i one) one v =
    U_bilinear (pow x (i + 1)) 1 v from by
      rw [M_op.eq_def]
      exact (U_bilinear_one_right (pow x (i + 1)) v).symm]
  conv_rhs => rw [show M_op (xCons (k + 1 + i) one) one v =
    U_bilinear (pow x (k + 1 + i + 1)) 1 v from by
      rw [M_op.eq_def]
      exact (U_bilinear_one_right (pow x (k + 1 + i + 1)) v).symm]
  conv_rhs => rw [show M_op (xCons i one) (xCons k one) v =
    U (pow x (i + 1)) (U_bilinear (pow x (k - i)) 1 v) from by
    rw [M_op.eq_def]
    simp only [ge_iff_le]
    rw [dif_neg (by omega : ¬ k ≤ i)]
    simp only [show ¬ k = i from by omega, ↓reduceIte]
    rw [show M_op one (xCons (k - i - 1) one) v = T (pow x (k - i)) v from by
      simp only [M_op.eq_def]
      rw [show k - i - 1 + 1 = k - i from by omega]]
    rw [U_bilinear_one_right]]
  have h247 := @JordanAlgebra.operator_identity_247 FreeJordanAlg _
    FreeJordanAlg.x (1 : FreeJordanAlg) (i + 1) (k + 1)
  have h247v := LinearMap.ext_iff.mp h247 v
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at h247v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq] at h247v
  rw [show i + 1 + (k + 1) = k + 1 + i + 1 from by omega] at h247v
  have hge := eq258_xCons_one_ge i k (by omega : i ≤ k) v
  rw [show M_op (xCons (i + 1 + k) one) one v =
    U_bilinear (pow x (i + 1 + k + 1)) 1 v from by
      rw [M_op.eq_def]
      exact (U_bilinear_one_right (pow x (i + 1 + k + 1)) v).symm] at hge
  rw [show M_op (xCons k one) one v =
    U_bilinear (pow x (k + 1)) 1 v from by
      rw [M_op.eq_def]
      exact (U_bilinear_one_right (pow x (k + 1)) v).symm] at hge
  rw [show M_op (xCons k one) (xCons i one) v =
    U (pow x (i + 1)) (U_bilinear (pow x (k - i)) 1 v) from by
    rw [M_op.eq_def]
    simp only [ge_iff_le]
    rw [dif_pos (by omega : i ≤ k)]
    simp only [show ¬ k = i from by omega, ↓reduceIte]
    rw [show M_op (xCons (k - i - 1) one) one v = T (pow x (k - i)) v from by
      simp only [M_op.eq_def]
      rw [show k - i - 1 + 1 = k - i from by omega]]
    rw [U_bilinear_one_right]] at hge
  simp only [T_apply] at hge ⊢
  have hkey : ∀ w : FreeJordanAlg,
      U_bilinear (pow x (i + 1)) (pow x (k + 1)) w =
      U (pow x (i + 1)) (mul (pow x (k - i)) w) := by
    intro w
    simpa [T_apply] using U_bilinear_x_pow_lt_as_U_T i k hik w
  simp only [T_apply] at h247v
  rw [hge] at h247v
  rw [show i + 1 + k + 1 = k + 1 + i + 1 from by omega] at h247v
  rw [hkey] at h247v
  rw [U_bilinear_one_right] at h247v
  simp only [T_apply, one_mul_eq] at h247v
  rw [U_bilinear_one_right (pow x (i + 1)) v]
  suffices h_suff :
      (1 / 2 : ℝ) • (U_bilinear (pow x (k + 1 + i + 1)) 1 v +
          U (pow x (i + 1)) (U_bilinear (pow x (k - i)) 1 v)) +
        (1 / 2 : ℝ) • (U_bilinear (pow x (k + 1 + i + 1)) 1 v +
          U (pow x (i + 1)) (U_bilinear (pow x (k - i)) 1 v)) =
      U (pow x (i + 1)) (mul (pow x (k - i)) v) +
        U_bilinear (pow x (k + 1 + i + 1)) 1 v by
    exact add_right_cancel (h247v.trans h_suff.symm)
  simp only [U_bilinear_one_right, T_apply]
  module

/-- Y-direction weight≤1 boundary, `j ≥ l`: the second argument is `1`. -/
theorem eq258_yCons_one_ge (l j : ℕ) (hlj : l ≤ j) (v : FreeJordanAlg) :
    T (pow y (l + 1)) (M_op (yCons j one) one v) =
    (1 / 2 : ℝ) • (M_op (yCons (l + 1 + j) one) one v +
                  M_op (yCons j one) (yCons l one) v) := by
  conv_lhs => rw [show M_op (yCons j one) one v =
    U_bilinear (pow y (j + 1)) 1 v from by
      rw [M_op.eq_def]
      exact (U_bilinear_one_right (pow y (j + 1)) v).symm]
  conv_rhs => rw [show M_op (yCons (l + 1 + j) one) one v =
    U_bilinear (pow y (l + 1 + j + 1)) 1 v from by
      rw [M_op.eq_def]
      exact (U_bilinear_one_right (pow y (l + 1 + j + 1)) v).symm]
  conv_rhs => rw [show M_op (yCons j one) (yCons l one) v =
    U (pow y (l + 1)) (U_bilinear (pow y (j - l)) 1 v) from by
    rw [M_op.eq_def]
    simp only [ge_iff_le]
    rw [dif_pos hlj]
    by_cases heq : j = l
    · subst heq
      simp only [Nat.sub_self, ite_true, pow_zero, M_op.eq_def,
        U_bilinear_apply, one_mul_eq]
      abel
    · rw [if_neg heq]
      rw [show M_op (yCons (j - l - 1) one) one v = T (pow y (j - l)) v from by
        simp only [M_op.eq_def]
        rw [show j - l - 1 + 1 = j - l from by omega]]
      rw [U_bilinear_one_right]]
  have h249 := @JordanAlgebra.operator_identity_249 FreeJordanAlg _
    FreeJordanAlg.y (1 : FreeJordanAlg) (l + 1) (j - l)
  have h249v := LinearMap.ext_iff.mp h249 v
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply] at h249v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq, FJ_U_linear_apply] at h249v
  rw [show l + 1 + (j - l) = j + 1 from by omega,
      show l + 1 + (j + 1) = l + 1 + j + 1 from by omega] at h249v
  simp only [T_apply] at h249v ⊢
  rw [show mul (pow y (l + 1)) (U_bilinear (pow y (j + 1)) 1 v)
      = (1 / 2 : ℝ) • ((2 : ℝ) • mul (pow y (l + 1))
          (U_bilinear (pow y (j + 1)) 1 v)) from by
        rw [smul_smul]
        norm_num,
    h249v]
  congr 1
  abel

/-- Y-direction weight≤1 boundary, `j < l`: the second argument is `1`. -/
theorem eq258_yCons_one_lt (l j : ℕ) (hjl : j < l) (v : FreeJordanAlg) :
    T (pow y (l + 1)) (M_op (yCons j one) one v) =
    (1 / 2 : ℝ) • (M_op (yCons (l + 1 + j) one) one v +
                  M_op (yCons j one) (yCons l one) v) := by
  conv_lhs => rw [show M_op (yCons j one) one v =
    U_bilinear (pow y (j + 1)) 1 v from by
      rw [M_op.eq_def]
      exact (U_bilinear_one_right (pow y (j + 1)) v).symm]
  conv_rhs => rw [show M_op (yCons (l + 1 + j) one) one v =
    U_bilinear (pow y (l + 1 + j + 1)) 1 v from by
      rw [M_op.eq_def]
      exact (U_bilinear_one_right (pow y (l + 1 + j + 1)) v).symm]
  conv_rhs => rw [show M_op (yCons j one) (yCons l one) v =
    U (pow y (j + 1)) (U_bilinear (pow y (l - j)) 1 v) from by
    rw [M_op.eq_def]
    simp only [ge_iff_le]
    rw [dif_neg (by omega : ¬ l ≤ j)]
    simp only [show ¬ l = j from by omega, ↓reduceIte]
    rw [show M_op one (yCons (l - j - 1) one) v = T (pow y (l - j)) v from by
      simp only [M_op.eq_def]
      rw [show l - j - 1 + 1 = l - j from by omega]]
    rw [U_bilinear_one_right]]
  have h247 := @JordanAlgebra.operator_identity_247 FreeJordanAlg _
    FreeJordanAlg.y (1 : FreeJordanAlg) (j + 1) (l + 1)
  have h247v := LinearMap.ext_iff.mp h247 v
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at h247v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq] at h247v
  rw [show j + 1 + (l + 1) = l + 1 + j + 1 from by omega] at h247v
  have hge := eq258_yCons_one_ge j l (by omega : j ≤ l) v
  rw [show M_op (yCons (j + 1 + l) one) one v =
    U_bilinear (pow y (j + 1 + l + 1)) 1 v from by
      rw [M_op.eq_def]
      exact (U_bilinear_one_right (pow y (j + 1 + l + 1)) v).symm] at hge
  rw [show M_op (yCons l one) one v =
    U_bilinear (pow y (l + 1)) 1 v from by
      rw [M_op.eq_def]
      exact (U_bilinear_one_right (pow y (l + 1)) v).symm] at hge
  rw [show M_op (yCons l one) (yCons j one) v =
    U (pow y (j + 1)) (U_bilinear (pow y (l - j)) 1 v) from by
    rw [M_op.eq_def]
    simp only [ge_iff_le]
    rw [dif_pos (by omega : j ≤ l)]
    simp only [show ¬ l = j from by omega, ↓reduceIte]
    rw [show M_op (yCons (l - j - 1) one) one v = T (pow y (l - j)) v from by
      simp only [M_op.eq_def]
      rw [show l - j - 1 + 1 = l - j from by omega]]
    rw [U_bilinear_one_right]] at hge
  simp only [T_apply] at hge ⊢
  have hkey : ∀ w : FreeJordanAlg,
      U_bilinear (pow y (j + 1)) (pow y (l + 1)) w =
      U (pow y (j + 1)) (mul (pow y (l - j)) w) := by
    intro w
    simpa [T_apply] using U_bilinear_y_pow_lt_as_U_T j l hjl w
  simp only [T_apply] at h247v
  rw [hge] at h247v
  rw [show j + 1 + l + 1 = l + 1 + j + 1 from by omega] at h247v
  rw [hkey] at h247v
  rw [U_bilinear_one_right] at h247v
  simp only [T_apply, one_mul_eq] at h247v
  rw [U_bilinear_one_right (pow y (j + 1)) v]
  suffices h_suff :
      (1 / 2 : ℝ) • (U_bilinear (pow y (l + 1 + j + 1)) 1 v +
          U (pow y (j + 1)) (U_bilinear (pow y (l - j)) 1 v)) +
        (1 / 2 : ℝ) • (U_bilinear (pow y (l + 1 + j + 1)) 1 v +
          U (pow y (j + 1)) (U_bilinear (pow y (l - j)) 1 v)) =
      U (pow y (j + 1)) (mul (pow y (l - j)) v) +
        U_bilinear (pow y (l + 1 + j + 1)) 1 v by
    exact add_right_cancel (h247v.trans h_suff.symm)
  simp only [U_bilinear_one_right, T_apply]
  module

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
    simp only [show ¬(k = i) from by omega, ↓reduceIte]]
  rw [show M_op one (xCons (k - i - 1) (yCons j one)) v =
    (2 : ℝ) • T (pow x (k - i)) (T (pow y (j + 1)) v)
      - U_bilinear (pow y (j + 1)) (pow x (k - i)) v from by
    simp only [M_op.eq_def, show k - i - 1 + 1 = k - i from by omega]]
  -- Step 2: Apply (2.47) with a=x, m=i+1, n=k+1, b=y^{j+1}
  have h247 := @JordanAlgebra.operator_identity_247 FreeJordanAlg _
    FreeJordanAlg.x (FreeJordanAlg.pow FreeJordanAlg.y (j + 1)) (i + 1) (k + 1)
  have h247v := LinearMap.ext_iff.mp h247 v
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at h247v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq] at h247v
  rw [show i + 1 + (k + 1) = k + 1 + i + 1 from by omega] at h247v
  -- Step 3: Apply eq258_xCons_yCons_ge (i≤k case) for T_{x^{i+1}} term
  have hge := eq258_xCons_yCons_ge i k j (by omega : i ≤ k) v
  rw [show M_op (xCons (i + 1 + k) one) (yCons j one) v =
    U_bilinear (pow x (i + 1 + k + 1)) (pow y (j + 1)) v from by rw [M_op.eq_def]] at hge
  rw [show M_op (xCons k one) (yCons j one) v =
    U_bilinear (pow x (k + 1)) (pow y (j + 1)) v from by rw [M_op.eq_def]] at hge
  rw [show M_op (xCons k one) (xCons i (yCons j one)) v =
    U (pow x (i + 1)) (U_bilinear (pow x (k - i)) (pow y (j + 1)) v) from by
    rw [M_op.eq_def]; simp only [ge_iff_le]; rw [dif_pos (by omega : i ≤ k)]
    simp only [show ¬(k = i) from by omega, ↓reduceIte]
    simp only [M_op.eq_def, show k - i - 1 + 1 = k - i from by omega]] at hge
  simp only [T_apply] at hge ⊢
  -- Step 4a: T∘U commutation for powers of same element
  -- H-O 2.4.5: L(x^l) commutes with U(x^m) since U = 2L²-L_{sq}, all L's commute
  have hLc : ∀ (a b : ℕ) (v : FreeJordanAlg),
      mul (pow x a) (mul (pow x b) v) = mul (pow x b) (mul (pow x a) v) := by
    intro a b v
    have hcomm := @JordanAlgebra.L_jpow_comm_all FreeJordanAlg _ x a b
    -- Extract element-level from operator commutation
    have h := LinearMap.ext_iff.mp hcomm v
    simp only [FJ_jpow_eq_pow] at h
    exact h
  have hprod : ∀ (a : ℕ), mul (pow x a) (pow x a) = pow x (a + a) := by
    intro a
    have h := JordanAlgebra.jpow_add (J := FreeJordanAlg) x a a
    simp only [FJ_jmul_eq_mul, FJ_jpow_eq_pow] at h
    exact h
  have hTU : ∀ (l m : ℕ) (w : FreeJordanAlg),
      mul (pow x l) (U (pow x m) w) = U (pow x m) (mul (pow x l) w) := by
    intro l m w
    simp only [FreeJordanAlg.U]
    -- Distribute mul(x^l) over 2•A - B
    rw [show (2:ℝ) • mul (pow x m) (mul (pow x m) w) - mul (mul (pow x m) (pow x m)) w =
      (2:ℝ) • mul (pow x m) (mul (pow x m) w) + (-1:ℝ) • mul (mul (pow x m) (pow x m)) w from by
      simp [sub_eq_add_neg]]
    rw [mul_add_right, smul_mul_right, smul_mul_right]
    -- First term: mul(x^l)(mul(x^m)(mul(x^m)(w))) → mul(x^m)(mul(x^m)(mul(x^l)(w)))
    rw [hLc l m (mul (pow x m) w)]
    conv_lhs => arg 1; arg 2; arg 2; rw [hLc l m w]
    -- Second term: mul(x^l)(mul(x^{2m})(w)) → mul(x^{2m})(mul(x^l)(w))
    rw [hprod m]; rw [hLc l (m + m) w]; rw [← hprod m]
    -- Now LHS = RHS, fold back sub
    simp [sub_eq_add_neg]
  -- Step 4b: hkey from power_formula_245 + hTU
  -- U_bi(x^{i+1},x^{k+1})(w) = U(x^{i+1})(mul(x^{k-i})(w))
  have hkey : ∀ w : FreeJordanAlg,
      U_bilinear (pow x (i + 1)) (pow x (k + 1)) w =
      U (pow x (i + 1)) (mul (pow x (k - i)) w) := by
    intro w
    have h245 := @JordanAlgebra.power_formula_245 FreeJordanAlg _ x w (k - i) (i + 1) (i + 1)
    rw [JordanAlgebra.triple_self_right] at h245
    rw [show i + 1 + (k - i) = k + 1 from by omega] at h245
    rw [show JordanAlgebra.triple (JordanAlgebra.jpow x (k + 1)) w (JordanAlgebra.jpow x (i + 1)) =
      JordanAlgebra.U_bilinear_linear (JordanAlgebra.jpow x (k + 1)) (JordanAlgebra.jpow x (i + 1)) w
      from rfl] at h245
    rw [show JordanAlgebra.triple (JordanAlgebra.jpow x (i + 1)) w (JordanAlgebra.jpow x (k + 1)) =
      JordanAlgebra.U_bilinear_linear (JordanAlgebra.jpow x (i + 1)) (JordanAlgebra.jpow x (k + 1)) w
      from rfl] at h245
    simp only [FJ_jmul_eq_mul, FJ_jpow_eq_pow, FJ_U_eq, FJ_U_bilinear_eq] at h245
    rw [U_bilinear_comm (pow x (k + 1)) (pow x (i + 1))] at h245
    -- Cancel the factor of 2: nsmul 2 A = A + A = B + B → 2•A = 2•B → A = B
    rw [two_nsmul] at h245
    have h1 : mul (pow x (k - i)) (U (pow x (i + 1)) w) =
        U_bilinear (pow x (i + 1)) (pow x (k + 1)) w := by
      have h2 : (2:ℝ) • mul (pow x (k - i)) (U (pow x (i + 1)) w) =
        (2:ℝ) • U_bilinear (pow x (i + 1)) (pow x (k + 1)) w := by
        rw [two_smul, two_smul]; exact h245
      have h3 := congr_arg ((1/2 : ℝ) • ·) h2
      simp only [smul_smul] at h3; norm_num at h3; exact h3
    rw [← h1, hTU (k - i) (i + 1) w]
  -- Step 4c: Endgame — combine h247v, hge, hkey
  simp only [T_apply] at h247v
  rw [hge] at h247v
  rw [show i + 1 + k + 1 = k + 1 + i + 1 from by omega] at h247v
  rw [hkey] at h247v
  -- Expand U linearity on goal RHS
  have hU_sub : ∀ (a b c : FreeJordanAlg),
      U a (b - c) = U a b - U a c := by
    intro a b c
    simp only [FreeJordanAlg.U]
    rw [show b - c = b + (-1:ℝ) • c from by simp [sub_eq_add_neg]]
    rw [mul_add_right, smul_mul_right, mul_add_right, smul_mul_right,
        mul_add_right, smul_mul_right]
    simp only [smul_add, smul_smul]; norm_num; abel
  have hU_smul : ∀ (a : FreeJordanAlg) (r : ℝ) (b : FreeJordanAlg),
      U a (r • b) = r • U a b := by
    intro a r b
    rw [← FJ_U_eq, ← FJ_U_eq]
    exact JordanAlgebra.U_smul_right a r b
  rw [hU_sub, hU_smul, U_bilinear_comm (pow y (j + 1)) (pow x (k - i))]
  -- Endgame: from h247v and the goal, both plus (1/2)•(B+C) give E+B.
  -- So they're equal by add_right_cancel.
  suffices h_suff :
      (1/2 : ℝ) • (U_bilinear (pow x (k + 1 + i + 1)) (pow y (j + 1)) v +
          ((2:ℝ) • U (pow x (i + 1)) (mul (pow x (k - i)) (mul (pow y (j + 1)) v)) -
            U (pow x (i + 1)) (U_bilinear (pow x (k - i)) (pow y (j + 1)) v))) +
        (1/2 : ℝ) • (U_bilinear (pow x (k + 1 + i + 1)) (pow y (j + 1)) v +
          U (pow x (i + 1)) (U_bilinear (pow x (k - i)) (pow y (j + 1)) v)) =
      U (pow x (i + 1)) (mul (pow x (k - i)) (mul (pow y (j + 1)) v)) +
        U_bilinear (pow x (k + 1 + i + 1)) (pow y (j + 1)) v by
    exact add_right_cancel (h247v.trans h_suff.symm)
  module

/-! ### Linearity of T over sub/smul — needed for weight > 1 proofs -/

/-- T distributes over subtraction: T_a(b - c) = T_a(b) - T_a(c). -/
theorem T_sub (a b c : FreeJordanAlg) : T a (b - c) = T a b - T a c := by
  simp only [T_apply, sub_eq_add_neg]
  rw [mul_add_right]
  congr 1
  rw [show (-c : FreeJordanAlg) = (-1 : ℝ) • c from by simp]
  rw [smul_mul_right]; simp

/-- T distributes over scalar multiplication: T_a(r • b) = r • T_a(b). -/
theorem T_smul' (a : FreeJordanAlg) (r : ℝ) (b : FreeJordanAlg) :
    T a (r • b) = r • T a b := by
  simp only [T_apply]; exact smul_mul_right r a b

/-- X-direction instance of H-O (2.58). The side conditions `p ∈ X`, `q ∈ Y`
    are tracked by the callers, not by this proposition. -/
def Eq258X (k : ℕ) (p q : FreeAssocMono) : Prop :=
  ∀ v : FreeJordanAlg,
    T (pow x (k + 1)) (M_op p q v) =
      (1 / 2 : ℝ) • (M_op (prependX k p) q v + M_op p (prependX k q) v)

/-- X-direction helper-family where the right multiplication is intentionally
    left unmerged as `xCons k q`. This is the raw shape produced by the current
    `M_op` recurrence helpers in the reversed-orientation lower-pair branch. -/
def Eq258XRawRight (k : ℕ) (p q : FreeAssocMono) : Prop :=
  ∀ v : FreeJordanAlg,
    T (pow x (k + 1)) (M_op p q v) =
      (1 / 2 : ℝ) • (M_op p (xCons k q) v + M_op (xCons k p) q v)

/-- Y-direction companion to H-O (2.58), obtained by swapping `x` and `y`.
    The side conditions `p ∈ Y`, `q ∈ X` are tracked by the callers. -/
def Eq258Y (j : ℕ) (p q : FreeAssocMono) : Prop :=
  ∀ v : FreeJordanAlg,
    T (pow y (j + 1)) (M_op p q v) =
      (1 / 2 : ℝ) • (M_op (prependY j p) q v + M_op p (prependY j q) v)

/-- Y-direction helper-family where the right multiplication is intentionally
    left unmerged as `yCons j q`, symmetric to `Eq258XRawRight`. -/
def Eq258YRawRight (j : ℕ) (p q : FreeAssocMono) : Prop :=
  ∀ v : FreeJordanAlg,
    T (pow y (j + 1)) (M_op p q v) =
      (1 / 2 : ℝ) • (M_op p (yCons j q) v + M_op (yCons j p) q v)

/-- Weight-indexed induction package for the eventual simultaneous Eq(2.58)
    driver. It ranges over the total `FreeAssocMono` syntax, not just WF inputs,
    because the recursive `M_op` equations generate unmerged products such as
    `xCons i s` even when `s ∈ X`. -/
structure Eq258DriverIH (n : ℕ) : Prop where
  x : ∀ (k : ℕ) (p q : FreeAssocMono), p.weight + q.weight < n → Eq258X k p q
  y : ∀ (j : ℕ) (p q : FreeAssocMono), p.weight + q.weight < n → Eq258Y j p q
  rawRight :
    ∀ (k : ℕ) (p q : FreeAssocMono), p.weight + q.weight < n → Eq258XRawRight k p q
  rawRightY :
    ∀ (j : ℕ) (p q : FreeAssocMono), p.weight + q.weight < n → Eq258YRawRight j p q

/-- Same-weight boundary package for the Eq(2.58) driver.

The long one-argument boundary recurrences do not decrease total block weight:
expanding `M(xCons i r, 1)` exposes the swapped term `M(r, xCons i 1)`, with
the same total weight as the target. This layer records exactly those
same-weight swapped facts, while strict lower-weight facts remain in
`Eq258DriverIH`. -/
structure Eq258DriverLayer (n : ℕ) : Prop where
  lower : Eq258DriverIH n
  xBoundarySwap :
    ∀ (k i m : ℕ) (r' : FreeAssocMono),
      (yCons m r').weight + (xCons i one).weight = n →
        Eq258X k (yCons m r') (xCons i one)
  yBoundarySwap :
    ∀ (l j m : ℕ) (r' : FreeAssocMono),
      (xCons m r').weight + (yCons j one).weight = n →
        Eq258Y l (xCons m r') (yCons j one)

/-- Well-formed current-weight driver layer for the long boundary swaps.

This is closer to H-O's proof than `Eq258DriverLayer`: in the x-boundary case
`yCons m r'` is well-formed only when `r' ∈ X`, and in the y-boundary case
`xCons m r'` is well-formed only when `r' ∈ Y`. The pure-tail cases are handled
by the weight≤1 swapped base lemmas, so this layer only asks for genuinely long
tails. -/
structure Eq258DriverWFLayer (n : ℕ) : Prop where
  lower : Eq258DriverIH n
  xBoundarySwapLong :
    ∀ (k i m l : ℕ) (r' : FreeAssocMono),
      (yCons m (xCons l r')).weight + (xCons i one).weight = n →
        Eq258X k (yCons m (xCons l r')) (xCons i one)
  yBoundarySwapLong :
    ∀ (l j m nTail : ℕ) (r' : FreeAssocMono),
      (xCons m (yCons nTail r')).weight + (yCons j one).weight = n →
        Eq258Y l (xCons m (yCons nTail r')) (yCons j one)

/-- The y-generator obligation consumed by the x-direction inductive helpers
    when `p = yCons m r'` and `q = s`. For well-formed H-O applications,
    callers should supply this from `Eq258Y j (yCons m r') s` together with
    the side condition that `s` lies in `X`, so `prependY j s = yCons j s`. -/
def Eq258YBaseObligation (j m : ℕ) (r' s : FreeAssocMono) (v : FreeJordanAlg) :
    Prop :=
  mul (pow y (j + 1)) (M_op (yCons m r') s v) =
    (1 / 2 : ℝ) • (M_op (prependY j (yCons m r')) s v +
      M_op (yCons m r') (yCons j s) v)

/-- The x-generator obligation symmetric to `Eq258YBaseObligation`, consumed
    by the future y-direction weight>1 helpers. -/
def Eq258XBaseObligation (k m : ℕ) (r' s : FreeAssocMono) (v : FreeJordanAlg) :
    Prop :=
  mul (pow x (k + 1)) (M_op (xCons m r') s v) =
    (1 / 2 : ℝ) • (M_op (prependX k (xCons m r')) s v +
      M_op (xCons m r') (xCons k s) v)

/-- Convert the y-direction Eq(2.58) family into the concrete y-base obligation
    used by the x-direction helpers. The `s ∈ X` side condition prevents the
    right prepend from merging and turns `prependY j s` into `yCons j s`. -/
theorem eq258YBaseObligation_of_eq258Y {j m : ℕ} {r' s : FreeAssocMono}
    {v : FreeJordanAlg} (hs : s.inX) (h : Eq258Y j (yCons m r') s) :
    Eq258YBaseObligation j m r' s v := by
  simpa [Eq258YBaseObligation, T_apply, prependY_of_inX hs] using h v

/-- Convert the x-direction Eq(2.58) family into the concrete x-base obligation
    needed by the y-direction helpers. The `s ∈ Y` side condition prevents the
    right prepend from merging and turns `prependX k s` into `xCons k s`. -/
theorem eq258XBaseObligation_of_eq258X {k m : ℕ} {r' s : FreeAssocMono}
    {v : FreeJordanAlg} (hs : s.inY) (h : Eq258X k (xCons m r') s) :
    Eq258XBaseObligation k m r' s v := by
  simpa [Eq258XBaseObligation, T_apply, prependX_of_inY hs] using h v

/-- Specialize an x-direction Eq(2.58) hypothesis when the right argument starts
    with an x-block. This is the shape of the swapped induction term in the
    weight > 1 helpers. -/
theorem eq258X_xCons_right_of_eq258X {k i : ℕ} {p s : FreeAssocMono}
    (h : Eq258X k p (xCons i s)) :
    ∀ v : FreeJordanAlg,
      T (pow x (k + 1)) (M_op p (xCons i s) v) =
        (1 / 2 : ℝ) • (M_op (prependX k p) (xCons i s) v +
          M_op p (xCons (k + 1 + i) s) v) := by
  intro v
  simpa [Eq258X, prependX] using h v

/-- Specialize an x-direction Eq(2.58) hypothesis when both arguments start
    with y-blocks, in the order used by the lower-pair obligation. -/
theorem eq258X_yCons_yCons_lower_of_eq258X {k j m : ℕ} {r' s : FreeAssocMono}
    (h : Eq258X k (yCons m r') (yCons j s)) :
    ∀ v : FreeJordanAlg,
      T (pow x (k + 1)) (M_op (yCons m r') (yCons j s) v) =
        (1 / 2 : ℝ) •
          (M_op (yCons m r') (xCons k (yCons j s)) v +
            M_op (xCons k (yCons m r')) (yCons j s) v) := by
  intro v
  simpa [Eq258X, prependX, add_comm] using h v

/-- Specialize the raw-right x-direction helper-family to the left lower-pair
    shape used in the `i < k` branch. -/
theorem eq258XRawRight_lower_left_of_family {k : ℕ} {p q : FreeAssocMono}
    (h : Eq258XRawRight k p q) :
    ∀ v : FreeJordanAlg,
      T (pow x (k + 1)) (M_op p q v) =
        (1 / 2 : ℝ) • (M_op p (xCons k q) v + M_op (xCons k p) q v) := by
  intro v
  exact h v

/-- Convert the ordinary x-family to the raw-right x-family when both arguments
    lie in `Y`, so neither x-prepend merges. -/
theorem eq258XRawRight_of_eq258X_of_inY {k : ℕ} {p q : FreeAssocMono}
    (hp : p.inY) (hq : q.inY) (h : Eq258X k p q) :
    Eq258XRawRight k p q := by
  intro v
  simpa [Eq258XRawRight, Eq258X, prependX_of_inY hp, prependX_of_inY hq, add_comm]
    using h v

/-- Specialize a y-direction Eq(2.58) hypothesis when the right argument starts
    with a y-block. Symmetric to `eq258X_xCons_right_of_eq258X`. -/
theorem eq258Y_yCons_right_of_eq258Y {j l : ℕ} {p s : FreeAssocMono}
    (h : Eq258Y j p (yCons l s)) :
    ∀ v : FreeJordanAlg,
      T (pow y (j + 1)) (M_op p (yCons l s) v) =
        (1 / 2 : ℝ) • (M_op (prependY j p) (yCons l s) v +
          M_op p (yCons (j + 1 + l) s) v) := by
  intro v
  simpa [Eq258Y, prependY] using h v

/-- Specialize a y-direction Eq(2.58) hypothesis when both arguments start
    with x-blocks, in the order used by the y-side lower-pair obligation. -/
theorem eq258Y_xCons_xCons_lower_of_eq258Y {j i m : ℕ} {r' s : FreeAssocMono}
    (h : Eq258Y j (xCons m r') (xCons i s)) :
    ∀ v : FreeJordanAlg,
      T (pow y (j + 1)) (M_op (xCons m r') (xCons i s) v) =
        (1 / 2 : ℝ) •
          (M_op (xCons m r') (yCons j (xCons i s)) v +
            M_op (yCons j (xCons m r')) (xCons i s) v) := by
  intro v
  simpa [Eq258Y, prependY, add_comm] using h v

/-- Specialize the y raw-right helper-family to the y-side lower-pair shape. -/
theorem eq258YRawRight_lower_left_of_family {j : ℕ} {p q : FreeAssocMono}
    (h : Eq258YRawRight j p q) :
    ∀ v : FreeJordanAlg,
      T (pow y (j + 1)) (M_op p q v) =
        (1 / 2 : ℝ) • (M_op p (yCons j q) v + M_op (yCons j p) q v) := by
  intro v
  exact h v

/-- Convert the ordinary y-family to the raw-right y-family when both arguments
    lie in `X`, so neither y-prepend merges. -/
theorem eq258YRawRight_of_eq258Y_of_inX {j : ℕ} {p q : FreeAssocMono}
    (hp : p.inX) (hq : q.inX) (h : Eq258Y j p q) :
    Eq258YRawRight j p q := by
  intro v
  simpa [Eq258YRawRight, Eq258Y, prependY_of_inX hp, prependY_of_inX hq, add_comm]
    using h v

/-- Symmetry of `M_op` on opposite pure powers. This is the concrete
    weight≤1 instance of H-O's symmetry in the tensor arguments. -/
theorem M_op_yCons_one_xCons_one_comm (j i : ℕ) (v : FreeJordanAlg) :
    M_op (yCons j one) (xCons i one) v = M_op (xCons i one) (yCons j one) v := by
  simp only [M_op.eq_def]
  rw [U_bilinear_comm]

/-- Symmetry of the same-x pure/one-block term used by the swapped x-base case. -/
theorem M_op_xCons_one_xCons_yCons_one_comm (i k j : ℕ) (v : FreeJordanAlg) :
    M_op (xCons i one) (xCons k (yCons j one)) v =
      M_op (xCons k (yCons j one)) (xCons i one) v := by
  rw [M_op.eq_def (xCons i one) (xCons k (yCons j one)) v]
  rw [M_op.eq_def (xCons k (yCons j one)) (xCons i one) v]
  simp only [ge_iff_le]
  by_cases hki : k ≤ i
  · rw [dif_pos hki]
    by_cases hik : i ≤ k
    · rw [dif_pos hik]
      have heq : i = k := by omega
      subst heq
      simp only [ite_true]
      rw [M_op.eq_def one (yCons j one) v, M_op.eq_def (yCons j one) one v]
    · rw [dif_neg hik]
      have hne1 : ¬ i = k := by omega
      simp only [hne1, ↓reduceIte]
      simp only [M_op.eq_def]
      rw [U_bilinear_comm]
  · rw [dif_neg hki]
    have hik : i ≤ k := by omega
    rw [dif_pos hik]
    have hne1 : ¬ k = i := by omega
    simp only [hne1, ↓reduceIte]
    simp only [M_op.eq_def]

/-- Symmetry of the same-y pure/one-block term used by the swapped y-base case. -/
theorem M_op_yCons_one_yCons_xCons_one_comm (j l i : ℕ) (v : FreeJordanAlg) :
    M_op (yCons j one) (yCons l (xCons i one)) v =
      M_op (yCons l (xCons i one)) (yCons j one) v := by
  rw [M_op.eq_def (yCons j one) (yCons l (xCons i one)) v]
  rw [M_op.eq_def (yCons l (xCons i one)) (yCons j one) v]
  simp only [ge_iff_le]
  by_cases hlj : l ≤ j
  · rw [dif_pos hlj]
    by_cases hjl : j ≤ l
    · rw [dif_pos hjl]
      have heq : j = l := by omega
      subst heq
      simp only [ite_true]
      rw [M_op.eq_def one (xCons i one) v, M_op.eq_def (xCons i one) one v]
    · rw [dif_neg hjl]
      have hne1 : ¬ j = l := by omega
      simp only [hne1, ↓reduceIte]
      simp only [M_op.eq_def]
      rw [U_bilinear_comm]
  · rw [dif_neg hlj]
    have hjl : j ≤ l := by omega
    rw [dif_pos hjl]
    have hne1 : ¬ l = j := by omega
    simp only [hne1, ↓reduceIte]
    simp only [M_op.eq_def]

/-- Different-letter symmetry for the long x-boundary swapped term, reduced to
    the two lower symmetry facts exposed by the defining recurrence. -/
theorem M_op_yCons_xCons_xCons_one_comm_of (m l i : ℕ) (r : FreeAssocMono)
    (v : FreeJordanAlg)
    (h_base : M_op (xCons l r) one v = M_op one (xCons l r) v)
    (h_tail : M_op (xCons (i + 1 + l) r) (yCons m one) v =
      M_op (yCons m one) (xCons (i + 1 + l) r) v) :
    M_op (yCons m (xCons l r)) (xCons i one) v =
      M_op (xCons i one) (yCons m (xCons l r)) v := by
  rw [M_op.eq_def (yCons m (xCons l r)) (xCons i one) v]
  rw [M_op.eq_def (xCons i one) (yCons m (xCons l r)) v]
  simp only [prependX, prependY]
  rw [h_base, h_tail]
  rw [U_bilinear_comm]

/-- Different-letter symmetry for the long y-boundary swapped term, reduced to
    the two lower symmetry facts exposed by the defining recurrence. -/
theorem M_op_xCons_yCons_yCons_one_comm_of (m l j : ℕ) (r : FreeAssocMono)
    (v : FreeJordanAlg)
    (h_base : M_op (yCons l r) one v = M_op one (yCons l r) v)
    (h_tail : M_op (yCons (j + 1 + l) r) (xCons m one) v =
      M_op (xCons m one) (yCons (j + 1 + l) r) v) :
    M_op (xCons m (yCons l r)) (yCons j one) v =
      M_op (yCons j one) (xCons m (yCons l r)) v := by
  rw [M_op.eq_def (xCons m (yCons l r)) (yCons j one) v]
  rw [M_op.eq_def (yCons j one) (xCons m (yCons l r)) v]
  simp only [prependX, prependY]
  rw [h_base, h_tail]
  rw [U_bilinear_comm]

/-- Same-x symmetry for the long x-boundary term, reduced to lower boundary and
    different-letter symmetry facts. -/
theorem M_op_xCons_one_xCons_yCons_xCons_comm_of (i k m l : ℕ)
    (r : FreeAssocMono) (v : FreeJordanAlg)
    (h_equal : M_op one (yCons m (xCons l r)) v =
      M_op (yCons m (xCons l r)) one v)
    (h_boundary : ∀ a : ℕ,
      M_op one (xCons a (yCons m (xCons l r))) v =
        M_op (xCons a (yCons m (xCons l r))) one v)
    (h_diff : ∀ a : ℕ,
      M_op (xCons a one) (yCons m (xCons l r)) v =
        M_op (yCons m (xCons l r)) (xCons a one) v) :
    M_op (xCons i one) (xCons k (yCons m (xCons l r))) v =
      M_op (xCons k (yCons m (xCons l r))) (xCons i one) v := by
  rw [M_op.eq_def (xCons i one) (xCons k (yCons m (xCons l r))) v]
  rw [M_op.eq_def (xCons k (yCons m (xCons l r))) (xCons i one) v]
  simp only [ge_iff_le]
  by_cases hki : k ≤ i
  · rw [dif_pos hki]
    by_cases hik : i ≤ k
    · rw [dif_pos hik]
      have heq : i = k := by omega
      subst heq
      simp only [ite_true]
      rw [h_equal]
    · rw [dif_neg hik]
      have hne : ¬ i = k := by omega
      simp only [hne, ↓reduceIte]
      rw [h_diff]
  · rw [dif_neg hki]
    have hik : i ≤ k := by omega
    rw [dif_pos hik]
    have hne : ¬ k = i := by omega
    simp only [hne, ↓reduceIte]
    rw [h_boundary]

/-- Same-y symmetry for the long y-boundary term, reduced to lower boundary and
    different-letter symmetry facts. -/
theorem M_op_yCons_one_yCons_xCons_yCons_comm_of (j l m n : ℕ)
    (r : FreeAssocMono) (v : FreeJordanAlg)
    (h_equal : M_op one (xCons m (yCons n r)) v =
      M_op (xCons m (yCons n r)) one v)
    (h_boundary : ∀ a : ℕ,
      M_op one (yCons a (xCons m (yCons n r))) v =
        M_op (yCons a (xCons m (yCons n r))) one v)
    (h_diff : ∀ a : ℕ,
      M_op (yCons a one) (xCons m (yCons n r)) v =
        M_op (xCons m (yCons n r)) (yCons a one) v) :
    M_op (yCons j one) (yCons l (xCons m (yCons n r))) v =
      M_op (yCons l (xCons m (yCons n r))) (yCons j one) v := by
  rw [M_op.eq_def (yCons j one) (yCons l (xCons m (yCons n r))) v]
  rw [M_op.eq_def (yCons l (xCons m (yCons n r))) (yCons j one) v]
  simp only [ge_iff_le]
  by_cases hlj : l ≤ j
  · rw [dif_pos hlj]
    by_cases hjl : j ≤ l
    · rw [dif_pos hjl]
      have heq : j = l := by omega
      subst heq
      simp only [ite_true]
      rw [h_equal]
    · rw [dif_neg hjl]
      have hne : ¬ j = l := by omega
      simp only [hne, ↓reduceIte]
      rw [h_diff]
  · rw [dif_neg hlj]
    have hjl : j ≤ l := by omega
    rw [dif_pos hjl]
    have hne : ¬ l = j := by omega
    simp only [hne, ↓reduceIte]
    rw [h_boundary]

/-- H-O's symmetry step for the x-family: if Eq(2.58) is known for `(q,p)`
    and the three resulting `M_op` terms commute, then it is known for `(p,q)`. -/
theorem Eq258X_of_swapped_comm {k : ℕ} {p q : FreeAssocMono}
    (h : Eq258X k q p)
    (h_pq : ∀ v, M_op p q v = M_op q p v)
    (h_left : ∀ v, M_op (prependX k p) q v = M_op q (prependX k p) v)
    (h_right : ∀ v, M_op p (prependX k q) v = M_op (prependX k q) p v) :
    Eq258X k p q := by
  intro v
  rw [h_pq]
  rw [h]
  rw [← h_left, ← h_right]
  rw [add_comm]

/-- H-O's symmetry step for the y-family. -/
theorem Eq258Y_of_swapped_comm {j : ℕ} {p q : FreeAssocMono}
    (h : Eq258Y j q p)
    (h_pq : ∀ v, M_op p q v = M_op q p v)
    (h_left : ∀ v, M_op (prependY j p) q v = M_op q (prependY j p) v)
    (h_right : ∀ v, M_op p (prependY j q) v = M_op (prependY j q) p v) :
    Eq258Y j p q := by
  intro v
  rw [h_pq]
  rw [h]
  rw [← h_left, ← h_right]
  rw [add_comm]

/-! ### Driver-ready weight≤1 x-direction cases -/

theorem eq258X_one_one (k : ℕ) : Eq258X k one one := by
  intro v
  simpa [Eq258X, prependX] using eq258_one_one k v

theorem eq258X_one_yCons_one (k j : ℕ) : Eq258X k one (yCons j one) := by
  intro v
  simpa [Eq258X, prependX] using eq258_one_yCons k j v

theorem eq258X_yCons_one_one (k j : ℕ) : Eq258X k (yCons j one) one := by
  intro v
  simpa [Eq258X, prependX] using eq258_yCons_one k j v

theorem eq258X_xCons_one_one (k i : ℕ) : Eq258X k (xCons i one) one := by
  intro v
  by_cases hik : k ≤ i
  · simpa [Eq258X, prependX] using eq258_xCons_one_ge k i hik v
  · have hlt : i < k := Nat.lt_of_not_ge hik
    simpa [Eq258X, prependX] using eq258_xCons_one_lt k i hlt v

theorem eq258X_xCons_one_yCons_one (k i j : ℕ) :
    Eq258X k (xCons i one) (yCons j one) := by
  intro v
  by_cases hik : k ≤ i
  · simpa [Eq258X, prependX] using eq258_xCons_yCons_ge k i j hik v
  · have hlt : i < k := Nat.lt_of_not_ge hik
    simpa [Eq258X, prependX] using eq258_xCons_yCons_lt k i j hlt v

/-- Swapped pure-power x-direction base case, following H-O's symmetry between
    `p ∈ X, q ∈ Y` and `p ∈ Y, q ∈ X`. -/
theorem eq258X_yCons_one_xCons_one (k j i : ℕ) :
    Eq258X k (yCons j one) (xCons i one) := by
  intro v
  have h := eq258X_xCons_one_yCons_one k i j
  simpa [Eq258X, prependX, M_op_yCons_one_xCons_one_comm,
    M_op_xCons_one_xCons_yCons_one_comm, add_comm, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using h v

/-! ### Driver-ready easy weight≤1 y-direction cases -/

theorem eq258Y_one_one (j : ℕ) : Eq258Y j one one := by
  intro v
  simp only [prependY, M_op.eq_def, T_apply]
  rw [← two_smul ℝ (mul (pow y (j + 1)) v), smul_smul]
  norm_num

theorem eq258Y_one_xCons_one (j i : ℕ) : Eq258Y j one (xCons i one) := by
  intro v
  simp only [prependY, M_op.eq_def, U_bilinear_apply, T_apply]
  conv_rhs =>
    rw [show mul (pow x (i + 1)) (pow y (j + 1)) =
      mul (pow y (j + 1)) (pow x (i + 1)) from FreeJordanAlg.mul_comm _ _]
  simp only [smul_add, smul_sub, smul_smul]
  norm_num
  abel

theorem eq258Y_xCons_one_one (j i : ℕ) : Eq258Y j (xCons i one) one := by
  intro v
  simp only [prependY, M_op.eq_def, U_bilinear_apply, T_apply]
  conv_rhs =>
    rw [show mul (pow x (i + 1)) (pow y (j + 1)) =
      mul (pow y (j + 1)) (pow x (i + 1)) from FreeJordanAlg.mul_comm _ _]
  simp only [smul_add, smul_sub, smul_smul]
  norm_num

theorem eq258Y_yCons_one_one (l j : ℕ) : Eq258Y l (yCons j one) one := by
  intro v
  by_cases hlj : l ≤ j
  · simpa [Eq258Y, prependY] using eq258_yCons_one_ge l j hlj v
  · have hjl : j < l := Nat.lt_of_not_ge hlj
    simpa [Eq258Y, prependY] using eq258_yCons_one_lt l j hjl v

theorem eq258Y_yCons_one_xCons_one (l j i : ℕ) :
    Eq258Y l (yCons j one) (xCons i one) := by
  intro v
  by_cases hlj : l ≤ j
  · simpa [Eq258Y, prependY] using eq258_yCons_xCons_ge l j i hlj v
  · have hjl : j < l := Nat.lt_of_not_ge hlj
    simpa [Eq258Y, prependY] using eq258_yCons_xCons_lt l j i hjl v

/-- Swapped pure-power y-direction base case, following H-O's symmetry between
    `p ∈ Y, q ∈ X` and `p ∈ X, q ∈ Y`. -/
theorem eq258Y_xCons_one_yCons_one (l i j : ℕ) :
    Eq258Y l (xCons i one) (yCons j one) := by
  intro v
  have h := eq258Y_yCons_one_xCons_one l j i
  simpa [Eq258Y, prependY, M_op_yCons_one_xCons_one_comm,
    M_op_yCons_one_yCons_xCons_one_comm, add_comm, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using h v

/-- Recover the x-boundary swapped obligation from the well-formed driver layer.
    The pure tail is already the swapped weight≤1 base case. -/
theorem Eq258DriverWFLayer.xBoundarySwap {n : ℕ} (hLayer : Eq258DriverWFLayer n)
    (k i m : ℕ) (r' : FreeAssocMono) (hr : r'.inX)
    (hw : (yCons m r').weight + (xCons i one).weight = n) :
    Eq258X k (yCons m r') (xCons i one) := by
  cases r' with
  | one =>
    simpa using eq258X_yCons_one_xCons_one k m i
  | xCons l rest =>
    exact hLayer.xBoundarySwapLong k i m l rest hw
  | yCons l rest =>
    cases hr with
    | inl h => cases h
    | inr h => simp [inX0, startsWithX] at h

/-- Recover the y-boundary swapped obligation from the well-formed driver layer.
    The pure tail is already the swapped weight≤1 base case. -/
theorem Eq258DriverWFLayer.yBoundarySwap {n : ℕ} (hLayer : Eq258DriverWFLayer n)
    (l j m : ℕ) (r' : FreeAssocMono) (hr : r'.inY)
    (hw : (xCons m r').weight + (yCons j one).weight = n) :
    Eq258Y l (xCons m r') (yCons j one) := by
  cases r' with
  | one =>
    simpa using eq258Y_xCons_one_yCons_one l m j
  | xCons nTail rest =>
    cases hr with
    | inl h => cases h
    | inr h => simp [inY0, startsWithY] at h
  | yCons nTail rest =>
    exact hLayer.yBoundarySwapLong l j m nTail rest hw

/-! ### Equation (2.58) weight > 1 — Inductive cases

H-O lines 1346-1377. For p = x^{i+1}·r, q = y^{j+1}·s where r ∈ Y, s ∈ X,
and either r ≠ 1 or s ≠ 1 (so weight > 1).

Equation (2.59): M_{p,q} = 2U_{x^{i+1},y^{j+1}} M_{r,s} - M_{y^{j+1}·r, x^{i+1}·s}

Case 1 (i ≥ k): Apply (2.49) to T_{x^{k+1}} U_{x^{i+1},y^{j+1}}, and
  induction on T_{x^{k+1}} M_{y^{j+1}·r, x^{i+1}·s} (lower weight).
  H-O lines 1346-1367.

Case 2 (i < k): Apply (2.47) to T_{x^{k+1}} U_{x^{i+1},y^{j+1}}, and
  induction on T_{x^{k+1}} M_{y^{j+1}·r, x^{i+1}·s} (lower weight).
  H-O lines 1369-1377. -/

/-- Equation (2.59): M_op recurrence for xCons-yCons with yCons tail.
    M(x^{i+1}·(y^m·r'), y^{j+1}·s) = 2·U_{x^{i+1},y^{j+1}}·M(y^m·r',s)
      - M(y^{j+1}·(y^m·r'), x^{i+1}·s).
    Direct from M_op_xCons_yCons_yCons. H-O lines 1350-1352 (equation 2.59). -/
theorem eq259_xCons_yCons (i j m : ℕ) (r' : FreeAssocMono)
    (s : FreeAssocMono) (v : FreeJordanAlg) :
    M_op (xCons i (yCons m r')) (yCons j s) v =
    (2 : ℝ) • U_bilinear (pow x (i + 1)) (pow y (j + 1))
        (M_op (yCons m r') s v)
      - M_op (prependY j (yCons m r')) (xCons i s) v :=
  M_op_xCons_yCons_yCons i m r' j s v

/-- Symmetric form of (2.59): M_op recurrence for yCons-xCons with xCons tail. -/
theorem eq259_yCons_xCons (j i m : ℕ) (r' : FreeAssocMono)
    (s : FreeAssocMono) (v : FreeJordanAlg) :
    M_op (yCons j (xCons m r')) (xCons i s) v =
    (2 : ℝ) • U_bilinear (pow y (j + 1)) (pow x (i + 1))
        (M_op (xCons m r') s v)
      - M_op (prependX i (xCons m r')) (yCons j s) v :=
  M_op_yCons_xCons_xCons j m r' i s v

/-- Boundary form of (2.59) from H-O (2.56a): second argument is `1`. -/
theorem eq259_xCons_one (i m : ℕ) (r' : FreeAssocMono) (v : FreeJordanAlg) :
    M_op (xCons i (yCons m r')) one v =
      (2 : ℝ) • T (pow x (i + 1)) (M_op (yCons m r') one v)
        - M_op (yCons m r') (xCons i one) v := by
  cases r' with
  | one =>
    rw [M_op.eq_def (xCons i (yCons m one)) one v,
      M_op.eq_def (yCons m one) one v,
      M_op.eq_def (yCons m one) (xCons i one) v]
  | xCons l rest =>
    rw [M_op.eq_def (xCons i (yCons m (xCons l rest))) one v]
  | yCons l rest =>
    rw [M_op.eq_def (xCons i (yCons m (yCons l rest))) one v]

/-- Symmetric boundary form of (2.59) from H-O (2.56b): second argument is `1`. -/
theorem eq259_yCons_one (j m : ℕ) (r' : FreeAssocMono) (v : FreeJordanAlg) :
    M_op (yCons j (xCons m r')) one v =
      (2 : ℝ) • T (pow y (j + 1)) (M_op (xCons m r') one v)
        - M_op (xCons m r') (yCons j one) v := by
  cases r' with
  | one =>
    rw [M_op.eq_def (yCons j (xCons m one)) one v,
      M_op.eq_def (xCons m one) one v,
      M_op.eq_def (xCons m one) (yCons j one) v]
  | xCons l rest =>
    rw [M_op.eq_def (yCons j (xCons m (xCons l rest))) one v]
  | yCons l rest =>
    rw [M_op.eq_def (yCons j (xCons m (yCons l rest))) one v]

/-- Boundary form of (2.59) from H-O (2.57b): first argument is `1`. -/
theorem eq259_one_xCons (i m : ℕ) (r' : FreeAssocMono) (v : FreeJordanAlg) :
    M_op one (xCons i (yCons m r')) v =
      (2 : ℝ) • T (pow x (i + 1)) (M_op one (yCons m r') v)
        - M_op (xCons i one) (yCons m r') v := by
  cases r' with
  | one =>
    simp only [M_op.eq_def]
    rw [U_bilinear_comm]
  | xCons l rest =>
    rw [M_op.eq_def one (xCons i (yCons m (xCons l rest))) v]
  | yCons l rest =>
    rw [M_op.eq_def one (xCons i (yCons m (yCons l rest))) v]

/-- Symmetric boundary form of (2.59) from H-O (2.57): first argument is `1`. -/
theorem eq259_one_yCons (j m : ℕ) (r' : FreeAssocMono) (v : FreeJordanAlg) :
    M_op one (yCons j (xCons m r')) v =
      (2 : ℝ) • T (pow y (j + 1)) (M_op one (xCons m r') v)
        - M_op (yCons j one) (xCons m r') v := by
  cases r' with
  | one =>
    simp only [M_op.eq_def]
    rw [U_bilinear_comm]
  | xCons l rest =>
    rw [M_op.eq_def one (yCons j (xCons m (xCons l rest))) v]
  | yCons l rest =>
    rw [M_op.eq_def one (yCons j (xCons m (yCons l rest))) v]

/-- Pure x boundary symmetry against `1`, directly from the base cases. -/
theorem M_op_xCons_one_one_comm (i : ℕ) (v : FreeJordanAlg) :
    M_op (xCons i one) one v = M_op one (xCons i one) v := by
  rw [M_op.eq_def (xCons i one) one v, M_op.eq_def one (xCons i one) v]

/-- Pure y boundary symmetry against `1`, directly from the base cases. -/
theorem M_op_yCons_one_one_comm (j : ℕ) (v : FreeJordanAlg) :
    M_op (yCons j one) one v = M_op one (yCons j one) v := by
  rw [M_op.eq_def (yCons j one) one v, M_op.eq_def one (yCons j one) v]

/-- Non-well-formed same-x boundary reduction on the left. -/
theorem M_op_xCons_xCons_one_boundary (i l : ℕ) (r : FreeAssocMono)
    (v : FreeJordanAlg) :
    M_op (xCons i (xCons l r)) one v =
      T (pow x (i + 1)) (M_op (xCons l r) one v) := by
  rw [M_op.eq_def (xCons i (xCons l r)) one v]

/-- Non-well-formed same-x boundary reduction on the right. -/
theorem M_op_one_xCons_xCons_boundary (i l : ℕ) (r : FreeAssocMono)
    (v : FreeJordanAlg) :
    M_op one (xCons i (xCons l r)) v =
      T (pow x (i + 1)) (M_op one (xCons l r) v) := by
  rw [M_op.eq_def one (xCons i (xCons l r)) v]

/-- Non-well-formed same-y boundary reduction on the left. -/
theorem M_op_yCons_yCons_one_boundary (j m : ℕ) (r : FreeAssocMono)
    (v : FreeJordanAlg) :
    M_op (yCons j (yCons m r)) one v =
      T (pow y (j + 1)) (M_op (yCons m r) one v) := by
  rw [M_op.eq_def (yCons j (yCons m r)) one v]

/-- Non-well-formed same-y boundary reduction on the right. -/
theorem M_op_one_yCons_yCons_boundary (j m : ℕ) (r : FreeAssocMono)
    (v : FreeJordanAlg) :
    M_op one (yCons j (yCons m r)) v =
      T (pow y (j + 1)) (M_op one (yCons m r) v) := by
  rw [M_op.eq_def one (yCons j (yCons m r)) v]

/-- Non-well-formed second y-block symmetry for pure x against a y-start term. -/
theorem M_op_xCons_one_yCons_yCons_comm (i j m : ℕ) (r : FreeAssocMono)
    (v : FreeJordanAlg) :
    M_op (xCons i one) (yCons j (yCons m r)) v =
      M_op (yCons j (yCons m r)) (xCons i one) v := by
  rw [M_op.eq_def (xCons i one) (yCons j (yCons m r)) v,
    M_op.eq_def (yCons j (yCons m r)) (xCons i one) v]

/-- Non-well-formed second x-block symmetry for pure y against an x-start term. -/
theorem M_op_yCons_one_xCons_xCons_comm (j i l : ℕ) (r : FreeAssocMono)
    (v : FreeJordanAlg) :
    M_op (yCons j one) (xCons i (xCons l r)) v =
      M_op (xCons i (xCons l r)) (yCons j one) v := by
  rw [M_op.eq_def (yCons j one) (xCons i (xCons l r)) v,
    M_op.eq_def (xCons i (xCons l r)) (yCons j one) v]

mutual

/-- Boundary symmetry for the total `M_op` recursion against `1`.

This packages H-O's evident symmetry `M_{p,q}=M_{q,p}` for the boundary shapes
needed by Eq(2.58). The proof is mutually recursive with the pure/long
different-letter symmetry facts because the boundary recurrences (2.56)/(2.57)
expose those terms. -/
theorem M_op_one_comm (p : FreeAssocMono) (v : FreeJordanAlg) :
    M_op p one v = M_op one p v := by
  cases p with
  | one =>
    rfl
  | xCons i r =>
    cases r with
    | one =>
      exact M_op_xCons_one_one_comm i v
    | xCons l rest =>
      rw [M_op_xCons_xCons_one_boundary i l rest v,
        M_op_one_xCons_xCons_boundary i l rest v]
      rw [M_op_one_comm (xCons l rest) v]
    | yCons m rest =>
      rw [eq259_xCons_one i m rest v, eq259_one_xCons i m rest v]
      rw [M_op_one_comm (yCons m rest) v]
      rw [← M_op_xCons_one_yCons_comm i m rest v]
  | yCons j r =>
    cases r with
    | one =>
      exact M_op_yCons_one_one_comm j v
    | xCons m rest =>
      rw [eq259_yCons_one j m rest v, eq259_one_yCons j m rest v]
      rw [M_op_one_comm (xCons m rest) v]
      rw [← M_op_yCons_one_xCons_comm j m rest v]
    | yCons m rest =>
      rw [M_op_yCons_yCons_one_boundary j m rest v,
        M_op_one_yCons_yCons_boundary j m rest v]
      rw [M_op_one_comm (yCons m rest) v]

/-- Different-letter symmetry for a pure x-block against a y-start monomial. -/
theorem M_op_xCons_one_yCons_comm (i j : ℕ) (r : FreeAssocMono)
    (v : FreeJordanAlg) :
    M_op (xCons i one) (yCons j r) v =
      M_op (yCons j r) (xCons i one) v := by
  cases r with
  | one =>
    exact (M_op_yCons_one_xCons_one_comm j i v).symm
  | xCons l rest =>
    exact (M_op_yCons_xCons_xCons_one_comm_of j l i rest v
      (M_op_one_comm (xCons l rest) v)
      ((M_op_yCons_one_xCons_comm j (i + 1 + l) rest v).symm)).symm
  | yCons m rest =>
    exact M_op_xCons_one_yCons_yCons_comm i j m rest v

/-- Different-letter symmetry for a pure y-block against an x-start monomial. -/
theorem M_op_yCons_one_xCons_comm (j i : ℕ) (r : FreeAssocMono)
    (v : FreeJordanAlg) :
    M_op (yCons j one) (xCons i r) v =
      M_op (xCons i r) (yCons j one) v := by
  cases r with
  | one =>
    exact M_op_yCons_one_xCons_one_comm j i v
  | xCons l rest =>
    exact M_op_yCons_one_xCons_xCons_comm j i l rest v
  | yCons n rest =>
    exact (M_op_xCons_yCons_yCons_one_comm_of i n j rest v
      (M_op_one_comm (yCons n rest) v)
      ((M_op_xCons_one_yCons_comm i (j + 1 + n) rest v).symm)).symm

end

/-- Boundary (2.58) obtained by rearranging H-O (2.56a). -/
theorem eq258X_yCons_one_exact (i m : ℕ) (r' : FreeAssocMono) :
    Eq258X i (yCons m r') one := by
  intro v
  have h := eq259_xCons_one i m r' v
  simp only [prependX]
  rw [h]
  module

/-- Symmetric boundary (2.58) obtained by rearranging H-O (2.56b). -/
theorem eq258Y_xCons_one_exact (j m : ℕ) (r' : FreeAssocMono) :
    Eq258Y j (xCons m r') one := by
  intro v
  have h := eq259_yCons_one j m r' v
  simp only [prependY]
  rw [h]
  module

/-- Boundary (2.58) obtained by rearranging H-O (2.57b). -/
theorem eq258X_one_yCons_exact (i m : ℕ) (r' : FreeAssocMono) :
    Eq258X i one (yCons m r') := by
  intro v
  have h := eq259_one_xCons i m r' v
  simp only [prependX]
  rw [h]
  module

/-- Symmetric boundary (2.58) obtained by rearranging H-O (2.57). -/
theorem eq258Y_one_xCons_exact (j m : ℕ) (r' : FreeAssocMono) :
    Eq258Y j one (xCons m r') := by
  intro v
  have h := eq259_one_yCons j m r' v
  simp only [prependY]
  rw [h]
  module

/-- Long boundary case for Eq(2.58), `i ≥ k`, with second argument `1`.

This is the H-O (2.56a) boundary analogue of
`eq258_xCons_yCons_general_ge`. The swapped term has the same total block
weight as the target, so this helper exposes that obligation explicitly rather
than pretending it is available from `Eq258DriverIH`. -/
theorem eq258_xCons_one_general_ge (k i m : ℕ) (r' : FreeAssocMono)
    (hik : k ≤ i)
    (ih_swap : ∀ v, T (pow x (k + 1)) (M_op (yCons m r') (xCons i one) v) =
      (1 / 2 : ℝ) • (M_op (xCons k (yCons m r')) (xCons i one) v +
        M_op (yCons m r') (xCons (k + 1 + i) one) v))
    (v : FreeJordanAlg) :
    T (pow x (k + 1)) (M_op (xCons i (yCons m r')) one v) =
    (1 / 2 : ℝ) • (M_op (xCons (k + 1 + i) (yCons m r')) one v +
      M_op (xCons i (yCons m r')) (xCons k one) v) := by
  rw [eq259_xCons_one]
  rw [T_sub, T_smul']
  have h249 := @JordanAlgebra.operator_identity_249 FreeJordanAlg _
    FreeJordanAlg.x (1 : FreeJordanAlg) (k + 1) (i - k)
  have h249v := LinearMap.ext_iff.mp h249 (M_op (yCons m r') one v)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply] at h249v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq, FJ_U_linear_apply] at h249v
  rw [show k + 1 + (i - k) = i + 1 from by omega,
      show k + 1 + (i + 1) = k + 1 + i + 1 from by omega] at h249v
  rw [ih_swap]
  have h249' : T (pow x (k + 1)) (T (pow x (i + 1)) (M_op (yCons m r') one v)) =
    (1 / 2 : ℝ) • (U (pow x (k + 1))
        (U_bilinear (pow x (i - k)) 1 (M_op (yCons m r') one v)) +
      U_bilinear (pow x (k + 1 + i + 1)) 1 (M_op (yCons m r') one v)) := by
    simp only [T_apply] at h249v ⊢
    rw [show mul (pow x (i + 1)) (M_op (yCons m r') one v) =
        U_bilinear (pow x (i + 1)) 1 (M_op (yCons m r') one v) from by
      rw [U_bilinear_one_right]
      rfl]
    rw [show mul (pow x (k + 1))
          (U_bilinear (pow x (i + 1)) 1 (M_op (yCons m r') one v))
        = (1 / 2 : ℝ) • ((2 : ℝ) • mul (pow x (k + 1))
            (U_bilinear (pow x (i + 1)) 1 (M_op (yCons m r') one v))) from by
          rw [smul_smul]
          norm_num,
      h249v]
  rw [h249']
  rw [smul_smul, show (2 : ℝ) * (1 / 2 : ℝ) = 1 from by norm_num, one_smul]
  have h_big : U_bilinear (pow x (k + 1 + i + 1)) 1 (M_op (yCons m r') one v) =
      (1 / 2 : ℝ) • (M_op (xCons (k + 1 + i) (yCons m r')) one v +
        M_op (yCons m r') (xCons (k + 1 + i) one) v) := by
    rw [U_bilinear_one_right]
    have h := eq258X_yCons_one_exact (k + 1 + i) m r'
    have hv := h v
    simpa [Eq258X, prependX, T_apply] using hv
  rw [h_big]
  suffices h_key : U (pow x (k + 1))
      (U_bilinear (pow x (i - k)) 1 (M_op (yCons m r') one v)) =
    (1 / 2 : ℝ) • (M_op (xCons k (yCons m r')) (xCons i one) v +
      M_op (xCons i (yCons m r')) (xCons k one) v) by
    rw [h_key]
    module
  by_cases hik' : i = k
  · subst hik'
    rw [show pow x (i - i) = 1 from by simp [FreeJordanAlg.pow_zero]]
    rw [U_bilinear_one_left]
    simp only [T_apply, one_mul_eq]
    rw [M_op_xCons_xCons i (yCons m r') one v]
    module
  · have hgt : k < i := Nat.lt_of_le_of_ne hik (Ne.symm hik')
    have hbase := eq258X_yCons_one_exact (i - k - 1) m r'
    have hbasev := hbase v
    have hbase' : U_bilinear (pow x (i - k)) 1 (M_op (yCons m r') one v) =
      (1 / 2 : ℝ) • (M_op (xCons (i - k - 1) (yCons m r')) one v +
        M_op (yCons m r') (xCons (i - k - 1) one) v) := by
      rw [U_bilinear_one_right]
      simpa [Eq258X, prependX, T_apply, show i - k - 1 + 1 = i - k from by omega]
        using hbasev
    rw [hbase']
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
      FJ_U_eq, FJ_U_eq]
    rw [M_op_U_prependX, M_op_U_prependX]
    rw [show prependX k (xCons (i - k - 1) (yCons m r')) =
      xCons i (yCons m r') from by
        simp [prependX]
        omega]
    rw [show prependX k (xCons (i - k - 1) one) = xCons i one from by
      simp [prependX]
      omega]
    simp only [show prependX k (yCons m r') = xCons k (yCons m r') from rfl,
      show prependX k one = xCons k one from rfl]
    rw [add_comm]

/-- Long boundary case for Eq(2.58), `i < k`, with second argument `1`.

The lower obligation is raw-right because the same-letter property naturally
produces the unmerged right product `xCons (k - i - 1) one`. -/
theorem eq258_xCons_one_general_lt (k i m : ℕ) (r' : FreeAssocMono)
    (hik : i < k)
    (ih_swap : ∀ v, T (pow x (k + 1)) (M_op (yCons m r') (xCons i one) v) =
      (1 / 2 : ℝ) • (M_op (xCons k (yCons m r')) (xCons i one) v +
        M_op (yCons m r') (xCons (k + 1 + i) one) v))
    (v : FreeJordanAlg)
    (ih_lower : Eq258XRawRight (k - i - 1) (yCons m r') one) :
    T (pow x (k + 1)) (M_op (xCons i (yCons m r')) one v) =
    (1 / 2 : ℝ) • (M_op (xCons (k + 1 + i) (yCons m r')) one v +
      M_op (xCons i (yCons m r')) (xCons k one) v) := by
  rw [eq259_xCons_one]
  rw [T_sub, T_smul']
  have h247 := @JordanAlgebra.operator_identity_247 FreeJordanAlg _
    FreeJordanAlg.x (1 : FreeJordanAlg) (i + 1) (k + 1)
  have h247v := LinearMap.ext_iff.mp h247 (M_op (yCons m r') one v)
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at h247v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq] at h247v
  rw [ih_swap]
  have h247_iso :
      T (pow x (k + 1)) (T (pow x (i + 1)) (M_op (yCons m r') one v)) =
        -T (pow x (i + 1))
            (U_bilinear (pow x (k + 1)) 1 (M_op (yCons m r') one v)) +
          U_bilinear (pow x (i + 1)) (pow x (k + 1))
            (T 1 (M_op (yCons m r') one v)) +
          U_bilinear (pow x (i + 1 + (k + 1))) 1
            (M_op (yCons m r') one v) := by
    rw [← U_bilinear_one_right (pow x (i + 1)) (M_op (yCons m r') one v)]
    calc
      T (pow x (k + 1))
          (U_bilinear (pow x (i + 1)) 1 (M_op (yCons m r') one v)) =
        (T (pow x (k + 1))
            (U_bilinear (pow x (i + 1)) 1 (M_op (yCons m r') one v)) +
          T (pow x (i + 1))
            (U_bilinear (pow x (k + 1)) 1 (M_op (yCons m r') one v))) -
          T (pow x (i + 1))
            (U_bilinear (pow x (k + 1)) 1 (M_op (yCons m r') one v)) := by
          abel
      _ =
        (U_bilinear (pow x (i + 1)) (pow x (k + 1))
            (T 1 (M_op (yCons m r') one v)) +
          U_bilinear (pow x (i + 1 + (k + 1))) 1
            (M_op (yCons m r') one v)) -
          T (pow x (i + 1))
            (U_bilinear (pow x (k + 1)) 1 (M_op (yCons m r') one v)) := by
          rw [h247v]
      _ =
        -T (pow x (i + 1))
            (U_bilinear (pow x (k + 1)) 1 (M_op (yCons m r') one v)) +
          U_bilinear (pow x (i + 1)) (pow x (k + 1))
            (T 1 (M_op (yCons m r') one v)) +
          U_bilinear (pow x (i + 1 + (k + 1))) 1
            (M_op (yCons m r') one v) := by
          abel
  have h249 := @JordanAlgebra.operator_identity_249 FreeJordanAlg _
    FreeJordanAlg.x (1 : FreeJordanAlg) (i + 1) (k - i)
  have h249v := LinearMap.ext_iff.mp h249 (M_op (yCons m r') one v)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply] at h249v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq, FJ_U_linear_apply] at h249v
  rw [show i + 1 + (k - i) = k + 1 from by omega,
      show i + 1 + (k + 1) = i + 1 + k + 1 from by omega] at h249v
  have h249_iso :
      T (pow x (i + 1))
          (U_bilinear (pow x (k + 1)) 1 (M_op (yCons m r') one v)) =
        (1 / 2 : ℝ) •
          (U (pow x (i + 1))
              (U_bilinear (pow x (k - i)) 1 (M_op (yCons m r') one v)) +
            U_bilinear (pow x (i + 1 + k + 1)) 1
              (M_op (yCons m r') one v)) := by
    simp only [T_apply] at h249v ⊢
    rw [show mul (pow x (i + 1))
          (U_bilinear (pow x (k + 1)) 1 (M_op (yCons m r') one v))
        = (1 / 2 : ℝ) • ((2 : ℝ) • mul (pow x (i + 1))
            (U_bilinear (pow x (k + 1)) 1 (M_op (yCons m r') one v))) from by
          rw [smul_smul]
          norm_num,
      h249v]
  rw [h247_iso, h249_iso]
  have h_same :
      U_bilinear (pow x (i + 1)) (pow x (k + 1))
          (T 1 (M_op (yCons m r') one v)) =
        (1 / 2 : ℝ) • (M_op (xCons k (yCons m r')) (xCons i one) v +
          M_op (xCons i (yCons m r')) (xCons k one) v) := by
    simp only [T_apply, one_mul_eq]
    rw [U_bilinear_x_pow_lt_as_U_T i k hik]
    have h_lower' :
        T (pow x (k - i)) (M_op (yCons m r') one v) =
          (1 / 2 : ℝ) •
            (M_op (yCons m r') (xCons (k - i - 1) one) v +
              M_op (xCons (k - i - 1) (yCons m r')) one v) := by
      simpa [Eq258XRawRight, show k - i - 1 + 1 = k - i from by omega]
        using ih_lower v
    rw [h_lower']
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
      FJ_U_eq, FJ_U_eq]
    rw [M_op_U_prependX, M_op_U_prependX]
    rw [show prependX i (xCons (k - i - 1) (yCons m r')) =
      xCons k (yCons m r') from by
        simp [prependX]
        omega]
    rw [show prependX i (xCons (k - i - 1) one) = xCons k one from by
      simp [prependX]
      omega]
    simp only [show prependX i (yCons m r') = xCons i (yCons m r') from rfl,
      show prependX i one = xCons i one from rfl]
    rw [add_comm]
  have h_first : U (pow x (i + 1))
      (U_bilinear (pow x (k - i)) 1 (M_op (yCons m r') one v)) =
        (1 / 2 : ℝ) • (M_op (xCons k (yCons m r')) (xCons i one) v +
          M_op (xCons i (yCons m r')) (xCons k one) v) := by
    have h_lower' :
        T (pow x (k - i)) (M_op (yCons m r') one v) =
          (1 / 2 : ℝ) •
            (M_op (yCons m r') (xCons (k - i - 1) one) v +
              M_op (xCons (k - i - 1) (yCons m r')) one v) := by
      simpa [Eq258XRawRight, show k - i - 1 + 1 = k - i from by omega]
        using ih_lower v
    rw [show U_bilinear (pow x (k - i)) 1 (M_op (yCons m r') one v) =
        T (pow x (k - i)) (M_op (yCons m r') one v) from by
      rw [U_bilinear_one_right]]
    rw [h_lower']
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
      FJ_U_eq, FJ_U_eq]
    rw [M_op_U_prependX, M_op_U_prependX]
    rw [show prependX i (xCons (k - i - 1) (yCons m r')) =
      xCons k (yCons m r') from by
        simp [prependX]
        omega]
    rw [show prependX i (xCons (k - i - 1) one) = xCons k one from by
      simp [prependX]
      omega]
    simp only [show prependX i (yCons m r') = xCons i (yCons m r') from rfl,
      show prependX i one = xCons i one from rfl]
    rw [add_comm]
  have h_big : U_bilinear (pow x (i + 1 + k + 1)) 1 (M_op (yCons m r') one v) =
      (1 / 2 : ℝ) • (M_op (xCons (i + 1 + k) (yCons m r')) one v +
        M_op (yCons m r') (xCons (i + 1 + k) one) v) := by
    rw [U_bilinear_one_right]
    have h := eq258X_yCons_one_exact (i + 1 + k) m r'
    have hv := h v
    simpa [Eq258X, prependX, T_apply] using hv
  rw [h_first]
  rw [h_same]
  rw [show i + 1 + (k + 1) = i + 1 + k + 1 from by omega]
  rw [h_big]
  rw [show i + 1 + k = k + 1 + i from by omega]
  module

/-- Combined long boundary x-direction adapter for second argument `1`.

The swapped same-weight obligation remains explicit; it cannot be discharged from
the total-weight `Eq258DriverIH` alone. -/
theorem eq258X_xCons_yCons_one_from_family_obligations (k i m : ℕ)
    (r' : FreeAssocMono)
    (ih_swap : Eq258X k (yCons m r') (xCons i one))
    (ih_lower : i < k → Eq258XRawRight (k - i - 1) (yCons m r') one) :
    Eq258X k (xCons i (yCons m r')) one := by
  intro v
  by_cases hik : k ≤ i
  · simpa [Eq258X, prependX] using
      eq258_xCons_one_general_ge k i m r' hik (eq258X_xCons_right_of_eq258X ih_swap) v
  · have hlt : i < k := Nat.lt_of_not_ge hik
    simpa [Eq258X, prependX] using
      eq258_xCons_one_general_lt k i m r' hlt (eq258X_xCons_right_of_eq258X ih_swap) v
        (ih_lower hlt)

/-- Long boundary case for the y-direction Eq(2.58), `j ≥ l`, with second argument `1`.

Symmetric to `eq258_xCons_one_general_ge`; the same-weight swapped obligation is
kept explicit for the same reason. -/
theorem eq258_yCons_one_general_ge (l j m : ℕ) (r' : FreeAssocMono)
    (hlj : l ≤ j)
    (ih_swap : ∀ v, T (pow y (l + 1)) (M_op (xCons m r') (yCons j one) v) =
      (1 / 2 : ℝ) • (M_op (yCons l (xCons m r')) (yCons j one) v +
        M_op (xCons m r') (yCons (l + 1 + j) one) v))
    (v : FreeJordanAlg) :
    T (pow y (l + 1)) (M_op (yCons j (xCons m r')) one v) =
    (1 / 2 : ℝ) • (M_op (yCons (l + 1 + j) (xCons m r')) one v +
      M_op (yCons j (xCons m r')) (yCons l one) v) := by
  rw [eq259_yCons_one]
  rw [T_sub, T_smul']
  have h249 := @JordanAlgebra.operator_identity_249 FreeJordanAlg _
    FreeJordanAlg.y (1 : FreeJordanAlg) (l + 1) (j - l)
  have h249v := LinearMap.ext_iff.mp h249 (M_op (xCons m r') one v)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply] at h249v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq, FJ_U_linear_apply] at h249v
  rw [show l + 1 + (j - l) = j + 1 from by omega,
      show l + 1 + (j + 1) = l + 1 + j + 1 from by omega] at h249v
  rw [ih_swap]
  have h249' : T (pow y (l + 1)) (T (pow y (j + 1)) (M_op (xCons m r') one v)) =
    (1 / 2 : ℝ) • (U (pow y (l + 1))
        (U_bilinear (pow y (j - l)) 1 (M_op (xCons m r') one v)) +
      U_bilinear (pow y (l + 1 + j + 1)) 1 (M_op (xCons m r') one v)) := by
    simp only [T_apply] at h249v ⊢
    rw [show mul (pow y (j + 1)) (M_op (xCons m r') one v) =
        U_bilinear (pow y (j + 1)) 1 (M_op (xCons m r') one v) from by
      rw [U_bilinear_one_right]
      rfl]
    rw [show mul (pow y (l + 1))
          (U_bilinear (pow y (j + 1)) 1 (M_op (xCons m r') one v))
        = (1 / 2 : ℝ) • ((2 : ℝ) • mul (pow y (l + 1))
            (U_bilinear (pow y (j + 1)) 1 (M_op (xCons m r') one v))) from by
          rw [smul_smul]
          norm_num,
      h249v]
  rw [h249']
  rw [smul_smul, show (2 : ℝ) * (1 / 2 : ℝ) = 1 from by norm_num, one_smul]
  have h_big : U_bilinear (pow y (l + 1 + j + 1)) 1 (M_op (xCons m r') one v) =
      (1 / 2 : ℝ) • (M_op (yCons (l + 1 + j) (xCons m r')) one v +
        M_op (xCons m r') (yCons (l + 1 + j) one) v) := by
    rw [U_bilinear_one_right]
    have h := eq258Y_xCons_one_exact (l + 1 + j) m r'
    have hv := h v
    simpa [Eq258Y, prependY, T_apply] using hv
  rw [h_big]
  suffices h_key : U (pow y (l + 1))
      (U_bilinear (pow y (j - l)) 1 (M_op (xCons m r') one v)) =
    (1 / 2 : ℝ) • (M_op (yCons l (xCons m r')) (yCons j one) v +
      M_op (yCons j (xCons m r')) (yCons l one) v) by
    rw [h_key]
    module
  by_cases hlj' : j = l
  · subst hlj'
    rw [show pow y (j - j) = 1 from by simp [FreeJordanAlg.pow_zero]]
    rw [U_bilinear_one_left]
    simp only [T_apply, one_mul_eq]
    rw [M_op_yCons_yCons j (xCons m r') one v]
    module
  · have hgt : l < j := Nat.lt_of_le_of_ne hlj (Ne.symm hlj')
    have hbase := eq258Y_xCons_one_exact (j - l - 1) m r'
    have hbasev := hbase v
    have hbase' : U_bilinear (pow y (j - l)) 1 (M_op (xCons m r') one v) =
      (1 / 2 : ℝ) • (M_op (yCons (j - l - 1) (xCons m r')) one v +
        M_op (xCons m r') (yCons (j - l - 1) one) v) := by
      rw [U_bilinear_one_right]
      simpa [Eq258Y, prependY, T_apply, show j - l - 1 + 1 = j - l from by omega]
        using hbasev
    rw [hbase']
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
      FJ_U_eq, FJ_U_eq]
    rw [M_op_U_prependY, M_op_U_prependY]
    rw [show prependY l (yCons (j - l - 1) (xCons m r')) =
      yCons j (xCons m r') from by
        simp [prependY]
        omega]
    rw [show prependY l (yCons (j - l - 1) one) = yCons j one from by
      simp [prependY]
      omega]
    simp only [show prependY l (xCons m r') = yCons l (xCons m r') from rfl,
      show prependY l one = yCons l one from rfl]
    rw [add_comm]

/-- Long boundary case for the y-direction Eq(2.58), `j < l`, with second argument `1`. -/
theorem eq258_yCons_one_general_lt (l j m : ℕ) (r' : FreeAssocMono)
    (hjl : j < l)
    (ih_swap : ∀ v, T (pow y (l + 1)) (M_op (xCons m r') (yCons j one) v) =
      (1 / 2 : ℝ) • (M_op (yCons l (xCons m r')) (yCons j one) v +
        M_op (xCons m r') (yCons (l + 1 + j) one) v))
    (v : FreeJordanAlg)
    (ih_lower : Eq258YRawRight (l - j - 1) (xCons m r') one) :
    T (pow y (l + 1)) (M_op (yCons j (xCons m r')) one v) =
    (1 / 2 : ℝ) • (M_op (yCons (l + 1 + j) (xCons m r')) one v +
      M_op (yCons j (xCons m r')) (yCons l one) v) := by
  rw [eq259_yCons_one]
  rw [T_sub, T_smul']
  have h247 := @JordanAlgebra.operator_identity_247 FreeJordanAlg _
    FreeJordanAlg.y (1 : FreeJordanAlg) (j + 1) (l + 1)
  have h247v := LinearMap.ext_iff.mp h247 (M_op (xCons m r') one v)
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at h247v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq] at h247v
  rw [ih_swap]
  have h247_iso :
      T (pow y (l + 1)) (T (pow y (j + 1)) (M_op (xCons m r') one v)) =
        -T (pow y (j + 1))
            (U_bilinear (pow y (l + 1)) 1 (M_op (xCons m r') one v)) +
          U_bilinear (pow y (j + 1)) (pow y (l + 1))
            (T 1 (M_op (xCons m r') one v)) +
          U_bilinear (pow y (j + 1 + (l + 1))) 1
            (M_op (xCons m r') one v) := by
    rw [← U_bilinear_one_right (pow y (j + 1)) (M_op (xCons m r') one v)]
    calc
      T (pow y (l + 1))
          (U_bilinear (pow y (j + 1)) 1 (M_op (xCons m r') one v)) =
        (T (pow y (l + 1))
            (U_bilinear (pow y (j + 1)) 1 (M_op (xCons m r') one v)) +
          T (pow y (j + 1))
            (U_bilinear (pow y (l + 1)) 1 (M_op (xCons m r') one v))) -
          T (pow y (j + 1))
            (U_bilinear (pow y (l + 1)) 1 (M_op (xCons m r') one v)) := by
          abel
      _ =
        (U_bilinear (pow y (j + 1)) (pow y (l + 1))
            (T 1 (M_op (xCons m r') one v)) +
          U_bilinear (pow y (j + 1 + (l + 1))) 1
            (M_op (xCons m r') one v)) -
          T (pow y (j + 1))
            (U_bilinear (pow y (l + 1)) 1 (M_op (xCons m r') one v)) := by
          rw [h247v]
      _ =
        -T (pow y (j + 1))
            (U_bilinear (pow y (l + 1)) 1 (M_op (xCons m r') one v)) +
          U_bilinear (pow y (j + 1)) (pow y (l + 1))
            (T 1 (M_op (xCons m r') one v)) +
          U_bilinear (pow y (j + 1 + (l + 1))) 1
            (M_op (xCons m r') one v) := by
          abel
  have h249 := @JordanAlgebra.operator_identity_249 FreeJordanAlg _
    FreeJordanAlg.y (1 : FreeJordanAlg) (j + 1) (l - j)
  have h249v := LinearMap.ext_iff.mp h249 (M_op (xCons m r') one v)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply] at h249v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq, FJ_U_linear_apply] at h249v
  rw [show j + 1 + (l - j) = l + 1 from by omega,
      show j + 1 + (l + 1) = j + 1 + l + 1 from by omega] at h249v
  have h249_iso :
      T (pow y (j + 1))
          (U_bilinear (pow y (l + 1)) 1 (M_op (xCons m r') one v)) =
        (1 / 2 : ℝ) •
          (U (pow y (j + 1))
              (U_bilinear (pow y (l - j)) 1 (M_op (xCons m r') one v)) +
            U_bilinear (pow y (j + 1 + l + 1)) 1
              (M_op (xCons m r') one v)) := by
    simp only [T_apply] at h249v ⊢
    rw [show mul (pow y (j + 1))
          (U_bilinear (pow y (l + 1)) 1 (M_op (xCons m r') one v))
        = (1 / 2 : ℝ) • ((2 : ℝ) • mul (pow y (j + 1))
            (U_bilinear (pow y (l + 1)) 1 (M_op (xCons m r') one v))) from by
          rw [smul_smul]
          norm_num,
      h249v]
  rw [h247_iso, h249_iso]
  have h_same :
      U_bilinear (pow y (j + 1)) (pow y (l + 1))
          (T 1 (M_op (xCons m r') one v)) =
        (1 / 2 : ℝ) • (M_op (yCons l (xCons m r')) (yCons j one) v +
          M_op (yCons j (xCons m r')) (yCons l one) v) := by
    simp only [T_apply, one_mul_eq]
    rw [U_bilinear_y_pow_lt_as_U_T j l hjl]
    have h_lower' :
        T (pow y (l - j)) (M_op (xCons m r') one v) =
          (1 / 2 : ℝ) •
            (M_op (xCons m r') (yCons (l - j - 1) one) v +
              M_op (yCons (l - j - 1) (xCons m r')) one v) := by
      simpa [Eq258YRawRight, show l - j - 1 + 1 = l - j from by omega]
        using ih_lower v
    rw [h_lower']
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
      FJ_U_eq, FJ_U_eq]
    rw [M_op_U_prependY, M_op_U_prependY]
    rw [show prependY j (yCons (l - j - 1) (xCons m r')) =
      yCons l (xCons m r') from by
        simp [prependY]
        omega]
    rw [show prependY j (yCons (l - j - 1) one) = yCons l one from by
      simp [prependY]
      omega]
    simp only [show prependY j (xCons m r') = yCons j (xCons m r') from rfl,
      show prependY j one = yCons j one from rfl]
    rw [add_comm]
  have h_first : U (pow y (j + 1))
      (U_bilinear (pow y (l - j)) 1 (M_op (xCons m r') one v)) =
        (1 / 2 : ℝ) • (M_op (yCons l (xCons m r')) (yCons j one) v +
          M_op (yCons j (xCons m r')) (yCons l one) v) := by
    have h_lower' :
        T (pow y (l - j)) (M_op (xCons m r') one v) =
          (1 / 2 : ℝ) •
            (M_op (xCons m r') (yCons (l - j - 1) one) v +
              M_op (yCons (l - j - 1) (xCons m r')) one v) := by
      simpa [Eq258YRawRight, show l - j - 1 + 1 = l - j from by omega]
        using ih_lower v
    rw [show U_bilinear (pow y (l - j)) 1 (M_op (xCons m r') one v) =
        T (pow y (l - j)) (M_op (xCons m r') one v) from by
      rw [U_bilinear_one_right]]
    rw [h_lower']
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
      FJ_U_eq, FJ_U_eq]
    rw [M_op_U_prependY, M_op_U_prependY]
    rw [show prependY j (yCons (l - j - 1) (xCons m r')) =
      yCons l (xCons m r') from by
        simp [prependY]
        omega]
    rw [show prependY j (yCons (l - j - 1) one) = yCons l one from by
      simp [prependY]
      omega]
    simp only [show prependY j (xCons m r') = yCons j (xCons m r') from rfl,
      show prependY j one = yCons j one from rfl]
    rw [add_comm]
  have h_big : U_bilinear (pow y (j + 1 + l + 1)) 1 (M_op (xCons m r') one v) =
      (1 / 2 : ℝ) • (M_op (yCons (j + 1 + l) (xCons m r')) one v +
        M_op (xCons m r') (yCons (j + 1 + l) one) v) := by
    rw [U_bilinear_one_right]
    have h := eq258Y_xCons_one_exact (j + 1 + l) m r'
    have hv := h v
    simpa [Eq258Y, prependY, T_apply] using hv
  rw [h_first]
  rw [h_same]
  rw [show j + 1 + (l + 1) = j + 1 + l + 1 from by omega]
  rw [h_big]
  rw [show j + 1 + l = l + 1 + j from by omega]
  module

/-- Combined long boundary y-direction adapter for second argument `1`. -/
theorem eq258Y_yCons_xCons_one_from_family_obligations (l j m : ℕ)
    (r' : FreeAssocMono)
    (ih_swap : Eq258Y l (xCons m r') (yCons j one))
    (ih_lower : j < l → Eq258YRawRight (l - j - 1) (xCons m r') one) :
    Eq258Y l (yCons j (xCons m r')) one := by
  intro v
  by_cases hlj : l ≤ j
  · simpa [Eq258Y, prependY] using
      eq258_yCons_one_general_ge l j m r' hlj (eq258Y_yCons_right_of_eq258Y ih_swap) v
  · have hlt : j < l := Nat.lt_of_not_ge hlj
    simpa [Eq258Y, prependY] using
      eq258_yCons_one_general_lt l j m r' hlt (eq258Y_yCons_right_of_eq258Y ih_swap) v
        (ih_lower hlt)

/-- Left-boundary x-direction adapter for the long `one / yCons (xCons ...)` case. -/
theorem eq258X_one_yCons_xCons_exact (k j m : ℕ) (r' : FreeAssocMono) :
    Eq258X k one (yCons j (xCons m r')) :=
  eq258X_one_yCons_exact k j (xCons m r')

/-- Left-boundary y-direction adapter for the long `one / xCons (yCons ...)` case. -/
theorem eq258Y_one_xCons_yCons_exact (l i m : ℕ) (r' : FreeAssocMono) :
    Eq258Y l one (xCons i (yCons m r')) :=
  eq258Y_one_xCons_exact l i (yCons m r')

/-- Pure-x/long-y instance of H-O (iv): the recurrence defining
    `M_op (xCons i one) (yCons j (xCons l r))` rearranged into property (iv). -/
theorem M_op_U_bilinear_one_xCons (i j l : ℕ) (r : FreeAssocMono)
    (v : FreeJordanAlg) :
    U_bilinear (pow x (i + 1)) (pow y (j + 1)) (M_op one (xCons l r) v) =
      (1 / 2 : ℝ) • (M_op (xCons i one) (yCons j (xCons l r)) v +
        M_op (yCons j one) (prependX i (xCons l r)) v) := by
  have h : M_op (xCons i one) (yCons j (xCons l r)) v =
      (2 : ℝ) • U_bilinear (pow x (i + 1)) (pow y (j + 1))
          (M_op one (xCons l r) v)
        - M_op (yCons j one) (prependX i (xCons l r)) v := by
    simpa [prependY] using
      (M_op.eq_def (xCons i one) (yCons j (xCons l r)) v)
  have key : (2 : ℝ) • U_bilinear (pow x (i + 1)) (pow y (j + 1))
      (M_op one (xCons l r) v) =
    M_op (xCons i one) (yCons j (xCons l r)) v +
      M_op (yCons j one) (prependX i (xCons l r)) v := by
    rw [h]
    abel
  calc U_bilinear (pow x (i + 1)) (pow y (j + 1)) (M_op one (xCons l r) v)
      = (1 / 2 : ℝ) • ((2 : ℝ) • U_bilinear (pow x (i + 1))
          (pow y (j + 1)) (M_op one (xCons l r) v)) := by
        rw [smul_smul]
        norm_num
    _ = (1 / 2 : ℝ) • (M_op (xCons i one) (yCons j (xCons l r)) v +
        M_op (yCons j one) (prependX i (xCons l r)) v) := by rw [key]

/-- Pure-x/long-y branch of Eq(2.58), `i ≥ k`. This is the swapped partner
    needed for the long x-boundary symmetry layer. -/
theorem eq258_xCons_one_yCons_xCons_ge (k i j l : ℕ) (r : FreeAssocMono)
    (hik : k ≤ i)
    (ih_swap : Eq258X k (yCons j one) (prependX i (xCons l r)))
    (v : FreeJordanAlg) :
    T (pow x (k + 1)) (M_op (xCons i one) (yCons j (xCons l r)) v) =
    (1 / 2 : ℝ) • (M_op (xCons (k + 1 + i) one) (yCons j (xCons l r)) v +
      M_op (xCons i one) (xCons k (yCons j (xCons l r))) v) := by
  rw [M_op.eq_def (xCons i one) (yCons j (xCons l r)) v]
  simp only [prependY]
  rw [T_sub, T_smul']
  have h249 := @JordanAlgebra.operator_identity_249 FreeJordanAlg _
    FreeJordanAlg.x (FreeJordanAlg.pow FreeJordanAlg.y (j + 1)) (k + 1) (i - k)
  have h249v := LinearMap.ext_iff.mp h249 (M_op one (xCons l r) v)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply] at h249v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq, FJ_U_linear_apply] at h249v
  rw [show k + 1 + (i - k) = i + 1 from by omega,
      show k + 1 + (i + 1) = k + 1 + i + 1 from by omega] at h249v
  rw [ih_swap]
  have h249' : T (pow x (k + 1))
      (U_bilinear (pow x (i + 1)) (pow y (j + 1)) (M_op one (xCons l r) v)) =
    (1 / 2 : ℝ) • (U (pow x (k + 1))
        (U_bilinear (pow x (i - k)) (pow y (j + 1)) (M_op one (xCons l r) v)) +
      U_bilinear (pow x (k + 1 + i + 1)) (pow y (j + 1))
        (M_op one (xCons l r) v)) := by
    simp only [T_apply] at h249v ⊢
    rw [show mul (pow x (k + 1))
          (U_bilinear (pow x (i + 1)) (pow y (j + 1)) (M_op one (xCons l r) v))
        = (1 / 2 : ℝ) • ((2 : ℝ) • mul (pow x (k + 1))
            (U_bilinear (pow x (i + 1)) (pow y (j + 1))
              (M_op one (xCons l r) v))) from by
          rw [smul_smul]
          norm_num,
      h249v]
  simp only [T_apply] at h249' ⊢
  rw [h249']
  rw [smul_smul, show (2 : ℝ) * (1 / 2 : ℝ) = 1 from by norm_num, one_smul]
  rw [M_op_U_bilinear_one_xCons (k + 1 + i) j l r v]
  suffices h_key : U (pow x (k + 1))
      (U_bilinear (pow x (i - k)) (pow y (j + 1)) (M_op one (xCons l r) v)) =
    (1 / 2 : ℝ) • (M_op (xCons i one) (xCons k (yCons j (xCons l r))) v +
      M_op (xCons k (yCons j one)) (prependX i (xCons l r)) v) by
    rw [h_key]
    rw [show prependX k (yCons j one) = xCons k (yCons j one) from rfl]
    rw [show prependX k (prependX i (xCons l r)) =
      prependX (k + 1 + i) (xCons l r) from by
        simp [prependX]
        omega]
    module
  by_cases hik' : i = k
  · subst hik'
    rw [show i - i = 0 from by omega]
    rw [show pow x 0 = 1 from FreeJordanAlg.pow_zero x]
    rw [U_bilinear_one_left]
    simp only [T_apply]
    have hbase := eq258Y_one_xCons_exact j l r
    have hbasev := hbase v
    have hbase' : T (pow y (j + 1)) (M_op one (xCons l r) v) =
        (1 / 2 : ℝ) • (M_op (yCons j one) (xCons l r) v +
          M_op one (yCons j (xCons l r)) v) := by
      simpa [Eq258Y, prependY, T_apply] using hbasev
    simp only [T_apply] at hbase'
    rw [hbase']
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
      FJ_U_eq, FJ_U_eq]
    rw [M_op_U_prependX, M_op_U_prependX]
    rw [show prependX i (xCons l r) = xCons (i + 1 + l) r from rfl]
    simp only [show prependX i (yCons j one) = xCons i (yCons j one) from rfl,
      show prependX i one = xCons i one from rfl,
      show prependX i (yCons j (xCons l r)) = xCons i (yCons j (xCons l r)) from rfl]
    rw [add_comm]
  · have hgt : k < i := Nat.lt_of_le_of_ne hik (Ne.symm hik')
    have h_iv := M_op_U_bilinear_one_xCons (i - k - 1) j l r v
    rw [show i - k - 1 + 1 = i - k from by omega] at h_iv
    rw [h_iv]
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
      FJ_U_eq, FJ_U_eq]
    rw [M_op_U_prependX, M_op_U_prependX]
    rw [show prependX k (xCons (i - k - 1) one) = xCons i one from by
      simp [prependX]
      omega]
    rw [show prependX k (prependX (i - k - 1) (xCons l r)) =
      prependX i (xCons l r) from by
        simp [prependX]
        omega]
    simp only [show prependX k (yCons j (xCons l r)) =
      xCons k (yCons j (xCons l r)) from rfl,
      show prependX k (yCons j one) = xCons k (yCons j one) from rfl]

/-- Pure-x/long-y branch of Eq(2.58), `i < k`. The lower pair facts are
    ordinary `Eq258X` facts: the first right argument starts with `x`, so the
    lower right prepend must merge rather than stay raw. -/
theorem eq258_xCons_one_yCons_xCons_lt (k i j l : ℕ) (r : FreeAssocMono)
    (hik : i < k)
    (ih_swap : Eq258X k (yCons j one) (prependX i (xCons l r)))
    (v : FreeJordanAlg)
    (ih_lower_pair :
      T (pow x (k - i)) (M_op (yCons j one) (xCons l r) v) =
        (1 / 2 : ℝ) •
          (M_op (xCons (k - i - 1) (yCons j one)) (xCons l r) v +
            M_op (yCons j one) (prependX (k - i - 1) (xCons l r)) v) ∧
      T (pow x (k - i)) (M_op one (yCons j (xCons l r)) v) =
        (1 / 2 : ℝ) •
          (M_op (xCons (k - i - 1) one) (yCons j (xCons l r)) v +
            M_op one (xCons (k - i - 1) (yCons j (xCons l r))) v)) :
    T (pow x (k + 1)) (M_op (xCons i one) (yCons j (xCons l r)) v) =
    (1 / 2 : ℝ) • (M_op (xCons (k + 1 + i) one) (yCons j (xCons l r)) v +
      M_op (xCons i one) (xCons k (yCons j (xCons l r))) v) := by
  rw [M_op.eq_def (xCons i one) (yCons j (xCons l r)) v]
  simp only [prependY]
  rw [T_sub, T_smul']
  have h247 := @JordanAlgebra.operator_identity_247 FreeJordanAlg _
    FreeJordanAlg.x (FreeJordanAlg.pow FreeJordanAlg.y (j + 1)) (i + 1) (k + 1)
  have h247v := LinearMap.ext_iff.mp h247 (M_op one (xCons l r) v)
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at h247v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq] at h247v
  rw [ih_swap]
  have h247_iso :
      T (pow x (k + 1))
          (U_bilinear (pow x (i + 1)) (pow y (j + 1)) (M_op one (xCons l r) v)) =
        -T (pow x (i + 1))
            (U_bilinear (pow x (k + 1)) (pow y (j + 1)) (M_op one (xCons l r) v)) +
          U_bilinear (pow x (i + 1)) (pow x (k + 1))
            (T (pow y (j + 1)) (M_op one (xCons l r) v)) +
          U_bilinear (pow x (i + 1 + (k + 1))) (pow y (j + 1))
            (M_op one (xCons l r) v) := by
    calc
      T (pow x (k + 1))
          (U_bilinear (pow x (i + 1)) (pow y (j + 1)) (M_op one (xCons l r) v)) =
        (T (pow x (k + 1))
            (U_bilinear (pow x (i + 1)) (pow y (j + 1))
              (M_op one (xCons l r) v)) +
          T (pow x (i + 1))
            (U_bilinear (pow x (k + 1)) (pow y (j + 1))
              (M_op one (xCons l r) v))) -
          T (pow x (i + 1))
            (U_bilinear (pow x (k + 1)) (pow y (j + 1))
              (M_op one (xCons l r) v)) := by
          abel
      _ =
        (U_bilinear (pow x (i + 1)) (pow x (k + 1))
            (T (pow y (j + 1)) (M_op one (xCons l r) v)) +
          U_bilinear (pow x (i + 1 + (k + 1))) (pow y (j + 1))
            (M_op one (xCons l r) v)) -
          T (pow x (i + 1))
            (U_bilinear (pow x (k + 1)) (pow y (j + 1))
              (M_op one (xCons l r) v)) := by
          rw [h247v]
      _ =
        -T (pow x (i + 1))
            (U_bilinear (pow x (k + 1)) (pow y (j + 1))
              (M_op one (xCons l r) v)) +
          U_bilinear (pow x (i + 1)) (pow x (k + 1))
            (T (pow y (j + 1)) (M_op one (xCons l r) v)) +
          U_bilinear (pow x (i + 1 + (k + 1))) (pow y (j + 1))
            (M_op one (xCons l r) v) := by
          abel
  have h249 := @JordanAlgebra.operator_identity_249 FreeJordanAlg _
    FreeJordanAlg.x (FreeJordanAlg.pow FreeJordanAlg.y (j + 1)) (i + 1) (k - i)
  have h249v := LinearMap.ext_iff.mp h249 (M_op one (xCons l r) v)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply] at h249v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq, FJ_U_linear_apply] at h249v
  rw [show i + 1 + (k - i) = k + 1 from by omega,
      show i + 1 + (k + 1) = i + 1 + k + 1 from by omega] at h249v
  have h249_iso :
      T (pow x (i + 1))
          (U_bilinear (pow x (k + 1)) (pow y (j + 1)) (M_op one (xCons l r) v)) =
        (1 / 2 : ℝ) •
          (U (pow x (i + 1))
              (U_bilinear (pow x (k - i)) (pow y (j + 1))
                (M_op one (xCons l r) v)) +
            U_bilinear (pow x (i + 1 + k + 1)) (pow y (j + 1))
              (M_op one (xCons l r) v)) := by
    simp only [T_apply] at h249v ⊢
    rw [show mul (pow x (i + 1))
          (U_bilinear (pow x (k + 1)) (pow y (j + 1))
            (M_op one (xCons l r) v))
        = (1 / 2 : ℝ) • ((2 : ℝ) • mul (pow x (i + 1))
            (U_bilinear (pow x (k + 1)) (pow y (j + 1))
              (M_op one (xCons l r) v))) from by
          rw [smul_smul]
          norm_num,
      h249v]
  rw [h247_iso, h249_iso]
  have h249_first :
      U (pow x (i + 1))
          (U_bilinear (pow x (k - i)) (pow y (j + 1))
            (M_op one (xCons l r) v)) =
        (1 / 2 : ℝ) •
          (M_op (xCons k one) (xCons i (yCons j (xCons l r))) v +
            M_op (xCons i (yCons j one)) (prependX k (xCons l r)) v) := by
    have h_iv := M_op_U_bilinear_one_xCons (k - i - 1) j l r v
    rw [show k - i - 1 + 1 = k - i from by omega] at h_iv
    rw [h_iv]
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
      FJ_U_eq, FJ_U_eq]
    rw [M_op_U_prependX, M_op_U_prependX]
    rw [show prependX i (xCons (k - i - 1) one) = xCons k one from by
      simp [prependX]
      omega]
    rw [show prependX i (prependX (k - i - 1) (xCons l r)) =
      prependX k (xCons l r) from by
        simp [prependX]
        omega]
    simp only [show prependX i (yCons j (xCons l r)) =
      xCons i (yCons j (xCons l r)) from rfl,
      show prependX i (yCons j one) = xCons i (yCons j one) from rfl]
  have h249_second :
      U_bilinear (pow x (i + 1 + k + 1)) (pow y (j + 1))
          (M_op one (xCons l r) v) =
        (1 / 2 : ℝ) •
          (M_op (xCons (i + 1 + k) one) (yCons j (xCons l r)) v +
            M_op (yCons j one) (prependX (i + 1 + k) (xCons l r)) v) := by
    simpa using M_op_U_bilinear_one_xCons (i + 1 + k) j l r v
  rw [h249_first]
  rw [show i + 1 + (k + 1) = i + 1 + k + 1 from by omega]
  rw [h249_second]
  suffices h_same :
      U_bilinear (pow x (i + 1)) (pow x (k + 1))
          (T (pow y (j + 1)) (M_op one (xCons l r) v)) =
        (1 / 4 : ℝ) •
          (M_op (xCons i (yCons j one)) (prependX k (xCons l r)) v +
            M_op (xCons k (yCons j one)) (prependX i (xCons l r)) v +
            M_op (xCons i one) (xCons k (yCons j (xCons l r))) v +
            M_op (xCons k one) (xCons i (yCons j (xCons l r))) v) by
    rw [h_same]
    rw [show i + 1 + k = k + 1 + i from by omega]
    rw [show prependX k (yCons j one) = xCons k (yCons j one) from rfl]
    rw [show prependX k (prependX i (xCons l r)) =
      prependX (k + 1 + i) (xCons l r) from by
        simp [prependX]
        omega]
    module
  suffices h_same_pair :
      U_bilinear (pow x (i + 1)) (pow x (k + 1))
          (M_op (yCons j one) (xCons l r) v) =
        (1 / 2 : ℝ) •
          (M_op (xCons i (yCons j one)) (prependX k (xCons l r)) v +
            M_op (xCons k (yCons j one)) (prependX i (xCons l r)) v) ∧
      U_bilinear (pow x (i + 1)) (pow x (k + 1))
          (M_op one (yCons j (xCons l r)) v) =
        (1 / 2 : ℝ) •
          (M_op (xCons i one) (xCons k (yCons j (xCons l r))) v +
            M_op (xCons k one) (xCons i (yCons j (xCons l r))) v) by
    have hbase := eq258Y_one_xCons_exact j l r
    have hbasev := hbase v
    have hbase' : T (pow y (j + 1)) (M_op one (xCons l r) v) =
        (1 / 2 : ℝ) • (M_op (yCons j one) (xCons l r) v +
          M_op one (yCons j (xCons l r)) v) := by
      simpa [Eq258Y, prependY, T_apply] using hbasev
    rw [hbase']
    rw [← FJ_U_bilinear_eq]
    rw [map_smul, map_add]
    rw [FJ_U_bilinear_eq, FJ_U_bilinear_eq]
    rw [h_same_pair.1, h_same_pair.2]
    module
  constructor
  · rw [U_bilinear_x_pow_lt_as_U_T i k hik]
    rw [ih_lower_pair.1]
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
      FJ_U_eq, FJ_U_eq]
    rw [M_op_U_prependX, M_op_U_prependX]
    rw [show prependX i (prependX (k - i - 1) (xCons l r)) =
      prependX k (xCons l r) from by
        simp [prependX]
        omega]
    rw [show prependX i (xCons (k - i - 1) (yCons j one)) =
      xCons k (yCons j one) from by
        simp [prependX]
        omega]
    simp only [show prependX i (yCons j one) = xCons i (yCons j one) from rfl]
    rw [add_comm]
  · rw [U_bilinear_x_pow_lt_as_U_T i k hik]
    rw [ih_lower_pair.2]
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
      FJ_U_eq, FJ_U_eq]
    rw [M_op_U_prependX, M_op_U_prependX]
    rw [show prependX i (xCons (k - i - 1) one) = xCons k one from by
      simp [prependX]
      omega]
    simp only [show prependX i one = xCons i one from rfl,
      show prependX i (yCons j (xCons l r)) =
        xCons i (yCons j (xCons l r)) from rfl,
      show prependX i (xCons (k - i - 1) (yCons j (xCons l r))) =
        xCons k (yCons j (xCons l r)) from by
          simp [prependX]
          omega]
    rw [add_comm]

/-- Pure-y/long-x instance of H-O (iv), symmetric to
    `M_op_U_bilinear_one_xCons`. -/
theorem M_op_U_bilinear_one_yCons (j i l : ℕ) (r : FreeAssocMono)
    (v : FreeJordanAlg) :
    U_bilinear (pow y (j + 1)) (pow x (i + 1)) (M_op one (yCons l r) v) =
      (1 / 2 : ℝ) • (M_op (yCons j one) (xCons i (yCons l r)) v +
        M_op (xCons i one) (prependY j (yCons l r)) v) := by
  have h : M_op (yCons j one) (xCons i (yCons l r)) v =
      (2 : ℝ) • U_bilinear (pow y (j + 1)) (pow x (i + 1))
          (M_op one (yCons l r) v)
        - M_op (xCons i one) (prependY j (yCons l r)) v := by
    simpa [prependX] using
      (M_op.eq_def (yCons j one) (xCons i (yCons l r)) v)
  have key : (2 : ℝ) • U_bilinear (pow y (j + 1)) (pow x (i + 1))
      (M_op one (yCons l r) v) =
    M_op (yCons j one) (xCons i (yCons l r)) v +
      M_op (xCons i one) (prependY j (yCons l r)) v := by
    rw [h]
    abel
  calc U_bilinear (pow y (j + 1)) (pow x (i + 1)) (M_op one (yCons l r) v)
      = (1 / 2 : ℝ) • ((2 : ℝ) • U_bilinear (pow y (j + 1))
          (pow x (i + 1)) (M_op one (yCons l r) v)) := by
        rw [smul_smul]
        norm_num
    _ = (1 / 2 : ℝ) • (M_op (yCons j one) (xCons i (yCons l r)) v +
        M_op (xCons i one) (prependY j (yCons l r)) v) := by rw [key]

/-- Pure-y/long-x branch of Eq(2.58)'s y-companion, `j ≥ l`. -/
theorem eq258_yCons_one_xCons_yCons_ge (l j i n : ℕ) (r : FreeAssocMono)
    (hlj : l ≤ j)
    (ih_swap : Eq258Y l (xCons i one) (prependY j (yCons n r)))
    (v : FreeJordanAlg) :
    T (pow y (l + 1)) (M_op (yCons j one) (xCons i (yCons n r)) v) =
    (1 / 2 : ℝ) • (M_op (yCons (l + 1 + j) one) (xCons i (yCons n r)) v +
      M_op (yCons j one) (yCons l (xCons i (yCons n r))) v) := by
  rw [M_op.eq_def (yCons j one) (xCons i (yCons n r)) v]
  simp only [prependX]
  rw [T_sub, T_smul']
  have h249 := @JordanAlgebra.operator_identity_249 FreeJordanAlg _
    FreeJordanAlg.y (FreeJordanAlg.pow FreeJordanAlg.x (i + 1)) (l + 1) (j - l)
  have h249v := LinearMap.ext_iff.mp h249 (M_op one (yCons n r) v)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply] at h249v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq, FJ_U_linear_apply] at h249v
  rw [show l + 1 + (j - l) = j + 1 from by omega,
      show l + 1 + (j + 1) = l + 1 + j + 1 from by omega] at h249v
  rw [ih_swap]
  have h249' : T (pow y (l + 1))
      (U_bilinear (pow y (j + 1)) (pow x (i + 1)) (M_op one (yCons n r) v)) =
    (1 / 2 : ℝ) • (U (pow y (l + 1))
        (U_bilinear (pow y (j - l)) (pow x (i + 1)) (M_op one (yCons n r) v)) +
      U_bilinear (pow y (l + 1 + j + 1)) (pow x (i + 1))
        (M_op one (yCons n r) v)) := by
    simp only [T_apply] at h249v ⊢
    rw [show mul (pow y (l + 1))
          (U_bilinear (pow y (j + 1)) (pow x (i + 1)) (M_op one (yCons n r) v))
        = (1 / 2 : ℝ) • ((2 : ℝ) • mul (pow y (l + 1))
            (U_bilinear (pow y (j + 1)) (pow x (i + 1))
              (M_op one (yCons n r) v))) from by
          rw [smul_smul]
          norm_num,
      h249v]
  simp only [T_apply] at h249' ⊢
  rw [h249']
  rw [smul_smul, show (2 : ℝ) * (1 / 2 : ℝ) = 1 from by norm_num, one_smul]
  rw [M_op_U_bilinear_one_yCons (l + 1 + j) i n r v]
  suffices h_key : U (pow y (l + 1))
      (U_bilinear (pow y (j - l)) (pow x (i + 1)) (M_op one (yCons n r) v)) =
    (1 / 2 : ℝ) • (M_op (yCons j one) (yCons l (xCons i (yCons n r))) v +
      M_op (yCons l (xCons i one)) (prependY j (yCons n r)) v) by
    rw [h_key]
    rw [show prependY l (xCons i one) = yCons l (xCons i one) from rfl]
    rw [show prependY l (prependY j (yCons n r)) =
      prependY (l + 1 + j) (yCons n r) from by
        simp [prependY]
        omega]
    module
  by_cases hlj' : j = l
  · subst j
    rw [show l - l = 0 from by omega]
    rw [show pow y 0 = 1 from FreeJordanAlg.pow_zero y]
    rw [U_bilinear_one_left]
    simp only [T_apply]
    have hbase := eq258X_one_yCons_exact i n r
    have hbasev := hbase v
    have hbase' : T (pow x (i + 1)) (M_op one (yCons n r) v) =
        (1 / 2 : ℝ) • (M_op (xCons i one) (yCons n r) v +
          M_op one (xCons i (yCons n r)) v) := by
      simpa [Eq258X, prependX, T_apply] using hbasev
    simp only [T_apply] at hbase'
    rw [hbase']
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
      FJ_U_eq, FJ_U_eq]
    rw [M_op_U_prependY, M_op_U_prependY]
    rw [show prependY l (yCons n r) = yCons (l + 1 + n) r from rfl]
    simp only [show prependY l (xCons i one) = yCons l (xCons i one) from rfl,
      show prependY l one = yCons l one from rfl,
      show prependY l (xCons i (yCons n r)) = yCons l (xCons i (yCons n r)) from rfl]
    rw [add_comm]
  · have hgt : l < j := Nat.lt_of_le_of_ne hlj (Ne.symm hlj')
    have h_iv := M_op_U_bilinear_one_yCons (j - l - 1) i n r v
    rw [show j - l - 1 + 1 = j - l from by omega] at h_iv
    rw [h_iv]
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
      FJ_U_eq, FJ_U_eq]
    rw [M_op_U_prependY, M_op_U_prependY]
    rw [show prependY l (yCons (j - l - 1) one) = yCons j one from by
      simp [prependY]
      omega]
    rw [show prependY l (prependY (j - l - 1) (yCons n r)) =
      prependY j (yCons n r) from by
        simp [prependY]
        omega]
    simp only [show prependY l (xCons i (yCons n r)) =
      yCons l (xCons i (yCons n r)) from rfl,
      show prependY l (xCons i one) = yCons l (xCons i one) from rfl]

/-- Pure-y/long-x branch of Eq(2.58)'s y-companion, `j < l`. -/
theorem eq258_yCons_one_xCons_yCons_lt (l j i n : ℕ) (r : FreeAssocMono)
    (hjl : j < l)
    (ih_swap : Eq258Y l (xCons i one) (prependY j (yCons n r)))
    (v : FreeJordanAlg)
    (ih_lower_pair :
      T (pow y (l - j)) (M_op (xCons i one) (yCons n r) v) =
        (1 / 2 : ℝ) •
          (M_op (yCons (l - j - 1) (xCons i one)) (yCons n r) v +
            M_op (xCons i one) (prependY (l - j - 1) (yCons n r)) v) ∧
      T (pow y (l - j)) (M_op one (xCons i (yCons n r)) v) =
        (1 / 2 : ℝ) •
          (M_op (yCons (l - j - 1) one) (xCons i (yCons n r)) v +
            M_op one (yCons (l - j - 1) (xCons i (yCons n r))) v)) :
    T (pow y (l + 1)) (M_op (yCons j one) (xCons i (yCons n r)) v) =
    (1 / 2 : ℝ) • (M_op (yCons (l + 1 + j) one) (xCons i (yCons n r)) v +
      M_op (yCons j one) (yCons l (xCons i (yCons n r))) v) := by
  rw [M_op.eq_def (yCons j one) (xCons i (yCons n r)) v]
  simp only [prependX]
  rw [T_sub, T_smul']
  have h247 := @JordanAlgebra.operator_identity_247 FreeJordanAlg _
    FreeJordanAlg.y (FreeJordanAlg.pow FreeJordanAlg.x (i + 1)) (j + 1) (l + 1)
  have h247v := LinearMap.ext_iff.mp h247 (M_op one (yCons n r) v)
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at h247v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq] at h247v
  rw [ih_swap]
  have h247_iso :
      T (pow y (l + 1))
          (U_bilinear (pow y (j + 1)) (pow x (i + 1)) (M_op one (yCons n r) v)) =
        -T (pow y (j + 1))
            (U_bilinear (pow y (l + 1)) (pow x (i + 1)) (M_op one (yCons n r) v)) +
          U_bilinear (pow y (j + 1)) (pow y (l + 1))
            (T (pow x (i + 1)) (M_op one (yCons n r) v)) +
          U_bilinear (pow y (j + 1 + (l + 1))) (pow x (i + 1))
            (M_op one (yCons n r) v) := by
    calc
      T (pow y (l + 1))
          (U_bilinear (pow y (j + 1)) (pow x (i + 1)) (M_op one (yCons n r) v)) =
        (T (pow y (l + 1))
            (U_bilinear (pow y (j + 1)) (pow x (i + 1))
              (M_op one (yCons n r) v)) +
          T (pow y (j + 1))
            (U_bilinear (pow y (l + 1)) (pow x (i + 1))
              (M_op one (yCons n r) v))) -
          T (pow y (j + 1))
            (U_bilinear (pow y (l + 1)) (pow x (i + 1))
              (M_op one (yCons n r) v)) := by
          abel
      _ =
        (U_bilinear (pow y (j + 1)) (pow y (l + 1))
            (T (pow x (i + 1)) (M_op one (yCons n r) v)) +
          U_bilinear (pow y (j + 1 + (l + 1))) (pow x (i + 1))
            (M_op one (yCons n r) v)) -
          T (pow y (j + 1))
            (U_bilinear (pow y (l + 1)) (pow x (i + 1))
              (M_op one (yCons n r) v)) := by
          rw [h247v]
      _ =
        -T (pow y (j + 1))
            (U_bilinear (pow y (l + 1)) (pow x (i + 1))
              (M_op one (yCons n r) v)) +
          U_bilinear (pow y (j + 1)) (pow y (l + 1))
            (T (pow x (i + 1)) (M_op one (yCons n r) v)) +
          U_bilinear (pow y (j + 1 + (l + 1))) (pow x (i + 1))
            (M_op one (yCons n r) v) := by
          abel
  have h249 := @JordanAlgebra.operator_identity_249 FreeJordanAlg _
    FreeJordanAlg.y (FreeJordanAlg.pow FreeJordanAlg.x (i + 1)) (j + 1) (l - j)
  have h249v := LinearMap.ext_iff.mp h249 (M_op one (yCons n r) v)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply] at h249v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq, FJ_U_linear_apply] at h249v
  rw [show j + 1 + (l - j) = l + 1 from by omega,
      show j + 1 + (l + 1) = j + 1 + l + 1 from by omega] at h249v
  have h249_iso :
      T (pow y (j + 1))
          (U_bilinear (pow y (l + 1)) (pow x (i + 1)) (M_op one (yCons n r) v)) =
        (1 / 2 : ℝ) •
          (U (pow y (j + 1))
              (U_bilinear (pow y (l - j)) (pow x (i + 1))
                (M_op one (yCons n r) v)) +
            U_bilinear (pow y (j + 1 + l + 1)) (pow x (i + 1))
              (M_op one (yCons n r) v)) := by
    simp only [T_apply] at h249v ⊢
    rw [show mul (pow y (j + 1))
          (U_bilinear (pow y (l + 1)) (pow x (i + 1))
            (M_op one (yCons n r) v))
        = (1 / 2 : ℝ) • ((2 : ℝ) • mul (pow y (j + 1))
            (U_bilinear (pow y (l + 1)) (pow x (i + 1))
              (M_op one (yCons n r) v))) from by
          rw [smul_smul]
          norm_num,
      h249v]
  rw [h247_iso, h249_iso]
  have h249_first :
      U (pow y (j + 1))
          (U_bilinear (pow y (l - j)) (pow x (i + 1))
            (M_op one (yCons n r) v)) =
        (1 / 2 : ℝ) •
          (M_op (yCons l one) (yCons j (xCons i (yCons n r))) v +
            M_op (yCons j (xCons i one)) (prependY l (yCons n r)) v) := by
    have h_iv := M_op_U_bilinear_one_yCons (l - j - 1) i n r v
    rw [show l - j - 1 + 1 = l - j from by omega] at h_iv
    rw [h_iv]
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
      FJ_U_eq, FJ_U_eq]
    rw [M_op_U_prependY, M_op_U_prependY]
    rw [show prependY j (yCons (l - j - 1) one) = yCons l one from by
      simp [prependY]
      omega]
    rw [show prependY j (prependY (l - j - 1) (yCons n r)) =
      prependY l (yCons n r) from by
        simp [prependY]
        omega]
    simp only [show prependY j (xCons i (yCons n r)) =
      yCons j (xCons i (yCons n r)) from rfl,
      show prependY j (xCons i one) = yCons j (xCons i one) from rfl]
  have h249_second :
      U_bilinear (pow y (j + 1 + l + 1)) (pow x (i + 1))
          (M_op one (yCons n r) v) =
        (1 / 2 : ℝ) •
          (M_op (yCons (j + 1 + l) one) (xCons i (yCons n r)) v +
            M_op (xCons i one) (prependY (j + 1 + l) (yCons n r)) v) := by
    simpa using M_op_U_bilinear_one_yCons (j + 1 + l) i n r v
  rw [h249_first]
  rw [show j + 1 + (l + 1) = j + 1 + l + 1 from by omega]
  rw [h249_second]
  suffices h_same :
      U_bilinear (pow y (j + 1)) (pow y (l + 1))
          (T (pow x (i + 1)) (M_op one (yCons n r) v)) =
        (1 / 4 : ℝ) •
          (M_op (yCons j (xCons i one)) (prependY l (yCons n r)) v +
            M_op (yCons l (xCons i one)) (prependY j (yCons n r)) v +
            M_op (yCons j one) (yCons l (xCons i (yCons n r))) v +
            M_op (yCons l one) (yCons j (xCons i (yCons n r))) v) by
    rw [h_same]
    rw [show j + 1 + l = l + 1 + j from by omega]
    rw [show prependY l (xCons i one) = yCons l (xCons i one) from rfl]
    rw [show prependY l (prependY j (yCons n r)) =
      prependY (l + 1 + j) (yCons n r) from by
        simp [prependY]
        omega]
    module
  suffices h_same_pair :
      U_bilinear (pow y (j + 1)) (pow y (l + 1))
          (M_op (xCons i one) (yCons n r) v) =
        (1 / 2 : ℝ) •
          (M_op (yCons j (xCons i one)) (prependY l (yCons n r)) v +
            M_op (yCons l (xCons i one)) (prependY j (yCons n r)) v) ∧
      U_bilinear (pow y (j + 1)) (pow y (l + 1))
          (M_op one (xCons i (yCons n r)) v) =
        (1 / 2 : ℝ) •
          (M_op (yCons j one) (yCons l (xCons i (yCons n r))) v +
            M_op (yCons l one) (yCons j (xCons i (yCons n r))) v) by
    have hbase := eq258X_one_yCons_exact i n r
    have hbasev := hbase v
    have hbase' : T (pow x (i + 1)) (M_op one (yCons n r) v) =
        (1 / 2 : ℝ) • (M_op (xCons i one) (yCons n r) v +
          M_op one (xCons i (yCons n r)) v) := by
      simpa [Eq258X, prependX, T_apply] using hbasev
    rw [hbase']
    rw [← FJ_U_bilinear_eq]
    rw [map_smul, map_add]
    rw [FJ_U_bilinear_eq, FJ_U_bilinear_eq]
    rw [h_same_pair.1, h_same_pair.2]
    module
  constructor
  · rw [U_bilinear_y_pow_lt_as_U_T j l hjl]
    rw [ih_lower_pair.1]
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
      FJ_U_eq, FJ_U_eq]
    rw [M_op_U_prependY, M_op_U_prependY]
    rw [show prependY j (prependY (l - j - 1) (yCons n r)) =
      prependY l (yCons n r) from by
        simp [prependY]
        omega]
    rw [show prependY j (yCons (l - j - 1) (xCons i one)) =
      yCons l (xCons i one) from by
        simp [prependY]
        omega]
    simp only [show prependY j (xCons i one) = yCons j (xCons i one) from rfl]
    rw [add_comm]
  · rw [U_bilinear_y_pow_lt_as_U_T j l hjl]
    rw [ih_lower_pair.2]
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
      FJ_U_eq, FJ_U_eq]
    rw [M_op_U_prependY, M_op_U_prependY]
    rw [show prependY j (yCons (l - j - 1) one) = yCons l one from by
      simp [prependY]
      omega]
    simp only [show prependY j one = yCons j one from rfl,
      show prependY j (xCons i (yCons n r)) =
        yCons j (xCons i (yCons n r)) from rfl,
      show prependY j (yCons (l - j - 1) (xCons i (yCons n r))) =
        yCons l (xCons i (yCons n r)) from by
          simp [prependY]
          omega]
    rw [add_comm]

/-- Driver-ready `i ≥ k` pure-x/long-y branch. -/
theorem eq258X_xCons_one_yCons_xCons_ge_from_driverIH (k i j l : ℕ)
    (r : FreeAssocMono) (hik : k ≤ i)
    (hIH : Eq258DriverIH ((xCons i one).weight + (yCons j (xCons l r)).weight)) :
    Eq258X k (xCons i one) (yCons j (xCons l r)) := by
  intro v
  have h_swap_weight :
      (yCons j one).weight + (prependX i (xCons l r)).weight <
        (xCons i one).weight + (yCons j (xCons l r)).weight := by
    simp [prependX]
  simpa [Eq258X, prependX] using
    eq258_xCons_one_yCons_xCons_ge k i j l r hik
      (hIH.x k (yCons j one) (prependX i (xCons l r)) h_swap_weight) v

/-- Driver-ready `i < k` pure-x/long-y branch. -/
theorem eq258X_xCons_one_yCons_xCons_lt_from_driverIH (k i j l : ℕ)
    (r : FreeAssocMono) (hik : i < k)
    (hIH : Eq258DriverIH ((xCons i one).weight + (yCons j (xCons l r)).weight)) :
    Eq258X k (xCons i one) (yCons j (xCons l r)) := by
  intro v
  have h_swap_weight :
      (yCons j one).weight + (prependX i (xCons l r)).weight <
        (xCons i one).weight + (yCons j (xCons l r)).weight := by
    simp [prependX]
  have h_lower_left_weight :
      (yCons j one).weight + (xCons l r).weight <
        (xCons i one).weight + (yCons j (xCons l r)).weight := by
    simp
  have h_lower_right_weight :
      one.weight + (yCons j (xCons l r)).weight <
        (xCons i one).weight + (yCons j (xCons l r)).weight := by
    simp
  have h_lower_left :
      T (pow x (k - i)) (M_op (yCons j one) (xCons l r) v) =
        (1 / 2 : ℝ) •
          (M_op (xCons (k - i - 1) (yCons j one)) (xCons l r) v +
            M_op (yCons j one) (prependX (k - i - 1) (xCons l r)) v) := by
    have h := hIH.x (k - i - 1) (yCons j one) (xCons l r) h_lower_left_weight
    have hv := h v
    simpa [Eq258X, show k - i - 1 + 1 = k - i from by omega] using hv
  have h_lower_right :
      T (pow x (k - i)) (M_op one (yCons j (xCons l r)) v) =
        (1 / 2 : ℝ) •
          (M_op (xCons (k - i - 1) one) (yCons j (xCons l r)) v +
            M_op one (xCons (k - i - 1) (yCons j (xCons l r))) v) := by
    have h := hIH.x (k - i - 1) one (yCons j (xCons l r)) h_lower_right_weight
    have hv := h v
    simpa [Eq258X, prependX, show k - i - 1 + 1 = k - i from by omega] using hv
  simpa [Eq258X, prependX] using
    eq258_xCons_one_yCons_xCons_lt k i j l r hik
      (hIH.x k (yCons j one) (prependX i (xCons l r)) h_swap_weight) v
      ⟨h_lower_left, h_lower_right⟩

/-- Driver-ready combined pure-x/long-y branch. -/
theorem eq258X_xCons_one_yCons_xCons_from_driverIH (k i j l : ℕ)
    (r : FreeAssocMono)
    (hIH : Eq258DriverIH ((xCons i one).weight + (yCons j (xCons l r)).weight)) :
    Eq258X k (xCons i one) (yCons j (xCons l r)) := by
  by_cases hik : k ≤ i
  · exact eq258X_xCons_one_yCons_xCons_ge_from_driverIH k i j l r hik hIH
  · exact eq258X_xCons_one_yCons_xCons_lt_from_driverIH k i j l r
      (Nat.lt_of_not_ge hik) hIH

/-- Driver-ready `j ≥ l` pure-y/long-x branch. -/
theorem eq258Y_yCons_one_xCons_yCons_ge_from_driverIH (l j i n : ℕ)
    (r : FreeAssocMono) (hlj : l ≤ j)
    (hIH : Eq258DriverIH ((yCons j one).weight + (xCons i (yCons n r)).weight)) :
    Eq258Y l (yCons j one) (xCons i (yCons n r)) := by
  intro v
  have h_swap_weight :
      (xCons i one).weight + (prependY j (yCons n r)).weight <
        (yCons j one).weight + (xCons i (yCons n r)).weight := by
    simp [prependY]
  simpa [Eq258Y, prependY] using
    eq258_yCons_one_xCons_yCons_ge l j i n r hlj
      (hIH.y l (xCons i one) (prependY j (yCons n r)) h_swap_weight) v

/-- Driver-ready `j < l` pure-y/long-x branch. -/
theorem eq258Y_yCons_one_xCons_yCons_lt_from_driverIH (l j i n : ℕ)
    (r : FreeAssocMono) (hjl : j < l)
    (hIH : Eq258DriverIH ((yCons j one).weight + (xCons i (yCons n r)).weight)) :
    Eq258Y l (yCons j one) (xCons i (yCons n r)) := by
  intro v
  have h_swap_weight :
      (xCons i one).weight + (prependY j (yCons n r)).weight <
        (yCons j one).weight + (xCons i (yCons n r)).weight := by
    simp [prependY]
  have h_lower_left_weight :
      (xCons i one).weight + (yCons n r).weight <
        (yCons j one).weight + (xCons i (yCons n r)).weight := by
    simp
  have h_lower_right_weight :
      one.weight + (xCons i (yCons n r)).weight <
        (yCons j one).weight + (xCons i (yCons n r)).weight := by
    simp
  have h_lower_left :
      T (pow y (l - j)) (M_op (xCons i one) (yCons n r) v) =
        (1 / 2 : ℝ) •
          (M_op (yCons (l - j - 1) (xCons i one)) (yCons n r) v +
            M_op (xCons i one) (prependY (l - j - 1) (yCons n r)) v) := by
    have h := hIH.y (l - j - 1) (xCons i one) (yCons n r) h_lower_left_weight
    have hv := h v
    simpa [Eq258Y, show l - j - 1 + 1 = l - j from by omega] using hv
  have h_lower_right :
      T (pow y (l - j)) (M_op one (xCons i (yCons n r)) v) =
        (1 / 2 : ℝ) •
          (M_op (yCons (l - j - 1) one) (xCons i (yCons n r)) v +
            M_op one (yCons (l - j - 1) (xCons i (yCons n r))) v) := by
    have h := hIH.y (l - j - 1) one (xCons i (yCons n r)) h_lower_right_weight
    have hv := h v
    simpa [Eq258Y, prependY, show l - j - 1 + 1 = l - j from by omega] using hv
  simpa [Eq258Y, prependY] using
    eq258_yCons_one_xCons_yCons_lt l j i n r hjl
      (hIH.y l (xCons i one) (prependY j (yCons n r)) h_swap_weight) v
      ⟨h_lower_left, h_lower_right⟩

/-- Driver-ready combined pure-y/long-x branch. -/
theorem eq258Y_yCons_one_xCons_yCons_from_driverIH (l j i n : ℕ)
    (r : FreeAssocMono)
    (hIH : Eq258DriverIH ((yCons j one).weight + (xCons i (yCons n r)).weight)) :
    Eq258Y l (yCons j one) (xCons i (yCons n r)) := by
  by_cases hlj : l ≤ j
  · exact eq258Y_yCons_one_xCons_yCons_ge_from_driverIH l j i n r hlj hIH
  · exact eq258Y_yCons_one_xCons_yCons_lt_from_driverIH l j i n r
      (Nat.lt_of_not_ge hlj) hIH

/-- Build the genuinely long x-boundary swap field from the swapped pure/long
    Eq(2.58) branch, leaving exactly the lower `M_op` symmetry facts exposed by
    the recurrence reducers. -/
theorem eq258X_yCons_xCons_xCons_one_from_driverIH_comm (k i m l : ℕ)
    (r : FreeAssocMono)
    (hIH : Eq258DriverIH ((yCons m (xCons l r)).weight + (xCons i one).weight))
    (h_base : ∀ v : FreeJordanAlg,
      M_op (xCons l r) one v = M_op one (xCons l r) v)
    (h_tail : ∀ a : ℕ, ∀ v : FreeJordanAlg,
      M_op (xCons (a + 1 + l) r) (yCons m one) v =
        M_op (yCons m one) (xCons (a + 1 + l) r) v)
    (h_equal : ∀ v : FreeJordanAlg,
      M_op one (yCons m (xCons l r)) v =
        M_op (yCons m (xCons l r)) one v)
    (h_boundary : ∀ a : ℕ, ∀ v : FreeJordanAlg,
      M_op one (xCons a (yCons m (xCons l r))) v =
        M_op (xCons a (yCons m (xCons l r))) one v) :
    Eq258X k (yCons m (xCons l r)) (xCons i one) := by
  have hIH' :
      Eq258DriverIH ((xCons i one).weight + (yCons m (xCons l r)).weight) := by
    simpa [Nat.add_comm] using hIH
  refine Eq258X_of_swapped_comm
    (eq258X_xCons_one_yCons_xCons_from_driverIH k i m l r hIH') ?_ ?_ ?_
  · intro v
    exact M_op_yCons_xCons_xCons_one_comm_of m l i r v (h_base v) (h_tail i v)
  · intro v
    have h := M_op_xCons_one_xCons_yCons_xCons_comm_of i k m l r v
      (h_equal v) (fun a => h_boundary a v)
      (fun a =>
        (M_op_yCons_xCons_xCons_one_comm_of m l a r v (h_base v) (h_tail a v)).symm)
    simpa [prependX] using h.symm
  · intro v
    simpa [prependX] using
      M_op_yCons_xCons_xCons_one_comm_of m l (k + 1 + i) r v
        (h_base v) (h_tail (k + 1 + i) v)

/-- Build the genuinely long y-boundary swap field from the swapped pure/long
    y-branch, symmetric to
    `eq258X_yCons_xCons_xCons_one_from_driverIH_comm`. -/
theorem eq258Y_xCons_yCons_yCons_one_from_driverIH_comm (l j m n : ℕ)
    (r : FreeAssocMono)
    (hIH : Eq258DriverIH ((xCons m (yCons n r)).weight + (yCons j one).weight))
    (h_base : ∀ v : FreeJordanAlg,
      M_op (yCons n r) one v = M_op one (yCons n r) v)
    (h_tail : ∀ a : ℕ, ∀ v : FreeJordanAlg,
      M_op (yCons (a + 1 + n) r) (xCons m one) v =
        M_op (xCons m one) (yCons (a + 1 + n) r) v)
    (h_equal : ∀ v : FreeJordanAlg,
      M_op one (xCons m (yCons n r)) v =
        M_op (xCons m (yCons n r)) one v)
    (h_boundary : ∀ a : ℕ, ∀ v : FreeJordanAlg,
      M_op one (yCons a (xCons m (yCons n r))) v =
        M_op (yCons a (xCons m (yCons n r))) one v) :
    Eq258Y l (xCons m (yCons n r)) (yCons j one) := by
  have hIH' :
      Eq258DriverIH ((yCons j one).weight + (xCons m (yCons n r)).weight) := by
    simpa [Nat.add_comm] using hIH
  refine Eq258Y_of_swapped_comm
    (eq258Y_yCons_one_xCons_yCons_from_driverIH l j m n r hIH') ?_ ?_ ?_
  · intro v
    exact M_op_xCons_yCons_yCons_one_comm_of m n j r v (h_base v) (h_tail j v)
  · intro v
    have h := M_op_yCons_one_yCons_xCons_yCons_comm_of j l m n r v
      (h_equal v) (fun a => h_boundary a v)
      (fun a =>
        (M_op_xCons_yCons_yCons_one_comm_of m n a r v (h_base v) (h_tail a v)).symm)
    simpa [prependY] using h.symm
  · intro v
    simpa [prependY] using
      M_op_xCons_yCons_yCons_one_comm_of m n (l + 1 + j) r v
        (h_base v) (h_tail (l + 1 + j) v)

/-- The well-formed same-weight boundary layer is recoverable from the ordinary
    lower-weight driver IH plus the recursively proved `M_op` symmetry package. -/
theorem Eq258DriverWFLayer.of_driverIH {n : ℕ} (hIH : Eq258DriverIH n) :
    Eq258DriverWFLayer n where
  lower := hIH
  xBoundarySwapLong := by
    intro k i m l r hw
    have hIH' :
        Eq258DriverIH ((yCons m (xCons l r)).weight + (xCons i one).weight) := by
      rw [hw]
      exact hIH
    exact eq258X_yCons_xCons_xCons_one_from_driverIH_comm k i m l r hIH'
      (fun v => M_op_one_comm (xCons l r) v)
      (fun a v => (M_op_yCons_one_xCons_comm m (a + 1 + l) r v).symm)
      (fun v => (M_op_one_comm (yCons m (xCons l r)) v).symm)
      (fun a v => (M_op_one_comm (xCons a (yCons m (xCons l r))) v).symm)
  yBoundarySwapLong := by
    intro l j m nTail r hw
    have hIH' :
        Eq258DriverIH ((xCons m (yCons nTail r)).weight + (yCons j one).weight) := by
      rw [hw]
      exact hIH
    exact eq258Y_xCons_yCons_yCons_one_from_driverIH_comm l j m nTail r hIH'
      (fun v => M_op_one_comm (yCons nTail r) v)
      (fun a v => (M_op_xCons_one_yCons_comm m (a + 1 + nTail) r v).symm)
      (fun v => (M_op_one_comm (xCons m (yCons nTail r)) v).symm)
      (fun a v => (M_op_one_comm (yCons a (xCons m (yCons nTail r))) v).symm)

/-- Driver-layer version of the long x-boundary constructor case.

This is the first consumer of `Eq258DriverLayer`: the same-weight swapped term is
read from the layer, while the `<` branch's raw-right lower fact is recovered
from the strict lower x-family because both arguments are in `Y`. -/
theorem eq258X_xCons_yCons_one_from_driverLayer (k i m : ℕ) (r' : FreeAssocMono)
    (hLayer : Eq258DriverLayer ((xCons i (yCons m r')).weight + one.weight)) :
    Eq258X k (xCons i (yCons m r')) one := by
  refine eq258X_xCons_yCons_one_from_family_obligations k i m r' ?_ ?_
  · exact hLayer.xBoundarySwap k i m r' (by simp)
  · intro hlt
    have h_lower_weight :
        (yCons m r').weight + one.weight <
          (xCons i (yCons m r')).weight + one.weight := by
      simp
    exact eq258XRawRight_of_eq258X_of_inY (yCons_inY m r') one_inY
      (hLayer.lower.x (k - i - 1) (yCons m r') one h_lower_weight)

/-- Driver-layer version of the long y-boundary constructor case.

Symmetric to `eq258X_xCons_yCons_one_from_driverLayer`: the same-weight swapped
term comes from the layer, and the lower raw-right fact is derived from the
strict lower y-family because both arguments are in `X`. -/
theorem eq258Y_yCons_xCons_one_from_driverLayer (l j m : ℕ) (r' : FreeAssocMono)
    (hLayer : Eq258DriverLayer ((yCons j (xCons m r')).weight + one.weight)) :
    Eq258Y l (yCons j (xCons m r')) one := by
  refine eq258Y_yCons_xCons_one_from_family_obligations l j m r' ?_ ?_
  · exact hLayer.yBoundarySwap l j m r' (by simp)
  · intro hlt
    have h_lower_weight :
        (xCons m r').weight + one.weight <
          (yCons j (xCons m r')).weight + one.weight := by
      simp
    exact eq258YRawRight_of_eq258Y_of_inX (xCons_inX m r') one_inX
      (hLayer.lower.y (l - j - 1) (xCons m r') one h_lower_weight)

/-- Well-formed driver-layer version of the long x-boundary constructor case.

This follows H-O's side conditions: `yCons m r'` is only used as an alternating
monomial when `r' ∈ X`. The pure-tail swapped obligation is discharged by the
swapped weight≤1 base case, so the layer only has to provide genuinely long
swap fields. -/
theorem eq258X_xCons_yCons_one_from_wfDriverLayer (k i m : ℕ) (r' : FreeAssocMono)
    (hr : r'.inX)
    (hLayer : Eq258DriverWFLayer ((xCons i (yCons m r')).weight + one.weight)) :
    Eq258X k (xCons i (yCons m r')) one := by
  refine eq258X_xCons_yCons_one_from_family_obligations k i m r' ?_ ?_
  · exact hLayer.xBoundarySwap k i m r' hr (by simp)
  · intro hlt
    have h_lower_weight :
        (yCons m r').weight + one.weight <
          (xCons i (yCons m r')).weight + one.weight := by
      simp
    exact eq258XRawRight_of_eq258X_of_inY (yCons_inY m r') one_inY
      (hLayer.lower.x (k - i - 1) (yCons m r') one h_lower_weight)

/-- Well-formed driver-layer version of the long y-boundary constructor case.

Symmetric to `eq258X_xCons_yCons_one_from_wfDriverLayer`. -/
theorem eq258Y_yCons_xCons_one_from_wfDriverLayer (l j m : ℕ) (r' : FreeAssocMono)
    (hr : r'.inY)
    (hLayer : Eq258DriverWFLayer ((yCons j (xCons m r')).weight + one.weight)) :
    Eq258Y l (yCons j (xCons m r')) one := by
  refine eq258Y_yCons_xCons_one_from_family_obligations l j m r' ?_ ?_
  · exact hLayer.yBoundarySwap l j m r' hr (by simp)
  · intro hlt
    have h_lower_weight :
        (xCons m r').weight + one.weight <
          (yCons j (xCons m r')).weight + one.weight := by
      simp
    exact eq258YRawRight_of_eq258Y_of_inX (xCons_inX m r') one_inX
      (hLayer.lower.y (l - j - 1) (xCons m r') one h_lower_weight)

/-- Driver-IH version of the long x-boundary constructor case. The current
    same-weight swap is supplied by `Eq258DriverWFLayer.of_driverIH`. -/
theorem eq258X_xCons_yCons_one_from_driverIH (k i m : ℕ) (r' : FreeAssocMono)
    (hr : r'.inX)
    (hIH : Eq258DriverIH ((xCons i (yCons m r')).weight + one.weight)) :
    Eq258X k (xCons i (yCons m r')) one := by
  exact eq258X_xCons_yCons_one_from_wfDriverLayer k i m r' hr
    (Eq258DriverWFLayer.of_driverIH hIH)

/-- Driver-IH version of the long y-boundary constructor case. -/
theorem eq258Y_yCons_xCons_one_from_driverIH (l j m : ℕ) (r' : FreeAssocMono)
    (hr : r'.inY)
    (hIH : Eq258DriverIH ((yCons j (xCons m r')).weight + one.weight)) :
    Eq258Y l (yCons j (xCons m r')) one := by
  exact eq258Y_yCons_xCons_one_from_wfDriverLayer l j m r' hr
    (Eq258DriverWFLayer.of_driverIH hIH)

/-- Y-direction weight > 1, j ≥ l case. Symmetric to
    `eq258_xCons_yCons_general_ge`. -/
theorem eq258_yCons_xCons_general_ge (l j i m : ℕ) (r' : FreeAssocMono)
    (s : FreeAssocMono) (hlj : l ≤ j)
    (ih_swap : ∀ v, T (pow y (l + 1))
        (M_op (prependX i (xCons m r')) (yCons j s) v) =
      (1 / 2 : ℝ) • (M_op (prependY l (prependX i (xCons m r'))) (yCons j s) v
        + M_op (prependX i (xCons m r')) (yCons (l + 1 + j) s) v))
    (v : FreeJordanAlg)
    (ih_x_base : Eq258XBaseObligation i m r' s v) :
    T (pow y (l + 1)) (M_op (yCons j (xCons m r')) (xCons i s) v) =
    (1 / 2 : ℝ) • (M_op (yCons (l + 1 + j) (xCons m r')) (xCons i s) v +
      M_op (yCons j (xCons m r')) (yCons l (xCons i s)) v) := by
  rw [eq259_yCons_xCons]
  rw [T_sub, T_smul']
  have h249 := @JordanAlgebra.operator_identity_249 FreeJordanAlg _
    FreeJordanAlg.y (FreeJordanAlg.pow FreeJordanAlg.x (i + 1)) (l + 1) (j - l)
  have h249v := LinearMap.ext_iff.mp h249 (M_op (xCons m r') s v)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply] at h249v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq, FJ_U_linear_apply] at h249v
  rw [show l + 1 + (j - l) = j + 1 from by omega,
      show l + 1 + (j + 1) = l + 1 + j + 1 from by omega] at h249v
  rw [ih_swap]
  have h249' : mul (pow y (l + 1))
      (U_bilinear (pow y (j + 1)) (pow x (i + 1)) (M_op (xCons m r') s v)) =
    (1 / 2 : ℝ) • (U (pow y (l + 1))
        (U_bilinear (pow y (j - l)) (pow x (i + 1)) (M_op (xCons m r') s v)) +
      U_bilinear (pow y (l + 1 + j + 1)) (pow x (i + 1))
        (M_op (xCons m r') s v)) := by
    simp only [T_apply] at h249v ⊢
    rw [show mul (pow y (l + 1)) (U_bilinear (pow y (j + 1)) (pow x (i + 1))
          (M_op (xCons m r') s v))
        = (1 / 2 : ℝ) • ((2 : ℝ) • mul (pow y (l + 1))
            (U_bilinear (pow y (j + 1)) (pow x (i + 1))
              (M_op (xCons m r') s v))) from by rw [smul_smul]; norm_num,
      h249v]
  simp only [T_apply] at h249' ⊢
  rw [h249']
  rw [smul_smul, show (2 : ℝ) * (1 / 2 : ℝ) = 1 from by norm_num, one_smul]
  rw [M_op_U_bilinear_xCons i (l + 1 + j) m r' s v]
  suffices h_key : U (pow y (l + 1))
      (U_bilinear (pow y (j - l)) (pow x (i + 1)) (M_op (xCons m r') s v)) =
    (1 / 2 : ℝ) • (M_op (prependY l (prependX i (xCons m r'))) (yCons j s) v +
      M_op (yCons j (xCons m r')) (yCons l (xCons i s)) v) by
    suffices h_mod :
        (1 / 2 : ℝ) • (M_op (prependY l (prependX i (xCons m r'))) (yCons j s) v +
          M_op (yCons j (xCons m r')) (yCons l (xCons i s)) v) +
        (1 / 2 : ℝ) • (M_op (yCons (l + 1 + j) (xCons m r')) (xCons i s) v +
          M_op (prependX i (xCons m r')) (yCons (l + 1 + j) s) v) -
        (1 / 2 : ℝ) • (M_op (prependY l (prependX i (xCons m r'))) (yCons j s) v +
          M_op (prependX i (xCons m r')) (yCons (l + 1 + j) s) v) =
      (1 / 2 : ℝ) • (M_op (yCons (l + 1 + j) (xCons m r')) (xCons i s) v +
        M_op (yCons j (xCons m r')) (yCons l (xCons i s)) v) by
      rw [h_key]; exact h_mod
    module
  by_cases hlj' : j = l
  · subst j
    simp only [Nat.sub_self, pow_zero, U_bilinear_one_left, T_apply]
    rw [ih_x_base]
    rw [show prependY l (prependX i (xCons m r')) =
      yCons l (prependX i (xCons m r')) from rfl]
    rw [M_op_yCons_yCons l (prependX i (xCons m r')) s v,
        M_op_yCons_yCons l (xCons m r') (xCons i s) v]
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right, FJ_U_eq, FJ_U_eq]
  · have hgt : l < j := Nat.lt_of_le_of_ne hlj (Ne.symm hlj')
    have h_iv := M_op_U_bilinear_xCons i (j - l - 1) m r' s v
    rw [show j - l - 1 + 1 = j - l from by omega] at h_iv
    rw [h_iv]
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right, FJ_U_eq, FJ_U_eq]
    rw [M_op_U_prependY, M_op_U_prependY]
    rw [add_comm]
    rw [show prependY l (yCons (j - l - 1) (xCons m r')) =
      yCons j (xCons m r') from by
        simp [prependY]; omega]
    rw [show prependY l (yCons (j - l - 1) s) = yCons j s from by
      simp [prependY]; omega]
    simp only [show prependY l (xCons i s) = yCons l (xCons i s) from rfl]

/-- Y-direction weight > 1, j < l case. Symmetric to
    `eq258_xCons_yCons_general_lt`. -/
theorem eq258_yCons_xCons_general_lt (l j i m : ℕ) (r' : FreeAssocMono)
    (s : FreeAssocMono) (hjl : j < l)
    (ih_swap : ∀ v, T (pow y (l + 1))
        (M_op (prependX i (xCons m r')) (yCons j s) v) =
      (1 / 2 : ℝ) • (M_op (prependY l (prependX i (xCons m r'))) (yCons j s) v
        + M_op (prependX i (xCons m r')) (yCons (l + 1 + j) s) v))
    (v : FreeJordanAlg)
    (ih_x_base : Eq258XBaseObligation i m r' s v)
    (ih_lower_pair :
      T (pow y (l - j)) (M_op (prependX i (xCons m r')) s v) =
        (1 / 2 : ℝ) •
          (M_op (prependX i (xCons m r')) (yCons (l - j - 1) s) v +
            M_op (yCons (l - j - 1) (prependX i (xCons m r'))) s v) ∧
      T (pow y (l - j)) (M_op (xCons m r') (xCons i s) v) =
        (1 / 2 : ℝ) •
          (M_op (xCons m r') (yCons (l - j - 1) (xCons i s)) v +
            M_op (yCons (l - j - 1) (xCons m r')) (xCons i s) v)) :
    T (pow y (l + 1)) (M_op (yCons j (xCons m r')) (xCons i s) v) =
    (1 / 2 : ℝ) • (M_op (yCons (l + 1 + j) (xCons m r')) (xCons i s) v +
      M_op (yCons j (xCons m r')) (yCons l (xCons i s)) v) := by
  rw [eq259_yCons_xCons]
  rw [T_sub, T_smul']
  have h247 := @JordanAlgebra.operator_identity_247 FreeJordanAlg _
    FreeJordanAlg.y (FreeJordanAlg.pow FreeJordanAlg.x (i + 1)) (j + 1) (l + 1)
  have h247v := LinearMap.ext_iff.mp h247 (M_op (xCons m r') s v)
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at h247v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq] at h247v
  rw [ih_swap]
  have h247_iso :
      T (pow y (l + 1))
          (U_bilinear (pow y (j + 1)) (pow x (i + 1)) (M_op (xCons m r') s v)) =
        -T (pow y (j + 1))
            (U_bilinear (pow y (l + 1)) (pow x (i + 1)) (M_op (xCons m r') s v)) +
          U_bilinear (pow y (j + 1)) (pow y (l + 1))
            (T (pow x (i + 1)) (M_op (xCons m r') s v)) +
          U_bilinear (pow y (j + 1 + (l + 1))) (pow x (i + 1))
            (M_op (xCons m r') s v) := by
    calc
      T (pow y (l + 1))
          (U_bilinear (pow y (j + 1)) (pow x (i + 1)) (M_op (xCons m r') s v))
          =
        (T (pow y (l + 1))
            (U_bilinear (pow y (j + 1)) (pow x (i + 1))
              (M_op (xCons m r') s v)) +
          T (pow y (j + 1))
            (U_bilinear (pow y (l + 1)) (pow x (i + 1))
              (M_op (xCons m r') s v))) -
          T (pow y (j + 1))
            (U_bilinear (pow y (l + 1)) (pow x (i + 1))
              (M_op (xCons m r') s v)) := by
          abel
      _ =
        (U_bilinear (pow y (j + 1)) (pow y (l + 1))
            (T (pow x (i + 1)) (M_op (xCons m r') s v)) +
          U_bilinear (pow y (j + 1 + (l + 1))) (pow x (i + 1))
            (M_op (xCons m r') s v)) -
          T (pow y (j + 1))
            (U_bilinear (pow y (l + 1)) (pow x (i + 1))
              (M_op (xCons m r') s v)) := by
          rw [h247v]
      _ =
        -T (pow y (j + 1))
            (U_bilinear (pow y (l + 1)) (pow x (i + 1))
              (M_op (xCons m r') s v)) +
          U_bilinear (pow y (j + 1)) (pow y (l + 1))
            (T (pow x (i + 1)) (M_op (xCons m r') s v)) +
          U_bilinear (pow y (j + 1 + (l + 1))) (pow x (i + 1))
            (M_op (xCons m r') s v) := by
          abel
  have h249 := @JordanAlgebra.operator_identity_249 FreeJordanAlg _
    FreeJordanAlg.y (FreeJordanAlg.pow FreeJordanAlg.x (i + 1)) (j + 1) (l - j)
  have h249v := LinearMap.ext_iff.mp h249 (M_op (xCons m r') s v)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply] at h249v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq, FJ_U_linear_apply] at h249v
  rw [show j + 1 + (l - j) = l + 1 from by omega,
      show j + 1 + (l + 1) = j + 1 + l + 1 from by omega] at h249v
  have h249_iso :
      T (pow y (j + 1))
          (U_bilinear (pow y (l + 1)) (pow x (i + 1)) (M_op (xCons m r') s v)) =
        (1 / 2 : ℝ) •
          (U (pow y (j + 1))
              (U_bilinear (pow y (l - j)) (pow x (i + 1))
                (M_op (xCons m r') s v)) +
            U_bilinear (pow y (j + 1 + l + 1)) (pow x (i + 1))
              (M_op (xCons m r') s v)) := by
    simp only [T_apply] at h249v ⊢
    rw [show mul (pow y (j + 1))
          (U_bilinear (pow y (l + 1)) (pow x (i + 1))
            (M_op (xCons m r') s v))
        = (1 / 2 : ℝ) • ((2 : ℝ) • mul (pow y (j + 1))
            (U_bilinear (pow y (l + 1)) (pow x (i + 1))
              (M_op (xCons m r') s v))) from by rw [smul_smul]; norm_num,
      h249v]
  rw [h247_iso, h249_iso]
  have h249_first :
      U (pow y (j + 1))
          (U_bilinear (pow y (l - j)) (pow x (i + 1))
            (M_op (xCons m r') s v)) =
        (1 / 2 : ℝ) •
          (M_op (yCons l (xCons m r')) (yCons j (xCons i s)) v +
            M_op (prependY j (prependX i (xCons m r'))) (yCons l s) v) := by
    have h_iv := M_op_U_bilinear_xCons i (l - j - 1) m r' s v
    rw [show l - j - 1 + 1 = l - j from by omega] at h_iv
    rw [h_iv]
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
      FJ_U_eq, FJ_U_eq]
    rw [M_op_U_prependY, M_op_U_prependY]
    rw [show prependY j (yCons (l - j - 1) (xCons m r')) =
      yCons l (xCons m r') from by
        simp [prependY]; omega]
    rw [show prependY j (yCons (l - j - 1) s) = yCons l s from by
      simp [prependY]; omega]
    simp only [show prependY j (xCons i s) = yCons j (xCons i s) from rfl]
  have h249_second :
      U_bilinear (pow y (j + 1 + l + 1)) (pow x (i + 1))
          (M_op (xCons m r') s v) =
        (1 / 2 : ℝ) •
          (M_op (yCons (j + 1 + l) (xCons m r')) (xCons i s) v +
            M_op (prependX i (xCons m r')) (yCons (j + 1 + l) s) v) := by
    simpa [show j + 1 + l + 1 = j + 1 + l + 1 from rfl] using
      M_op_U_bilinear_xCons i (j + 1 + l) m r' s v
  rw [h249_first]
  rw [show j + 1 + (l + 1) = j + 1 + l + 1 from by omega]
  rw [h249_second]
  suffices h_same :
      U_bilinear (pow y (j + 1)) (pow y (l + 1))
          (T (pow x (i + 1)) (M_op (xCons m r') s v)) =
        (1 / 4 : ℝ) •
          (M_op (prependY j (prependX i (xCons m r'))) (yCons l s) v +
            M_op (prependY l (prependX i (xCons m r'))) (yCons j s) v +
            M_op (yCons j (xCons m r')) (yCons l (xCons i s)) v +
            M_op (yCons l (xCons m r')) (yCons j (xCons i s)) v) by
    rw [h_same]
    rw [show j + 1 + l = l + 1 + j from by omega]
    module
  suffices h_same_pair :
      U_bilinear (pow y (j + 1)) (pow y (l + 1))
          (M_op (prependX i (xCons m r')) s v) =
        (1 / 2 : ℝ) •
          (M_op (prependY j (prependX i (xCons m r'))) (yCons l s) v +
            M_op (prependY l (prependX i (xCons m r'))) (yCons j s) v) ∧
      U_bilinear (pow y (j + 1)) (pow y (l + 1))
          (M_op (xCons m r') (xCons i s) v) =
        (1 / 2 : ℝ) •
          (M_op (yCons j (xCons m r')) (yCons l (xCons i s)) v +
            M_op (yCons l (xCons m r')) (yCons j (xCons i s)) v) by
    have h_same_left := h_same_pair.1
    have h_same_right := h_same_pair.2
    simp only [T_apply]
    rw [ih_x_base]
    rw [← FJ_U_bilinear_eq]
    rw [map_smul, map_add]
    rw [FJ_U_bilinear_eq, FJ_U_bilinear_eq]
    rw [h_same_left, h_same_right]
    module
  suffices h_lower_pair :
      T (pow y (l - j)) (M_op (prependX i (xCons m r')) s v) =
        (1 / 2 : ℝ) •
          (M_op (prependX i (xCons m r')) (yCons (l - j - 1) s) v +
            M_op (yCons (l - j - 1) (prependX i (xCons m r'))) s v) ∧
      T (pow y (l - j)) (M_op (xCons m r') (xCons i s) v) =
        (1 / 2 : ℝ) •
          (M_op (xCons m r') (yCons (l - j - 1) (xCons i s)) v +
            M_op (yCons (l - j - 1) (xCons m r')) (xCons i s) v) by
    constructor
    · rw [U_bilinear_y_pow_lt_as_U_T j l hjl]
      rw [h_lower_pair.1]
      rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
        FJ_U_eq, FJ_U_eq]
      rw [show prependY j (prependX i (xCons m r')) =
        yCons j (prependX i (xCons m r')) from by simp [prependX, prependY]]
      rw [show prependY l (prependX i (xCons m r')) =
        yCons l (prependX i (xCons m r')) from by simp [prependX, prependY]]
      rw [M_op.eq_def (yCons j (prependX i (xCons m r'))) (yCons l s)]
      rw [M_op.eq_def (yCons l (prependX i (xCons m r'))) (yCons j s)]
      simp only [ge_iff_le]
      rw [dif_neg (by omega : ¬ l ≤ j), dif_pos (by omega : j ≤ l)]
      simp only [show ¬ l = j from by omega, ↓reduceIte]
    · rw [U_bilinear_y_pow_lt_as_U_T j l hjl]
      rw [h_lower_pair.2]
      rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
        FJ_U_eq, FJ_U_eq]
      rw [M_op.eq_def (yCons j (xCons m r')) (yCons l (xCons i s))]
      rw [M_op.eq_def (yCons l (xCons m r')) (yCons j (xCons i s))]
      simp only [ge_iff_le]
      rw [dif_neg (by omega : ¬ l ≤ j), dif_pos (by omega : j ≤ l)]
      simp only [show ¬ l = j from by omega, ↓reduceIte]
  exact ih_lower_pair

/-- Y-direction weight > 1, `j ≥ l`, with family-shaped obligations. -/
theorem eq258_yCons_xCons_general_ge_from_families (l j i m : ℕ)
    (r' s : FreeAssocMono) (hlj : l ≤ j) (hs : s.inY)
    (ih_swap : Eq258Y l (prependX i (xCons m r')) (yCons j s))
    (ih_x : Eq258X i (xCons m r') s) (v : FreeJordanAlg) :
    T (pow y (l + 1)) (M_op (yCons j (xCons m r')) (xCons i s) v) =
    (1 / 2 : ℝ) • (M_op (yCons (l + 1 + j) (xCons m r')) (xCons i s) v +
      M_op (yCons j (xCons m r')) (yCons l (xCons i s)) v) := by
  exact eq258_yCons_xCons_general_ge l j i m r' s hlj
    (eq258Y_yCons_right_of_eq258Y ih_swap) v
    (eq258XBaseObligation_of_eq258X hs ih_x)

/-- Y-direction weight > 1, `j < l`, with family-shaped obligations and raw
    lower-pair facts left explicit. -/
theorem eq258_yCons_xCons_general_lt_from_families (l j i m : ℕ)
    (r' s : FreeAssocMono) (hjl : j < l) (hs : s.inY)
    (ih_swap : Eq258Y l (prependX i (xCons m r')) (yCons j s))
    (ih_x : Eq258X i (xCons m r') s) (v : FreeJordanAlg)
    (ih_lower_pair :
      T (pow y (l - j)) (M_op (prependX i (xCons m r')) s v) =
        (1 / 2 : ℝ) •
          (M_op (prependX i (xCons m r')) (yCons (l - j - 1) s) v +
            M_op (yCons (l - j - 1) (prependX i (xCons m r'))) s v) ∧
      T (pow y (l - j)) (M_op (xCons m r') (xCons i s) v) =
        (1 / 2 : ℝ) •
          (M_op (xCons m r') (yCons (l - j - 1) (xCons i s)) v +
            M_op (yCons (l - j - 1) (xCons m r')) (xCons i s) v)) :
    T (pow y (l + 1)) (M_op (yCons j (xCons m r')) (xCons i s) v) =
    (1 / 2 : ℝ) • (M_op (yCons (l + 1 + j) (xCons m r')) (xCons i s) v +
      M_op (yCons j (xCons m r')) (yCons l (xCons i s)) v) := by
  exact eq258_yCons_xCons_general_lt l j i m r' s hjl
    (eq258Y_yCons_right_of_eq258Y ih_swap) v
    (eq258XBaseObligation_of_eq258X hs ih_x) ih_lower_pair

/-- Y-direction weight > 1, `j < l`, with all remaining obligations supplied
    from named theorem-family predicates. -/
theorem eq258_yCons_xCons_general_lt_from_family_obligations (l j i m : ℕ)
    (r' s : FreeAssocMono) (hjl : j < l) (hs : s.inY)
    (ih_swap : Eq258Y l (prependX i (xCons m r')) (yCons j s))
    (ih_x : Eq258X i (xCons m r') s)
    (v : FreeJordanAlg)
    (ih_lower_left : Eq258YRawRight (l - j - 1) (prependX i (xCons m r')) s)
    (ih_lower_right : Eq258Y (l - j - 1) (xCons m r') (xCons i s)) :
    T (pow y (l + 1)) (M_op (yCons j (xCons m r')) (xCons i s) v) =
    (1 / 2 : ℝ) • (M_op (yCons (l + 1 + j) (xCons m r')) (xCons i s) v +
      M_op (yCons j (xCons m r')) (yCons l (xCons i s)) v) := by
  have h_right :
      T (pow y (l - j)) (M_op (xCons m r') (xCons i s) v) =
        (1 / 2 : ℝ) •
          (M_op (xCons m r') (yCons (l - j - 1) (xCons i s)) v +
            M_op (yCons (l - j - 1) (xCons m r')) (xCons i s) v) := by
    have h := eq258Y_xCons_xCons_lower_of_eq258Y ih_lower_right v
    simpa [show l - j - 1 + 1 = l - j from by omega] using h
  have h_left :
      T (pow y (l - j)) (M_op (prependX i (xCons m r')) s v) =
        (1 / 2 : ℝ) •
          (M_op (prependX i (xCons m r')) (yCons (l - j - 1) s) v +
            M_op (yCons (l - j - 1) (prependX i (xCons m r'))) s v) := by
    have h := eq258YRawRight_lower_left_of_family ih_lower_left v
    simpa [show l - j - 1 + 1 = l - j from by omega] using h
  exact eq258_yCons_xCons_general_lt_from_families l j i m r' s hjl hs ih_swap ih_x v
    ⟨h_left, h_right⟩

/-- Combined y-direction weight > 1 yCons/xCons adapter. -/
theorem eq258_yCons_xCons_general_from_family_obligations (l j i m : ℕ)
    (r' s : FreeAssocMono) (hs : s.inY)
    (ih_swap : Eq258Y l (prependX i (xCons m r')) (yCons j s))
    (ih_x : Eq258X i (xCons m r') s)
    (ih_lower_left :
      j < l → Eq258YRawRight (l - j - 1) (prependX i (xCons m r')) s)
    (ih_lower_right : j < l → Eq258Y (l - j - 1) (xCons m r') (xCons i s))
    (v : FreeJordanAlg) :
    T (pow y (l + 1)) (M_op (yCons j (xCons m r')) (xCons i s) v) =
    (1 / 2 : ℝ) • (M_op (yCons (l + 1 + j) (xCons m r')) (xCons i s) v +
      M_op (yCons j (xCons m r')) (yCons l (xCons i s)) v) := by
  by_cases hlj : l ≤ j
  · exact eq258_yCons_xCons_general_ge_from_families l j i m r' s hlj hs ih_swap ih_x v
  · have hjl : j < l := Nat.lt_of_not_ge hlj
    exact eq258_yCons_xCons_general_lt_from_family_obligations l j i m r' s hjl hs
      ih_swap ih_x v (ih_lower_left hjl) (ih_lower_right hjl)

/-- Driver-ready y-direction constructor case:
    `p = yCons j (xCons m r')`, `q = xCons i s`. -/
theorem eq258Y_yCons_xCons_from_driverIH (l j i m : ℕ) (r' s : FreeAssocMono)
    (hs : s.inY)
    (hIH : Eq258DriverIH ((yCons j (xCons m r')).weight + (xCons i s).weight)) :
    Eq258Y l (yCons j (xCons m r')) (xCons i s) := by
  intro v
  have h_swap_weight :
      (prependX i (xCons m r')).weight + (yCons j s).weight <
        (yCons j (xCons m r')).weight + (xCons i s).weight := by
    simp [prependX]
  have h_x_weight :
      (xCons m r').weight + s.weight <
        (yCons j (xCons m r')).weight + (xCons i s).weight := by
    simp
    omega
  have h_lower_left_weight :
      (prependX i (xCons m r')).weight + s.weight <
        (yCons j (xCons m r')).weight + (xCons i s).weight := by
    simp [prependX]
    omega
  have h_lower_right_weight :
      (xCons m r').weight + (xCons i s).weight <
        (yCons j (xCons m r')).weight + (xCons i s).weight := by
    simp
  simpa [Eq258Y, prependY] using
    eq258_yCons_xCons_general_from_family_obligations l j i m r' s hs
      (hIH.y l (prependX i (xCons m r')) (yCons j s) h_swap_weight)
      (hIH.x i (xCons m r') s h_x_weight)
      (fun _ =>
        hIH.rawRightY (l - j - 1) (prependX i (xCons m r')) s h_lower_left_weight)
      (fun _ =>
        hIH.y (l - j - 1) (xCons m r') (xCons i s) h_lower_right_weight)
      v

/-- (2.58) weight > 1, i ≥ k case: T_{x^{k+1}} M_{x^{i+1}·(y^m·r'), y^{j+1}·s}.
    H-O lines 1346-1367. Proof structure:
    1. Expand LHS via (2.59) = M_op recurrence
    2. Distribute T over sub and smul (T_sub, T_smul')
    3. Apply (2.49) to the 2·T_{x^{k+1}} U_{x^{i+1},y^{j+1}} term
    4. Apply induction (ih_swap) to the T_{x^{k+1}} M_{swapped} term
    5. Group U_{x^{k+1}} factors using property (iii) (M_op_U_prependX)
    6. Apply (iv) (M_op_U_bilinear_yCons) to convert U_bilinear to M_op terms
    7. Expand RHS using (2.55a), cancel, close by algebra. -/
theorem eq258_xCons_yCons_general_ge (k i j m : ℕ) (r' : FreeAssocMono)
    (s : FreeAssocMono) (hik : k ≤ i)
    -- IH: eq258 for swapped term M_{y^{j+1}·(y^m·r'), x^{i+1}·s}
    -- Weight decreases: prependY merges y-blocks, so
    -- w(prependY j (yCons m r')) + w(xCons i s) < w(xCons i (yCons m r')) + w(yCons j s)
    -- H-O line 1354: "by induction, (iv) to the second"
    (ih_swap : ∀ v, T (pow x (k + 1))
        (M_op (prependY j (yCons m r')) (xCons i s) v) =
      (1/2 : ℝ) • (M_op (prependX k (prependY j (yCons m r'))) (xCons i s) v
        + M_op (prependY j (yCons m r')) (xCons (k + 1 + i) s) v))
    (v : FreeJordanAlg)
    (ih_y_base : Eq258YBaseObligation j m r' s v) :
    T (pow x (k + 1)) (M_op (xCons i (yCons m r')) (yCons j s) v) =
    (1/2 : ℝ) • (M_op (xCons (k + 1 + i) (yCons m r')) (yCons j s) v +
                  M_op (xCons i (yCons m r')) (xCons k (yCons j s)) v) := by
  -- Step 1: Expand LHS via (2.59) = M_op recurrence (H-O lines 1350-1352)
  rw [eq259_xCons_yCons]
  -- Step 2: Distribute T over sub and smul
  rw [T_sub, T_smul']
  -- Step 3: Apply (2.49) to 2·T_{x^{k+1}}(U_bi(x^{i+1},y^{j+1})(...))
  -- (2.49) with a=x, m=k+1, k'=i-k, b=y^{j+1}:
  -- 2·T_{a^m} U_{a^{m+k'},b} = U_{a^m} U_{a^{k'},b} + U_{a^{2m+k'},b}
  have h249 := @JordanAlgebra.operator_identity_249 FreeJordanAlg _
    FreeJordanAlg.x (FreeJordanAlg.pow FreeJordanAlg.y (j + 1)) (k + 1) (i - k)
  have h249v := LinearMap.ext_iff.mp h249 (M_op (yCons m r') s v)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply] at h249v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq, FJ_U_linear_apply] at h249v
  rw [show k + 1 + (i - k) = i + 1 from by omega,
      show k + 1 + (i + 1) = k + 1 + i + 1 from by omega] at h249v
  -- h249v: 2 • mul(x^{k+1})(U_bi(x^{i+1},y^{j+1})(w)) =
  --   U(x^{k+1})(U_bi(x^{i-k},y^{j+1})(w)) + U_bi(x^{k+1+i+1},y^{j+1})(w)
  -- where w = M_op (yCons m r') s v
  -- Step 4: Apply ih_swap to the T_{x^{k+1}} M_{swapped} term
  rw [ih_swap]
  -- Step 5: Halve h249v to get expression for mul term
  have h249' : mul (pow x (k + 1))
      (U_bilinear (pow x (i + 1)) (pow y (j + 1)) (M_op (yCons m r') s v)) =
    (1/2 : ℝ) • (U (pow x (k + 1))
        (U_bilinear (pow x (i - k)) (pow y (j + 1)) (M_op (yCons m r') s v)) +
      U_bilinear (pow x (k + 1 + i + 1)) (pow y (j + 1))
        (M_op (yCons m r') s v)) := by
    simp only [T_apply] at h249v ⊢
    rw [show mul (pow x (k + 1)) (U_bilinear (pow x (i + 1)) (pow y (j + 1))
          (M_op (yCons m r') s v))
        = (1/2 : ℝ) • ((2 : ℝ) • mul (pow x (k + 1))
            (U_bilinear (pow x (i + 1)) (pow y (j + 1))
              (M_op (yCons m r') s v))) from by rw [smul_smul]; norm_num,
      h249v]
  simp only [T_apply] at h249' ⊢
  rw [h249']
  -- Remaining goal (H-O lines 1358-1367):
  -- (1/2)•(U(x^{k+1})(U_bi(x^{i-k},y^{j+1})(w)) + U_bi(x^{k+1+i+1},y^{j+1})(w))
  -- - (1/2)•(M(prependX k (prependY j (yCons m r')), xCons i s)(v)
  --        + M(prependY j (yCons m r'), xCons(k+1+i) s)(v))
  -- = (1/2)•(M(xCons(k+1+i)(yCons m r'), yCons j s)(v)
  --        + M(xCons i (yCons m r'), xCons k (yCons j s))(v))
  --
  -- Step 5: Simplify 2•(1/2)•X = X (avoiding norm_num which triggers simp unfolding)
  rw [smul_smul, show (2:ℝ) * (1/2:ℝ) = 1 from by norm_num, one_smul]
  -- Step 6: Apply M_op_U_bilinear_yCons to standalone U_bi term (property iv)
  rw [M_op_U_bilinear_yCons (k + 1 + i) j m r' s v]
  -- Step 7: Reduce to h_key via module arithmetic (D terms cancel)
  suffices h_key : U (pow x (k + 1))
      (U_bilinear (pow x (i - k)) (pow y (j + 1)) (M_op (yCons m r') s v)) =
    (1/2 : ℝ) • (M_op (prependX k (prependY j (yCons m r'))) (xCons i s) v +
      M_op (xCons i (yCons m r')) (xCons k (yCons j s)) v) by
    suffices h_mod :
        (1/2 : ℝ) • (M_op (prependX k (prependY j (yCons m r'))) (xCons i s) v +
          M_op (xCons i (yCons m r')) (xCons k (yCons j s)) v) +
        (1/2 : ℝ) • (M_op (xCons (k + 1 + i) (yCons m r')) (yCons j s) v +
          M_op (prependY j (yCons m r')) (xCons (k + 1 + i) s) v) -
        (1/2 : ℝ) • (M_op (prependX k (prependY j (yCons m r'))) (xCons i s) v +
          M_op (prependY j (yCons m r')) (xCons (k + 1 + i) s) v) =
      (1/2 : ℝ) • (M_op (xCons (k + 1 + i) (yCons m r')) (yCons j s) v +
        M_op (xCons i (yCons m r')) (xCons k (yCons j s)) v) by
      rw [h_key]; exact h_mod
    module
  -- Step 8: Prove h_key by cases on i = k vs i > k
  by_cases hik' : i = k
  · -- Case i = k: U_bi(x^0, y^{j+1})(w) = T(y^{j+1})(w)
    -- This requires M_op composition (U applied to nested M_op)
    subst hik'
    simp only [Nat.sub_self, pow_zero, U_bilinear_one_left, T_apply]
    -- Goal: mul(y^{j+1})(w) = (1/2)•(E + F)
    -- Use the y-direction base obligation to convert mul(y) to M_op, then fold into U.
    rw [ih_y_base]
    -- Fold RHS M_op terms via M_op_xCons_xCons
    rw [show prependX i (prependY j (yCons m r')) =
      xCons i (prependY j (yCons m r')) from rfl]
    rw [M_op_xCons_xCons i (prependY j (yCons m r')) s v,
        M_op_xCons_xCons i (yCons m r') (yCons j s) v]
    -- Distribute U over (1/2)•(P₁ + P₂) on LHS
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right, FJ_U_eq, FJ_U_eq]
  · -- Case i > k: standard M_op conversion
    have hgt : k < i := Nat.lt_of_le_of_ne hik (Ne.symm hik')
    have h_iv := M_op_U_bilinear_yCons (i - k - 1) j m r' s v
    rw [show i - k - 1 + 1 = i - k from by omega] at h_iv
    rw [h_iv]
    -- Distribute U over (1/2)•(A + B)
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right, FJ_U_eq, FJ_U_eq]
    -- Apply M_op_U_prependX to each M_op argument
    rw [M_op_U_prependX, M_op_U_prependX]
    -- After prependX, terms are in swapped order from goal. Fix with add_comm.
    rw [add_comm]
    -- Simplify prependX merging: k+1+(i-k-1) = i
    rw [show prependX k (xCons (i - k - 1) (yCons m r')) = xCons i (yCons m r') from by
      simp [prependX]; omega]
    rw [show prependX k (xCons (i - k - 1) s) = xCons i s from by
      simp [prependX]; omega]
    simp only [show prependX k (yCons j s) = xCons k (yCons j s) from rfl]

/-- (2.58) weight > 1, i < k case: T_{x^{k+1}} M_{x^{i+1}·(y^m·r'), y^{j+1}·s}.
    H-O lines 1369-1377. Proof structure:
    1. Expand LHS via (2.59) = M_op recurrence
    2. Distribute T over sub and smul
    3. Apply (2.47) to decompose T_{x^{k+1}} U_{x^{i+1},y^{j+1}}
    4. Apply induction (ih_swap) to the T_{x^{k+1}} M_{swapped} term
    5. Use (2.49) on the resulting T_{x^{i+1}} U_{x^{k+1},y^{j+1}} term
    6. Use the lower-power IH exposed by `U_bilinear_x_pow_lt_as_U_T`
    7. Apply property (iii) and (iv), cancel, close by algebra. -/
theorem eq258_xCons_yCons_general_lt (k i j m : ℕ) (r' : FreeAssocMono)
    (s : FreeAssocMono) (hik : i < k)
    -- IH: eq258 for swapped term (same as ge case)
    (ih_swap : ∀ v, T (pow x (k + 1))
        (M_op (prependY j (yCons m r')) (xCons i s) v) =
      (1 / 2 : ℝ) • (M_op (prependX k (prependY j (yCons m r'))) (xCons i s) v
        + M_op (prependY j (yCons m r')) (xCons (k + 1 + i) s) v))
    (v : FreeJordanAlg)
    (ih_y_base : Eq258YBaseObligation j m r' s v)
    -- Lower-power IH needed after `U_bilinear_x_pow_lt_as_U_T` turns
    -- `U_{x^{i+1},x^{k+1}}` into `U_{x^{i+1}} T_{x^{k-i}}`.
    (ih_lower_pair :
      T (pow x (k - i)) (M_op (prependY j (yCons m r')) s v) =
        (1 / 2 : ℝ) •
          (M_op (prependY j (yCons m r')) (xCons (k - i - 1) s) v +
            M_op (xCons (k - i - 1) (prependY j (yCons m r'))) s v) ∧
      T (pow x (k - i)) (M_op (yCons m r') (yCons j s) v) =
        (1 / 2 : ℝ) •
          (M_op (yCons m r') (xCons (k - i - 1) (yCons j s)) v +
            M_op (xCons (k - i - 1) (yCons m r')) (yCons j s) v)) :
    T (pow x (k + 1)) (M_op (xCons i (yCons m r')) (yCons j s) v) =
    (1 / 2 : ℝ) • (M_op (xCons (k + 1 + i) (yCons m r')) (yCons j s) v +
      M_op (xCons i (yCons m r')) (xCons k (yCons j s)) v) := by
  -- Step 1: Expand LHS via (2.59) (H-O line 1369)
  rw [eq259_xCons_yCons]
  -- Step 2: Distribute T
  rw [T_sub, T_smul']
  -- Step 3: Apply (2.47) to the 2·T_{x^{k+1}} U_{x^{i+1},y^{j+1}} term
  -- (2.47) with a=x, m=i+1, n=k+1, b=y^{j+1}:
  -- T_{a^n} U_{a^m,b} + T_{a^m} U_{a^n,b} = U_{a^m,a^n} T_b + U_{a^{m+n},b}
  have h247 := @JordanAlgebra.operator_identity_247 FreeJordanAlg _
    FreeJordanAlg.x (FreeJordanAlg.pow FreeJordanAlg.y (j + 1)) (i + 1) (k + 1)
  have h247v := LinearMap.ext_iff.mp h247 (M_op (yCons m r') s v)
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at h247v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq] at h247v
  -- h247v: T(x^{k+1})(U_bi(x^{i+1},y^{j+1})(w)) + T(x^{i+1})(U_bi(x^{k+1},y^{j+1})(w)) =
  --   U_bi(x^{i+1},x^{k+1})(T(y^{j+1})(w)) + U_bi(x^{i+k+2},y^{j+1})(w)
  -- Step 4: Apply ih_swap to the T_{x^{k+1}} M_{swapped} term
  rw [ih_swap]
  -- Step 5a: Rearrange (2.47) to isolate the T_{x^{k+1}} U_{x^{i+1},y^{j+1}}
  -- term. This is the first line of H-O's calculation after applying induction:
  -- T_{x^k} U_{x^i,y^j} = -T_{x^i} U_{x^k,y^j}
  --   + U_{x^i,x^k} T_{y^j} + U_{x^{i+k},y^j}.
  have h247_iso :
      T (pow x (k + 1))
          (U_bilinear (pow x (i + 1)) (pow y (j + 1)) (M_op (yCons m r') s v)) =
        -T (pow x (i + 1))
            (U_bilinear (pow x (k + 1)) (pow y (j + 1)) (M_op (yCons m r') s v)) +
          U_bilinear (pow x (i + 1)) (pow x (k + 1))
            (T (pow y (j + 1)) (M_op (yCons m r') s v)) +
          U_bilinear (pow x (i + 1 + (k + 1))) (pow y (j + 1))
            (M_op (yCons m r') s v) := by
    calc
      T (pow x (k + 1))
          (U_bilinear (pow x (i + 1)) (pow y (j + 1)) (M_op (yCons m r') s v))
          =
        (T (pow x (k + 1))
            (U_bilinear (pow x (i + 1)) (pow y (j + 1))
              (M_op (yCons m r') s v)) +
          T (pow x (i + 1))
            (U_bilinear (pow x (k + 1)) (pow y (j + 1))
              (M_op (yCons m r') s v))) -
          T (pow x (i + 1))
            (U_bilinear (pow x (k + 1)) (pow y (j + 1))
              (M_op (yCons m r') s v)) := by
          abel
      _ =
        (U_bilinear (pow x (i + 1)) (pow x (k + 1))
            (T (pow y (j + 1)) (M_op (yCons m r') s v)) +
          U_bilinear (pow x (i + 1 + (k + 1))) (pow y (j + 1))
            (M_op (yCons m r') s v)) -
          T (pow x (i + 1))
            (U_bilinear (pow x (k + 1)) (pow y (j + 1))
              (M_op (yCons m r') s v)) := by
          rw [h247v]
      _ =
        -T (pow x (i + 1))
            (U_bilinear (pow x (k + 1)) (pow y (j + 1))
              (M_op (yCons m r') s v)) +
          U_bilinear (pow x (i + 1)) (pow x (k + 1))
            (T (pow y (j + 1)) (M_op (yCons m r') s v)) +
          U_bilinear (pow x (i + 1 + (k + 1))) (pow y (j + 1))
            (M_op (yCons m r') s v) := by
          abel
  -- Step 5b: Apply (2.49) to the first term exposed by `h247_iso`.
  have h249 := @JordanAlgebra.operator_identity_249 FreeJordanAlg _
    FreeJordanAlg.x (FreeJordanAlg.pow FreeJordanAlg.y (j + 1)) (i + 1) (k - i)
  have h249v := LinearMap.ext_iff.mp h249 (M_op (yCons m r') s v)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply] at h249v
  simp only [FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq, FJ_U_linear_apply] at h249v
  rw [show i + 1 + (k - i) = k + 1 from by omega,
      show i + 1 + (k + 1) = i + 1 + k + 1 from by omega] at h249v
  have h249_iso :
      T (pow x (i + 1))
          (U_bilinear (pow x (k + 1)) (pow y (j + 1)) (M_op (yCons m r') s v)) =
        (1 / 2 : ℝ) •
          (U (pow x (i + 1))
              (U_bilinear (pow x (k - i)) (pow y (j + 1))
                (M_op (yCons m r') s v)) +
            U_bilinear (pow x (i + 1 + k + 1)) (pow y (j + 1))
              (M_op (yCons m r') s v)) := by
    simp only [T_apply] at h249v ⊢
    rw [show mul (pow x (i + 1))
          (U_bilinear (pow x (k + 1)) (pow y (j + 1))
            (M_op (yCons m r') s v))
        = (1 / 2 : ℝ) • ((2 : ℝ) • mul (pow x (i + 1))
            (U_bilinear (pow x (k + 1)) (pow y (j + 1))
              (M_op (yCons m r') s v))) from by rw [smul_smul]; norm_num,
      h249v]
  rw [h247_iso, h249_iso]
  -- Step 5c: Convert the mixed `U_{x^{k-i},y^{j+1}}` term exposed by (2.49),
  -- then push the outer `U_{x^{i+1}}` through the resulting two M-operators.
  -- This is the first summand in H-O line 1373.
  have h249_first :
      U (pow x (i + 1))
          (U_bilinear (pow x (k - i)) (pow y (j + 1))
            (M_op (yCons m r') s v)) =
        (1 / 2 : ℝ) •
          (M_op (xCons k (yCons m r')) (xCons i (yCons j s)) v +
            M_op (prependX i (prependY j (yCons m r'))) (xCons k s) v) := by
    have h_iv := M_op_U_bilinear_yCons (k - i - 1) j m r' s v
    rw [show k - i - 1 + 1 = k - i from by omega] at h_iv
    rw [h_iv]
    rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
      FJ_U_eq, FJ_U_eq]
    rw [M_op_U_prependX, M_op_U_prependX]
    rw [show prependX i (xCons (k - i - 1) (yCons m r')) =
      xCons k (yCons m r') from by
        simp [prependX]; omega]
    rw [show prependX i (xCons (k - i - 1) s) = xCons k s from by
      simp [prependX]; omega]
    simp only [show prependX i (yCons j s) = xCons i (yCons j s) from rfl]
  -- Step 5d: Convert the standalone mixed `U_{x^{i+k+2},y^{j+1}}` term.
  have h249_second :
      U_bilinear (pow x (i + 1 + k + 1)) (pow y (j + 1))
          (M_op (yCons m r') s v) =
        (1 / 2 : ℝ) •
          (M_op (xCons (i + 1 + k) (yCons m r')) (yCons j s) v +
            M_op (prependY j (yCons m r')) (xCons (i + 1 + k) s) v) := by
    simpa [show i + 1 + k + 1 = i + 1 + k + 1 from rfl] using
      M_op_U_bilinear_yCons (i + 1 + k) j m r' s v
  rw [h249_first]
  rw [show i + 1 + (k + 1) = i + 1 + k + 1 from by omega]
  rw [h249_second]
  -- Step 5e: The remaining H-O algebra closes once the same-letter
  -- linearized property (iii) is available on the two M-operators produced by
  -- the y-base case.
  suffices h_same :
      U_bilinear (pow x (i + 1)) (pow x (k + 1))
          (T (pow y (j + 1)) (M_op (yCons m r') s v)) =
        (1 / 4 : ℝ) •
          (M_op (prependX i (prependY j (yCons m r'))) (xCons k s) v +
            M_op (prependX k (prependY j (yCons m r'))) (xCons i s) v +
            M_op (xCons i (yCons m r')) (xCons k (yCons j s)) v +
            M_op (xCons k (yCons m r')) (xCons i (yCons j s)) v) by
    rw [h_same]
    rw [show i + 1 + k = k + 1 + i from by omega]
    module
  suffices h_same_pair :
      U_bilinear (pow x (i + 1)) (pow x (k + 1))
          (M_op (prependY j (yCons m r')) s v) =
        (1 / 2 : ℝ) •
          (M_op (prependX i (prependY j (yCons m r'))) (xCons k s) v +
            M_op (prependX k (prependY j (yCons m r'))) (xCons i s) v) ∧
      U_bilinear (pow x (i + 1)) (pow x (k + 1))
          (M_op (yCons m r') (yCons j s) v) =
        (1 / 2 : ℝ) •
          (M_op (xCons i (yCons m r')) (xCons k (yCons j s)) v +
            M_op (xCons k (yCons m r')) (xCons i (yCons j s)) v) by
    have h_same_left := h_same_pair.1
    have h_same_right := h_same_pair.2
    simp only [T_apply]
    rw [ih_y_base]
    rw [← FJ_U_bilinear_eq]
    rw [map_smul, map_add]
    rw [FJ_U_bilinear_eq, FJ_U_bilinear_eq]
    rw [h_same_left, h_same_right]
    module
  suffices h_lower_pair :
      T (pow x (k - i)) (M_op (prependY j (yCons m r')) s v) =
        (1 / 2 : ℝ) •
          (M_op (prependY j (yCons m r')) (xCons (k - i - 1) s) v +
            M_op (xCons (k - i - 1) (prependY j (yCons m r'))) s v) ∧
      T (pow x (k - i)) (M_op (yCons m r') (yCons j s) v) =
        (1 / 2 : ℝ) •
          (M_op (yCons m r') (xCons (k - i - 1) (yCons j s)) v +
            M_op (xCons (k - i - 1) (yCons m r')) (yCons j s) v) by
    constructor
    · rw [U_bilinear_x_pow_lt_as_U_T i k hik]
      rw [h_lower_pair.1]
      rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
        FJ_U_eq, FJ_U_eq]
      rw [show prependX i (prependY j (yCons m r')) =
        xCons i (prependY j (yCons m r')) from by simp [prependX, prependY]]
      rw [show prependX k (prependY j (yCons m r')) =
        xCons k (prependY j (yCons m r')) from by simp [prependX, prependY]]
      rw [M_op.eq_def (xCons i (prependY j (yCons m r'))) (xCons k s)]
      rw [M_op.eq_def (xCons k (prependY j (yCons m r'))) (xCons i s)]
      simp only [ge_iff_le]
      rw [dif_neg (by omega : ¬ k ≤ i), dif_pos (by omega : i ≤ k)]
      simp only [show ¬ k = i from by omega, ↓reduceIte]
    · rw [U_bilinear_x_pow_lt_as_U_T i k hik]
      rw [h_lower_pair.2]
      rw [← FJ_U_eq, JordanAlgebra.U_smul_right, JordanAlgebra.U_add_right,
        FJ_U_eq, FJ_U_eq]
      rw [M_op.eq_def (xCons i (yCons m r')) (xCons k (yCons j s))]
      rw [M_op.eq_def (xCons k (yCons m r')) (xCons i (yCons j s))]
      simp only [ge_iff_le]
      rw [dif_neg (by omega : ¬ k ≤ i), dif_pos (by omega : i ≤ k)]
      simp only [show ¬ k = i from by omega, ↓reduceIte]
  exact ih_lower_pair

/-- Weight > 1, `i ≥ k`, with the swapped and y-base obligations supplied from
    the Eq(2.58) theorem-family predicates. This is the adapter shape expected
    from the eventual simultaneous induction driver. -/
theorem eq258_xCons_yCons_general_ge_from_families (k i j m : ℕ)
    (r' s : FreeAssocMono) (hik : k ≤ i) (hs : s.inX)
    (ih_swap : Eq258X k (prependY j (yCons m r')) (xCons i s))
    (ih_y : Eq258Y j (yCons m r') s) (v : FreeJordanAlg) :
    T (pow x (k + 1)) (M_op (xCons i (yCons m r')) (yCons j s) v) =
    (1 / 2 : ℝ) • (M_op (xCons (k + 1 + i) (yCons m r')) (yCons j s) v +
      M_op (xCons i (yCons m r')) (xCons k (yCons j s)) v) := by
  exact eq258_xCons_yCons_general_ge k i j m r' s hik
    (eq258X_xCons_right_of_eq258X ih_swap) v
    (eq258YBaseObligation_of_eq258Y hs ih_y)

/-- Weight > 1, `i < k`, with the swapped and y-base obligations supplied from
    the Eq(2.58) theorem-family predicates. The lower-pair facts remain explicit:
    they are the remaining simultaneous-induction obligations for this branch. -/
theorem eq258_xCons_yCons_general_lt_from_families (k i j m : ℕ)
    (r' s : FreeAssocMono) (hik : i < k) (hs : s.inX)
    (ih_swap : Eq258X k (prependY j (yCons m r')) (xCons i s))
    (ih_y : Eq258Y j (yCons m r') s) (v : FreeJordanAlg)
    (ih_lower_pair :
      T (pow x (k - i)) (M_op (prependY j (yCons m r')) s v) =
        (1 / 2 : ℝ) •
          (M_op (prependY j (yCons m r')) (xCons (k - i - 1) s) v +
            M_op (xCons (k - i - 1) (prependY j (yCons m r'))) s v) ∧
      T (pow x (k - i)) (M_op (yCons m r') (yCons j s) v) =
        (1 / 2 : ℝ) •
          (M_op (yCons m r') (xCons (k - i - 1) (yCons j s)) v +
            M_op (xCons (k - i - 1) (yCons m r')) (yCons j s) v)) :
    T (pow x (k + 1)) (M_op (xCons i (yCons m r')) (yCons j s) v) =
    (1 / 2 : ℝ) • (M_op (xCons (k + 1 + i) (yCons m r')) (yCons j s) v +
      M_op (xCons i (yCons m r')) (xCons k (yCons j s)) v) := by
  exact eq258_xCons_yCons_general_lt k i j m r' s hik
    (eq258X_xCons_right_of_eq258X ih_swap) v
    (eq258YBaseObligation_of_eq258Y hs ih_y) ih_lower_pair

/-- Weight > 1, `i < k`, with all remaining obligations supplied from named
    theorem-family predicates. The left lower-pair obligation uses
    `Eq258XRawRight` because the current recurrence-helper algebra keeps the
    right product unmerged as `xCons _ s`. -/
theorem eq258_xCons_yCons_general_lt_from_family_obligations (k i j m : ℕ)
    (r' s : FreeAssocMono) (hik : i < k) (hs : s.inX)
    (ih_swap : Eq258X k (prependY j (yCons m r')) (xCons i s))
    (ih_y : Eq258Y j (yCons m r') s)
    (v : FreeJordanAlg)
    (ih_lower_left : Eq258XRawRight (k - i - 1) (prependY j (yCons m r')) s)
    (ih_lower_right : Eq258X (k - i - 1) (yCons m r') (yCons j s)) :
    T (pow x (k + 1)) (M_op (xCons i (yCons m r')) (yCons j s) v) =
    (1 / 2 : ℝ) • (M_op (xCons (k + 1 + i) (yCons m r')) (yCons j s) v +
      M_op (xCons i (yCons m r')) (xCons k (yCons j s)) v) := by
  have h_right :
      T (pow x (k - i)) (M_op (yCons m r') (yCons j s) v) =
        (1 / 2 : ℝ) •
          (M_op (yCons m r') (xCons (k - i - 1) (yCons j s)) v +
            M_op (xCons (k - i - 1) (yCons m r')) (yCons j s) v) := by
    have h := eq258X_yCons_yCons_lower_of_eq258X ih_lower_right v
    simpa [show k - i - 1 + 1 = k - i from by omega] using h
  have h_left :
      T (pow x (k - i)) (M_op (prependY j (yCons m r')) s v) =
        (1 / 2 : ℝ) •
          (M_op (prependY j (yCons m r')) (xCons (k - i - 1) s) v +
            M_op (xCons (k - i - 1) (prependY j (yCons m r'))) s v) := by
    have h := eq258XRawRight_lower_left_of_family ih_lower_left v
    simpa [show k - i - 1 + 1 = k - i from by omega] using h
  exact eq258_xCons_yCons_general_lt_from_families k i j m r' s hik hs ih_swap ih_y v
    ⟨h_left, h_right⟩

/-- Combined weight > 1 xCons/yCons adapter. It selects the H-O `i ≥ k` or
    `i < k` helper internally, leaving only the induction-family obligations
    needed by the selected branch. -/
theorem eq258_xCons_yCons_general_from_family_obligations (k i j m : ℕ)
    (r' s : FreeAssocMono) (hs : s.inX)
    (ih_swap : Eq258X k (prependY j (yCons m r')) (xCons i s))
    (ih_y : Eq258Y j (yCons m r') s)
    (ih_lower_left :
      i < k → Eq258XRawRight (k - i - 1) (prependY j (yCons m r')) s)
    (ih_lower_right : i < k → Eq258X (k - i - 1) (yCons m r') (yCons j s))
    (v : FreeJordanAlg) :
    T (pow x (k + 1)) (M_op (xCons i (yCons m r')) (yCons j s) v) =
    (1 / 2 : ℝ) • (M_op (xCons (k + 1 + i) (yCons m r')) (yCons j s) v +
      M_op (xCons i (yCons m r')) (xCons k (yCons j s)) v) := by
  by_cases hik : k ≤ i
  · exact eq258_xCons_yCons_general_ge_from_families k i j m r' s hik hs ih_swap ih_y v
  · have hlt : i < k := Nat.lt_of_not_ge hik
    exact eq258_xCons_yCons_general_lt_from_family_obligations k i j m r' s hlt hs
      ih_swap ih_y v (ih_lower_left hlt) (ih_lower_right hlt)

/-- Driver-ready constructor case for H-O's weight > 1 branch:
    `p = xCons i (yCons m r')`, `q = yCons j s`. All recursive obligations are
    obtained from the weight-indexed simultaneous IH package. -/
theorem eq258X_xCons_yCons_from_driverIH (k i j m : ℕ) (r' s : FreeAssocMono)
    (hs : s.inX)
    (hIH : Eq258DriverIH ((xCons i (yCons m r')).weight + (yCons j s).weight)) :
    Eq258X k (xCons i (yCons m r')) (yCons j s) := by
  intro v
  have h_swap_weight :
      (prependY j (yCons m r')).weight + (xCons i s).weight <
        (xCons i (yCons m r')).weight + (yCons j s).weight := by
    simp [prependY]
  have h_y_weight :
      (yCons m r').weight + s.weight <
        (xCons i (yCons m r')).weight + (yCons j s).weight := by
    simp
    omega
  have h_lower_left_weight :
      (prependY j (yCons m r')).weight + s.weight <
        (xCons i (yCons m r')).weight + (yCons j s).weight := by
    simp [prependY]
    omega
  have h_lower_right_weight :
      (yCons m r').weight + (yCons j s).weight <
        (xCons i (yCons m r')).weight + (yCons j s).weight := by
    simp
  simpa [Eq258X, prependX] using
    eq258_xCons_yCons_general_from_family_obligations k i j m r' s hs
      (hIH.x k (prependY j (yCons m r')) (xCons i s) h_swap_weight)
      (hIH.y j (yCons m r') s h_y_weight)
      (fun _ =>
        hIH.rawRight (k - i - 1) (prependY j (yCons m r')) s h_lower_left_weight)
      (fun _ =>
        hIH.x (k - i - 1) (yCons m r') (yCons j s) h_lower_right_weight)
      v

/-! ### Well-formed driver dispatchers -/

/-- Complete x-direction dispatcher for the H-O well-formed side conditions
    `p ∈ X`, `q ∈ Y`. This is the case split needed by the eventual global
    driver once it has reduced to alternating monomials. -/
theorem eq258X_of_driverIH_of_inX_inY (k : ℕ) (p q : FreeAssocMono)
    (hp : p.inX) (hq : q.inY) (hwp : p.WF) (hwq : q.WF)
    (hIH : Eq258DriverIH (p.weight + q.weight)) :
    Eq258X k p q := by
  cases p with
  | one =>
    cases q with
    | one =>
      exact eq258X_one_one k
    | xCons j s =>
      cases hq with
      | inl h => cases h
      | inr h => simp [inY0, startsWithY] at h
    | yCons j s =>
      cases s with
      | one =>
        exact eq258X_one_yCons_one k j
      | xCons m rest =>
        exact eq258X_one_yCons_xCons_exact k j m rest
      | yCons m rest =>
        cases hwq.1 with
        | inl h => cases h
        | inr h => simp [inX0, startsWithX] at h
  | xCons i r =>
    cases q with
    | one =>
      cases r with
      | one =>
        exact eq258X_xCons_one_one k i
      | xCons m rest =>
        cases hwp.1 with
        | inl h => cases h
        | inr h => simp [inY0, startsWithY] at h
      | yCons m rest =>
        exact eq258X_xCons_yCons_one_from_driverIH k i m rest hwp.2.1 hIH
    | xCons j s =>
      cases hq with
      | inl h => cases h
      | inr h => simp [inY0, startsWithY] at h
    | yCons j s =>
      cases r with
      | one =>
        cases s with
        | one =>
          exact eq258X_xCons_one_yCons_one k i j
        | xCons l rest =>
          exact eq258X_xCons_one_yCons_xCons_from_driverIH k i j l rest hIH
        | yCons l rest =>
          cases hwq.1 with
          | inl h => cases h
          | inr h => simp [inX0, startsWithX] at h
      | xCons m rest =>
        cases hwp.1 with
        | inl h => cases h
        | inr h => simp [inY0, startsWithY] at h
      | yCons m rest =>
        exact eq258X_xCons_yCons_from_driverIH k i j m rest s hwq.1 hIH
  | yCons i r =>
    cases hp with
    | inl h => cases h
    | inr h => simp [inX0, startsWithX] at h

/-- Complete y-direction dispatcher for the H-O well-formed side conditions
    `p ∈ Y`, `q ∈ X`, symmetric to
    `eq258X_of_driverIH_of_inX_inY`. -/
theorem eq258Y_of_driverIH_of_inY_inX (l : ℕ) (p q : FreeAssocMono)
    (hp : p.inY) (hq : q.inX) (hwp : p.WF) (hwq : q.WF)
    (hIH : Eq258DriverIH (p.weight + q.weight)) :
    Eq258Y l p q := by
  cases p with
  | one =>
    cases q with
    | one =>
      exact eq258Y_one_one l
    | xCons i s =>
      cases s with
      | one =>
        exact eq258Y_one_xCons_one l i
      | xCons m rest =>
        cases hwq.1 with
        | inl h => cases h
        | inr h => simp [inY0, startsWithY] at h
      | yCons m rest =>
        exact eq258Y_one_xCons_yCons_exact l i m rest
    | yCons j s =>
      cases hq with
      | inl h => cases h
      | inr h => simp [inX0, startsWithX] at h
  | xCons i r =>
    cases hp with
    | inl h => cases h
    | inr h => simp [inY0, startsWithY] at h
  | yCons j r =>
    cases q with
    | one =>
      cases r with
      | one =>
        exact eq258Y_yCons_one_one l j
      | xCons m rest =>
        exact eq258Y_yCons_xCons_one_from_driverIH l j m rest hwp.2.1 hIH
      | yCons m rest =>
        cases hwp.1 with
        | inl h => cases h
        | inr h => simp [inX0, startsWithX] at h
    | xCons i s =>
      cases r with
      | one =>
        cases s with
        | one =>
          exact eq258Y_yCons_one_xCons_one l j i
        | xCons m rest =>
          cases hwq.1 with
          | inl h => cases h
          | inr h => simp [inY0, startsWithY] at h
        | yCons n rest =>
          exact eq258Y_yCons_one_xCons_yCons_from_driverIH l j i n rest hIH
      | xCons m rest =>
        exact eq258Y_yCons_xCons_from_driverIH l j i m rest s hwq.1 hIH
      | yCons m rest =>
        cases hwp.1 with
        | inl h => cases h
        | inr h => simp [inX0, startsWithX] at h
    | yCons i s =>
      cases hq with
      | inl h => cases h
      | inr h => simp [inX0, startsWithX] at h
