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

/-- Y-direction companion to H-O (2.58), obtained by swapping `x` and `y`.
    The side conditions `p ∈ Y`, `q ∈ X` are tracked by the callers. -/
def Eq258Y (j : ℕ) (p q : FreeAssocMono) : Prop :=
  ∀ v : FreeJordanAlg,
    T (pow y (j + 1)) (M_op p q v) =
      (1 / 2 : ℝ) • (M_op (prependY j p) q v + M_op p (prependY j q) v)

/-- The y-generator obligation consumed by the x-direction inductive helpers
    when `p = yCons m r'` and `q = s`. For well-formed H-O applications,
    callers should supply this from `Eq258Y j (yCons m r') s` together with
    the side condition that `s` lies in `X`, so `prependY j s = yCons j s`. -/
def Eq258YBaseObligation (j m : ℕ) (r' s : FreeAssocMono) (v : FreeJordanAlg) :
    Prop :=
  mul (pow y (j + 1)) (M_op (yCons m r') s v) =
    (1 / 2 : ℝ) • (M_op (prependY j (yCons m r')) s v +
      M_op (yCons m r') (yCons j s) v)

/-- Convert the y-direction Eq(2.58) family into the concrete y-base obligation
    used by the x-direction helpers. The `s ∈ X` side condition prevents the
    right prepend from merging and turns `prependY j s` into `yCons j s`. -/
theorem eq258YBaseObligation_of_eq258Y {j m : ℕ} {r' s : FreeAssocMono}
    {v : FreeJordanAlg} (hs : s.inX) (h : Eq258Y j (yCons m r') s) :
    Eq258YBaseObligation j m r' s v := by
  simpa [Eq258YBaseObligation, T_apply, prependY_of_inX hs] using h v

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

/-- Weight > 1, `i < k`, with all family-shaped obligations supplied from
    `Eq258X`/`Eq258Y`. Only the left lower-pair fact remains explicit because
    its current helper shape uses the unnormalized product `xCons _ s`. -/
theorem eq258_xCons_yCons_general_lt_from_family_obligations (k i j m : ℕ)
    (r' s : FreeAssocMono) (hik : i < k) (hs : s.inX)
    (ih_swap : Eq258X k (prependY j (yCons m r')) (xCons i s))
    (ih_y : Eq258Y j (yCons m r') s)
    (v : FreeJordanAlg)
    (ih_lower_left :
      T (pow x (k - i)) (M_op (prependY j (yCons m r')) s v) =
        (1 / 2 : ℝ) •
          (M_op (prependY j (yCons m r')) (xCons (k - i - 1) s) v +
            M_op (xCons (k - i - 1) (prependY j (yCons m r'))) s v))
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
  exact eq258_xCons_yCons_general_lt_from_families k i j m r' s hik hs ih_swap ih_y v
    ⟨ih_lower_left, h_right⟩
