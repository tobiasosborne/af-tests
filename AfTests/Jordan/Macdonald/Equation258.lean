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
  -- Step 4: Proof via T∘U commutation + power_formula_245.
  -- Proven pieces (all compile individually via multi_attempt):
  --   hc: L commutation for powers of x (L_jpow_comm_all)
  --   hpow: mul(x^m)(x^m) = pow x (m+m) (jpow_add)
  --   hc2: L commutation for x^{2m} (L_jpow_comm_all)
  --   hTU: mul(x^l)(U(x^m)(w)) = U(x^m)(mul(x^l)(w)) (expand U, distribute, commute)
  --   h245w: mul(x^l)(U(x^m)(w)) = U_bi(x^m,x^{l+m})(w) (power_formula_245 + fold)
  --   hkey: U_bi(x^{i+1},x^{k+1})(w) = U(x^{i+1})(mul(x^{k-i})(w)) (h245w.symm.trans hTU)
  -- Endgame: simp [T_apply] at h247v, rw [hge, hkey] at h247v, expand U linearity, linarith
  -- Remaining fixes needed (see HANDOFF.md):
  --   (a) hpow: remove extra ← FJ_jpow_eq_pow (jpow=pow after ← FJ_jmul_eq_mul)
  --   (b) hTU: bare negation -X ≠ (-1)•X, need mul_neg_right helper or neg_one_smul
  --   (c) h245w: add FJ_U_eq to convert JordanAlgebra.U → FreeJordanAlg.U
  --   (d) endgame: qualify JordanAlgebra.U_add_right/U_smul_right, fix sub→add pattern
  sorry

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
    7. Expand RHS using (2.55a), cancel, close by algebra
    The algebra closure (steps 5-7) is left as sorry. -/
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
    (v : FreeJordanAlg) :
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
  -- Remaining steps:
  -- a) Use M_op_U_bilinear_yCons on U_bi terms to convert to M_op
  -- b) Use M_op_U_prependX on U terms (property iii)
  -- c) Expand RHS M_op terms using (2.55a) = M_op_xCons_yCons_yCons
  -- d) Cancel matching terms
  sorry

/-- (2.58) weight > 1, i < k case: T_{x^{k+1}} M_{x^{i+1}·(y^m·r'), y^{j+1}·s}.
    H-O lines 1369-1377. Proof structure:
    1. Expand LHS via (2.59) = M_op recurrence
    2. Distribute T over sub and smul
    3. Apply (2.47) to decompose T_{x^{k+1}} U_{x^{i+1},y^{j+1}}
    4. Apply induction (ih_swap) to the T_{x^{k+1}} M_{swapped} term
    5. Use (2.49) on the resulting T_{x^{i+1}} U_{x^{k+1},y^{j+1}} term
    6. Apply property (iii) and (iv), cancel, close by algebra
    The algebra closure (steps 5-6) is left as sorry. -/
theorem eq258_xCons_yCons_general_lt (k i j m : ℕ) (r' : FreeAssocMono)
    (s : FreeAssocMono) (hik : i < k)
    -- IH: eq258 for swapped term (same as ge case)
    (ih_swap : ∀ v, T (pow x (k + 1))
        (M_op (prependY j (yCons m r')) (xCons i s) v) =
      (1/2 : ℝ) • (M_op (prependX k (prependY j (yCons m r'))) (xCons i s) v
        + M_op (prependY j (yCons m r')) (xCons (k + 1 + i) s) v))
    (v : FreeJordanAlg) :
    T (pow x (k + 1)) (M_op (xCons i (yCons m r')) (yCons j s) v) =
    (1/2 : ℝ) • (M_op (xCons (k + 1 + i) (yCons m r')) (yCons j s) v +
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
  -- Remaining goal (H-O lines 1371-1377):
  -- Involves T(x^{i+1})(U_bi(x^{k+1},y^{j+1})(w)), U_bi(x^{i+1},x^{k+1})(T(y^{j+1})(w)),
  -- and various M_op terms from ih_swap expansion.
  --
  -- Remaining steps:
  -- a) Use h247v to express T(x^{k+1}) U_bi in terms of T(x^{i+1}), U_bi, etc.
  -- b) Apply (2.49) or Case 1 to T(x^{i+1}) U_bi(x^{k+1},y^{j+1})
  -- c) Use property (iii) on U_bi(x^{i+1},x^{k+1}) T terms
  -- d) Apply (iv) and induction to convert everything to M_op
  -- e) Cancel matching terms in the 6-line algebra (H-O lines 1373-1377)
  sorry
