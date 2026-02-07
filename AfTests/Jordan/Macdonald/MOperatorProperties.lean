/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Macdonald.MOperator
import AfTests.Jordan.Macdonald.FJBridge

/-!
# Properties of M_{p,q} Operators (H-O 2.4.24)

Properties (iii) and (iv) of the M_{p,q} multiplication operators:
- (iii) Same-letter U property: M(x^k·p, x^k·q) = U_{x^{k+1}} ∘ M(p,q)
- (iv) Different-letter U_bilinear property

## References

* Hanche-Olsen & Størmer, "Jordan Operator Algebras", §2.4.24, (2.53)-(2.55)
-/

open FreeJordanAlg FreeAssocMono

/-! ### Property (ii): M_{1,1} = identity -/

/-- Property (ii): M(1,1) is the identity operator. -/
theorem M_op_one_one (v : FreeJordanAlg) : M_op .one .one v = v := by
  rw [M_op.eq_def]

/-! ### Property (iii): Same-letter U factorization -/

/-- Property (iii)x: M(x^k·p, x^k·q) v = U_{x^{k+1}}(M(p,q) v).
    When both arguments start with the same x-block of equal exponent,
    the M operator factors through the quadratic U operator. -/
theorem M_op_xCons_xCons (k : ℕ) (p q : FreeAssocMono) (v : FreeJordanAlg) :
    M_op (xCons k p) (xCons k q) v = U (pow x (k + 1)) (M_op p q v) := by
  rw [M_op.eq_def]
  simp only [ge_iff_le, le_refl, ↓reduceDIte, ↓reduceIte]

/-- Property (iii)y: M(y^l·p, y^l·q) v = U_{y^{l+1}}(M(p,q) v).
    Symmetric to `M_op_xCons_xCons` for the y generator. -/
theorem M_op_yCons_yCons (l : ℕ) (p q : FreeAssocMono) (v : FreeJordanAlg) :
    M_op (yCons l p) (yCons l q) v = U (pow y (l + 1)) (M_op p q v) := by
  rw [M_op.eq_def]
  simp only [ge_iff_le, le_refl, ↓reduceDIte, ↓reduceIte]

/-! ### Property (iv): Different-letter U_bilinear symmetrization

From the M_op definition (2.55):
  M(xCons k p, yCons l q) = 2·U_{x^{k+1},y^{l+1}}·M(p,q) - M(yCons l p, xCons k q)

Rearranging gives:
  U_{x^{k+1},y^{l+1}}(M(p,q) v) = ½(M(xCons k p, yCons l q) + M(yCons l p, xCons k q))

We prove the recurrence equation directly for each pattern match case,
then derive property (iv) as a corollary. -/

/-- Recurrence (2.55): M(xCons k (yCons m p'), yCons l q) unfolds to
    2·U_{x^{k+1},y^{l+1}}(M(yCons m p', q)) - M(yCons l (yCons m p'), xCons k q). -/
theorem M_op_xCons_yCons_yCons (k m : ℕ) (p' : FreeAssocMono)
    (l : ℕ) (q : FreeAssocMono) (v : FreeJordanAlg) :
    M_op (xCons k (yCons m p')) (yCons l q) v =
      (2 : ℝ) • U_bilinear (pow x (k + 1)) (pow y (l + 1))
          (M_op (yCons m p') q v)
        - M_op (prependY l (yCons m p')) (xCons k q) v := by
  rw [M_op.eq_def]

/-- Symmetric recurrence (2.55b): M(yCons l (xCons n q'), xCons k p) unfolds to
    2·U_{y^{l+1},x^{k+1}}(M(xCons n q', p)) - M(xCons k (xCons n q'), yCons l p). -/
theorem M_op_yCons_xCons_xCons (l n : ℕ) (q' : FreeAssocMono)
    (k : ℕ) (p : FreeAssocMono) (v : FreeJordanAlg) :
    M_op (yCons l (xCons n q')) (xCons k p) v =
      (2 : ℝ) • U_bilinear (pow y (l + 1)) (pow x (k + 1))
          (M_op (xCons n q') p v)
        - M_op (prependX k (xCons n q')) (yCons l p) v := by
  rw [M_op.eq_def]

/-- Property (iv), yCons case: U_{x^{k+1},y^{l+1}}(M(yCons m p', q) v) =
    ½(M(xCons k (yCons m p'), yCons l q) + M(prependY l (yCons m p'), xCons k q)).
    Derived by rearranging the different-letter recurrence (2.55). -/
theorem M_op_U_bilinear_yCons (k l m : ℕ) (p' : FreeAssocMono)
    (q : FreeAssocMono) (v : FreeJordanAlg) :
    U_bilinear (pow x (k + 1)) (pow y (l + 1))
        (M_op (yCons m p') q v) =
      (1 / 2 : ℝ) • (M_op (xCons k (yCons m p')) (yCons l q) v
        + M_op (prependY l (yCons m p')) (xCons k q) v) := by
  have h := M_op_xCons_yCons_yCons k m p' l q v
  have key : (2 : ℝ) • U_bilinear (pow x (k + 1)) (pow y (l + 1))
      (M_op (yCons m p') q v) =
    M_op (xCons k (yCons m p')) (yCons l q) v
      + M_op (prependY l (yCons m p')) (xCons k q) v := by
    rw [h]; abel
  calc U_bilinear (pow x (k + 1)) (pow y (l + 1)) (M_op (yCons m p') q v)
      = (1 / 2 : ℝ) • ((2 : ℝ) • U_bilinear (pow x (k + 1)) (pow y (l + 1))
          (M_op (yCons m p') q v)) := by rw [smul_smul]; norm_num
    _ = (1 / 2 : ℝ) • (M_op (xCons k (yCons m p')) (yCons l q) v
        + M_op (prependY l (yCons m p')) (xCons k q) v) := by rw [key]

/-- Property (iv), xCons case: U_{y^{l+1},x^{k+1}}(M(xCons n q', p) v) =
    ½(M(yCons l (xCons n q'), xCons k p) + M(prependX k (xCons n q'), yCons l p)).
    Symmetric version of `M_op_U_bilinear_yCons`. -/
theorem M_op_U_bilinear_xCons (k l n : ℕ) (q' : FreeAssocMono)
    (p : FreeAssocMono) (v : FreeJordanAlg) :
    U_bilinear (pow y (l + 1)) (pow x (k + 1))
        (M_op (xCons n q') p v) =
      (1 / 2 : ℝ) • (M_op (yCons l (xCons n q')) (xCons k p) v
        + M_op (prependX k (xCons n q')) (yCons l p) v) := by
  have h := M_op_yCons_xCons_xCons l n q' k p v
  have key : (2 : ℝ) • U_bilinear (pow y (l + 1)) (pow x (k + 1))
      (M_op (xCons n q') p v) =
    M_op (yCons l (xCons n q')) (xCons k p) v
      + M_op (prependX k (xCons n q')) (yCons l p) v := by
    rw [h]; abel
  calc U_bilinear (pow y (l + 1)) (pow x (k + 1)) (M_op (xCons n q') p v)
      = (1 / 2 : ℝ) • ((2 : ℝ) • U_bilinear (pow y (l + 1)) (pow x (k + 1))
          (M_op (xCons n q') p v)) := by rw [smul_smul]; norm_num
    _ = (1 / 2 : ℝ) • (M_op (yCons l (xCons n q')) (xCons k p) v
        + M_op (prependX k (xCons n q')) (yCons l p) v) := by rw [key]

/-! ### U-power composition -/

/-- U_{a^m}(U_{a^n}(w)) = U_{a^{m+n}}(w) for FreeJordanAlg.
    Follows from U_jpow (FundamentalFormula.lean). H-O line 1296. -/
theorem FJ_U_pow_comp (a : FreeJordanAlg) (m n : ℕ) (w : FreeJordanAlg) :
    U (pow a m) (U (pow a n) w) = U (pow a (m + n)) w := by
  rw [← FJ_U_eq, ← FJ_U_eq, ← FJ_U_eq,
      ← FJ_jpow_eq_pow, ← FJ_jpow_eq_pow, ← FJ_jpow_eq_pow]
  simp only [JordanAlgebra.U_jpow]
  rw [← pow_add]

/-! ### Property (iii) general: U_{x^k} ∘ M_{p,q} = M_{x^k·p, x^k·q}
    H-O lines 1290-1302. -/

/-- Property (iii), x version, general:
    U_{x^{k+1}} M_{p,q} = M_{prependX(k,p), prependX(k,q)}.
    Proof by cases on p,q: both-in-Y uses M_op_xCons_xCons,
    mixed uses M_op.eq_def arithmetic, both-in-X₀ uses FJ_U_pow_comp. -/
theorem M_op_U_prependX (k : ℕ) (p q : FreeAssocMono) (v : FreeJordanAlg) :
    U (pow x (k + 1)) (M_op p q v) = M_op (prependX k p) (prependX k q) v := by
  cases p with
  | one =>
    cases q with
    | one => simp only [prependX]; rw [M_op_xCons_xCons]
    | yCons j s => simp only [prependX]; rw [M_op_xCons_xCons]
    | xCons j s =>
      -- p ∈ Y, q ∈ X₀: prependX k one = xCons k one, prependX k (xCons j s) = xCons (k+1+j) s
      -- M_op(xCons k one, xCons(k+1+j) s): k < k+1+j, so factors U_{x^{k+1}}
      show U (pow x (k + 1)) (M_op one (xCons j s) v) =
        M_op (xCons k one) (xCons (k + 1 + j) s) v
      rw [M_op.eq_def (xCons k one) (xCons (k + 1 + j) s)]
      simp only [ge_iff_le]
      rw [dif_neg (by omega : ¬(k + 1 + j ≤ k))]
      simp only [show ¬(k + 1 + j = k) from by omega, ite_false]
      congr 2; omega
  | yCons i r =>
    cases q with
    | one => simp only [prependX]; rw [M_op_xCons_xCons]
    | yCons j s => simp only [prependX]; rw [M_op_xCons_xCons]
    | xCons j s =>
      show U (pow x (k + 1)) (M_op (yCons i r) (xCons j s) v) =
        M_op (xCons k (yCons i r)) (xCons (k + 1 + j) s) v
      rw [M_op.eq_def (xCons k (yCons i r)) (xCons (k + 1 + j) s)]
      simp only [ge_iff_le]
      rw [dif_neg (by omega : ¬(k + 1 + j ≤ k))]
      simp only [show ¬(k + 1 + j = k) from by omega, ite_false]
      congr 2; omega
  | xCons i r =>
    cases q with
    | one =>
      show U (pow x (k + 1)) (M_op (xCons i r) one v) =
        M_op (xCons (k + 1 + i) r) (xCons k one) v
      rw [M_op.eq_def (xCons (k + 1 + i) r) (xCons k one)]
      simp only [ge_iff_le]
      rw [dif_pos (by omega : k ≤ k + 1 + i)]
      simp only [(by omega : ¬(k + 1 + i = k)), ite_false]
      congr 2; omega
    | yCons j s =>
      show U (pow x (k + 1)) (M_op (xCons i r) (yCons j s) v) =
        M_op (xCons (k + 1 + i) r) (xCons k (yCons j s)) v
      rw [M_op.eq_def (xCons (k + 1 + i) r) (xCons k (yCons j s))]
      simp only [ge_iff_le]
      rw [dif_pos (by omega : k ≤ k + 1 + i)]
      simp only [(by omega : ¬(k + 1 + i = k)), ite_false]
      congr 2; omega
    | xCons j s =>
      -- Both in X₀: needs U-power composition (H-O line 1294-1296)
      show U (pow x (k + 1)) (M_op (xCons i r) (xCons j s) v) =
        M_op (xCons (k + 1 + i) r) (xCons (k + 1 + j) s) v
      -- Unfold both M_op calls
      rw [M_op.eq_def (xCons i r) (xCons j s)]
      rw [M_op.eq_def (xCons (k + 1 + i) r) (xCons (k + 1 + j) s)]
      simp only [ge_iff_le]
      by_cases h : j ≤ i
      · -- i ≥ j
        rw [dif_pos h, dif_pos (by omega : k + 1 + j ≤ k + 1 + i)]
        by_cases heq : i = j
        · subst heq
          simp only [ite_true, show k + 1 + i = k + 1 + i from rfl]
          exact FJ_U_pow_comp x (k + 1) (i + 1) (M_op r s v)
        · have : ¬(k + 1 + i = k + 1 + j) := by omega
          simp only [heq, this, ite_false]
          rw [show k + 1 + i - (k + 1 + j) - 1 = i - j - 1 from by omega]
          exact FJ_U_pow_comp x (k + 1) (j + 1) (M_op (xCons (i - j - 1) r) s v)
      · -- i < j
        rw [dif_neg h, dif_neg (by omega : ¬(k + 1 + i ≥ k + 1 + j))]
        by_cases heq : j = i
        · omega  -- contradiction with ¬(j ≤ i) and j = i
        · have : ¬(k + 1 + j = k + 1 + i) := by omega
          simp only [heq, this, ite_false]
          rw [show k + 1 + j - (k + 1 + i) - 1 = j - i - 1 from by omega]
          exact FJ_U_pow_comp x (k + 1) (i + 1) (M_op r (xCons (j - i - 1) s) v)

/-- Property (iii), y version, general:
    U_{y^{l+1}} M_{p,q} = M_{prependY(l,p), prependY(l,q)}.
    H-O lines 1290-1302, symmetric in x,y. -/
theorem M_op_U_prependY (l : ℕ) (p q : FreeAssocMono) (v : FreeJordanAlg) :
    U (pow y (l + 1)) (M_op p q v) = M_op (prependY l p) (prependY l q) v := by
  cases p with
  | one =>
    cases q with
    | one => rw [M_op_yCons_yCons]
    | xCons j s => rw [M_op_yCons_yCons]
    | yCons j s =>
      show U (pow y (l + 1)) (M_op one (yCons j s) v) =
        M_op (yCons l one) (yCons (l + 1 + j) s) v
      rw [M_op.eq_def (yCons l one) (yCons (l + 1 + j) s)]
      simp only [ge_iff_le]
      rw [dif_neg (by omega : ¬(l + 1 + j ≤ l))]
      simp only [(by omega : ¬(l + 1 + j = l)), ite_false]
      congr 2; omega
  | xCons i r =>
    cases q with
    | one => rw [M_op_yCons_yCons]
    | xCons j s => rw [M_op_yCons_yCons]
    | yCons j s =>
      show U (pow y (l + 1)) (M_op (xCons i r) (yCons j s) v) =
        M_op (yCons l (xCons i r)) (yCons (l + 1 + j) s) v
      rw [M_op.eq_def (yCons l (xCons i r)) (yCons (l + 1 + j) s)]
      simp only [ge_iff_le]
      rw [dif_neg (by omega : ¬(l + 1 + j ≤ l))]
      simp only [(by omega : ¬(l + 1 + j = l)), ite_false]
      congr 2; omega
  | yCons i r =>
    cases q with
    | one =>
      show U (pow y (l + 1)) (M_op (yCons i r) one v) =
        M_op (yCons (l + 1 + i) r) (yCons l one) v
      rw [M_op.eq_def (yCons (l + 1 + i) r) (yCons l one)]
      simp only [ge_iff_le]
      rw [dif_pos (by omega : l ≤ l + 1 + i)]
      simp only [(by omega : ¬(l + 1 + i = l)), ite_false]
      congr 2; omega
    | xCons j s =>
      show U (pow y (l + 1)) (M_op (yCons i r) (xCons j s) v) =
        M_op (yCons (l + 1 + i) r) (yCons l (xCons j s)) v
      rw [M_op.eq_def (yCons (l + 1 + i) r) (yCons l (xCons j s))]
      simp only [ge_iff_le]
      rw [dif_pos (by omega : l ≤ l + 1 + i)]
      simp only [(by omega : ¬(l + 1 + i = l)), ite_false]
      congr 2; omega
    | yCons j s =>
      show U (pow y (l + 1)) (M_op (yCons i r) (yCons j s) v) =
        M_op (yCons (l + 1 + i) r) (yCons (l + 1 + j) s) v
      rw [M_op.eq_def (yCons i r) (yCons j s)]
      rw [M_op.eq_def (yCons (l + 1 + i) r) (yCons (l + 1 + j) s)]
      simp only [ge_iff_le]
      by_cases h : j ≤ i
      · rw [dif_pos h, dif_pos (by omega : l + 1 + j ≤ l + 1 + i)]
        by_cases heq : i = j
        · subst heq
          simp only [ite_true, show l + 1 + i = l + 1 + i from rfl]
          exact FJ_U_pow_comp y (l + 1) (i + 1) (M_op r s v)
        · have : ¬(l + 1 + i = l + 1 + j) := by omega
          simp only [heq, this, ite_false]
          rw [show l + 1 + i - (l + 1 + j) - 1 = i - j - 1 from by omega]
          exact FJ_U_pow_comp y (l + 1) (j + 1) (M_op (yCons (i - j - 1) r) s v)
      · rw [dif_neg h, dif_neg (by omega : ¬(l + 1 + i ≥ l + 1 + j))]
        by_cases heq : j = i
        · omega
        · have : ¬(l + 1 + j = l + 1 + i) := by omega
          simp only [heq, this, ite_false]
          rw [show l + 1 + j - (l + 1 + i) - 1 = j - i - 1 from by omega]
          exact FJ_U_pow_comp y (l + 1) (i + 1) (M_op r (yCons (j - i - 1) s) v)
