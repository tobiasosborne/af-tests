/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Macdonald.MOperator

/-!
# Properties of M_{p,q} Operators (H-O 2.4.24)

Properties (iii) and (iv) of the M_{p,q} multiplication operators:
- (iii) Same-letter U property: M(x^k·p, x^k·q) = U_{x^{k+1}} ∘ M(p,q)
- (iv) Different-letter U_bilinear property

## References

* Hanche-Olsen & Størmer, "Jordan Operator Algebras", §2.4.24, (2.53)-(2.55)
-/

open FreeJordanAlg FreeAssocMono

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
        - M_op (yCons l (yCons m p')) (xCons k q) v := by
  rw [M_op.eq_def]

/-- Symmetric recurrence (2.55b): M(yCons l (xCons n q'), xCons k p) unfolds to
    2·U_{y^{l+1},x^{k+1}}(M(xCons n q', p)) - M(xCons k (xCons n q'), yCons l p). -/
theorem M_op_yCons_xCons_xCons (l n : ℕ) (q' : FreeAssocMono)
    (k : ℕ) (p : FreeAssocMono) (v : FreeJordanAlg) :
    M_op (yCons l (xCons n q')) (xCons k p) v =
      (2 : ℝ) • U_bilinear (pow y (l + 1)) (pow x (k + 1))
          (M_op (xCons n q') p v)
        - M_op (xCons k (xCons n q')) (yCons l p) v := by
  rw [M_op.eq_def]

/-- Property (iv), yCons case: U_{x^{k+1},y^{l+1}}(M(yCons m p', q) v) =
    ½(M(xCons k (yCons m p'), yCons l q) + M(yCons l (yCons m p'), xCons k q)).
    Derived by rearranging the different-letter recurrence (2.55). -/
theorem M_op_U_bilinear_yCons (k l m : ℕ) (p' : FreeAssocMono)
    (q : FreeAssocMono) (v : FreeJordanAlg) :
    U_bilinear (pow x (k + 1)) (pow y (l + 1))
        (M_op (yCons m p') q v) =
      (1 / 2 : ℝ) • (M_op (xCons k (yCons m p')) (yCons l q) v
        + M_op (yCons l (yCons m p')) (xCons k q) v) := by
  have h := M_op_xCons_yCons_yCons k m p' l q v
  -- h : M(x·p, y·q) = 2 • U_bi(...) - M(y·p, x·q)
  -- So: 2 • U_bi(...) = M(x·p, y·q) + M(y·p, x·q)
  -- And: U_bi(...) = (1/2) • (M(x·p, y·q) + M(y·p, x·q))
  -- h : M(x·p, y·q) = 2 • U_bi - M(y·p, x·q)
  -- Goal: U_bi = (1/2) • (M(x·p, y·q) + M(y·p, x·q))
  -- From h: 2 • U_bi = M(x·p, y·q) + M(y·p, x·q)
  -- So: U_bi = (1/2) • (M(x·p, y·q) + M(y·p, x·q))
  have key : (2 : ℝ) • U_bilinear (pow x (k + 1)) (pow y (l + 1))
      (M_op (yCons m p') q v) =
    M_op (xCons k (yCons m p')) (yCons l q) v
      + M_op (yCons l (yCons m p')) (xCons k q) v := by
    rw [h]; abel
  calc U_bilinear (pow x (k + 1)) (pow y (l + 1)) (M_op (yCons m p') q v)
      = (1 / 2 : ℝ) • ((2 : ℝ) • U_bilinear (pow x (k + 1)) (pow y (l + 1))
          (M_op (yCons m p') q v)) := by rw [smul_smul]; norm_num
    _ = (1 / 2 : ℝ) • (M_op (xCons k (yCons m p')) (yCons l q) v
        + M_op (yCons l (yCons m p')) (xCons k q) v) := by rw [key]

/-- Property (iv), xCons case: U_{y^{l+1},x^{k+1}}(M(xCons n q', p) v) =
    ½(M(yCons l (xCons n q'), xCons k p) + M(xCons k (xCons n q'), yCons l p)).
    Symmetric version of `M_op_U_bilinear_yCons`. -/
theorem M_op_U_bilinear_xCons (k l n : ℕ) (q' : FreeAssocMono)
    (p : FreeAssocMono) (v : FreeJordanAlg) :
    U_bilinear (pow y (l + 1)) (pow x (k + 1))
        (M_op (xCons n q') p v) =
      (1 / 2 : ℝ) • (M_op (yCons l (xCons n q')) (xCons k p) v
        + M_op (xCons k (xCons n q')) (yCons l p) v) := by
  have h := M_op_yCons_xCons_xCons l n q' k p v
  have key : (2 : ℝ) • U_bilinear (pow y (l + 1)) (pow x (k + 1))
      (M_op (xCons n q') p v) =
    M_op (yCons l (xCons n q')) (xCons k p) v
      + M_op (xCons k (xCons n q')) (yCons l p) v := by
    rw [h]; abel
  calc U_bilinear (pow y (l + 1)) (pow x (k + 1)) (M_op (xCons n q') p v)
      = (1 / 2 : ℝ) • ((2 : ℝ) • U_bilinear (pow y (l + 1)) (pow x (k + 1))
          (M_op (xCons n q') p v)) := by rw [smul_smul]; norm_num
    _ = (1 / 2 : ℝ) • (M_op (yCons l (xCons n q')) (xCons k p) v
        + M_op (xCons k (xCons n q')) (yCons l p) v) := by rw [key]
