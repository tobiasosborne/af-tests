/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.SpinFactor.Def
import AfTests.Jordan.FormallyReal.Def

/-!
# Spin Factors are Formally Real

Spin factors V_n are formally real: if a sum of squares equals zero, each term is zero.

## Main results

* `SpinFactor.sq_eq_zero_imp_zero` - If x² = 0 then x = 0
* `SpinFactor.formallyReal` - Instance: SpinFactor n is formally real

## Implementation

We prove `FormallyRealJordan` directly by showing that spin factor squares have
non-negative scalar components (x.1² + ⟨x.2, x.2⟩). This avoids the sorry in
`FormallyRealJordan.of_sq_eq_zero` which requires spectral theory for abstract algebras.
-/

namespace SpinFactor

variable {n : ℕ}

/-! ### Auxiliary lemmas -/

/-- Sum of two non-negative reals is zero iff both are zero. -/
private theorem add_eq_zero_of_sq_add_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 0) : a = 0 ∧ b = 0 := by
  constructor
  · linarith
  · linarith

/-! ### Key lemmas -/

/-- Key lemma: If x² = 0 then x.1 = 0. -/
theorem sq_eq_zero_imp_scalar_zero {x : SpinFactor n} (h : sq x = 0) : x.1 = 0 := by
  -- From sq_scalar: (sq x).1 = x.1² + ⟨x.2, x.2⟩
  -- If sq x = 0 then (sq x).1 = 0
  have h1 : (sq x).1 = 0 := by simp only [h, Prod.fst_zero]
  rw [sq_scalar] at h1
  -- x.1² + ⟨x.2, x.2⟩ = 0, and both terms are ≥ 0
  have hsq : 0 ≤ x.1 ^ 2 := sq_nonneg x.1
  have hinner : 0 ≤ @inner ℝ _ _ x.2 x.2 := real_inner_self_nonneg
  have ⟨hx1, _⟩ := add_eq_zero_of_sq_add_nonneg hsq hinner h1
  exact sq_eq_zero_iff.mp hx1

/-- Key lemma: If x² = 0 then x.2 = 0. -/
theorem sq_eq_zero_imp_vector_zero {x : SpinFactor n} (h : sq x = 0) : x.2 = 0 := by
  -- From sq_scalar: x.1² + ‖x.2‖² = 0 implies ‖x.2‖ = 0
  have h1 : (sq x).1 = 0 := by simp only [h, Prod.fst_zero]
  rw [sq_scalar] at h1
  have hsq : 0 ≤ x.1 ^ 2 := sq_nonneg x.1
  have hinner : 0 ≤ @inner ℝ _ _ x.2 x.2 := real_inner_self_nonneg
  have ⟨_, hx2⟩ := add_eq_zero_of_sq_add_nonneg hsq hinner h1
  exact inner_self_eq_zero.mp hx2

/-- In a spin factor, x² = 0 implies x = 0. -/
theorem sq_eq_zero_imp_zero {x : SpinFactor n} (h : sq x = 0) : x = 0 := by
  have h1 : x.1 = 0 := sq_eq_zero_imp_scalar_zero h
  have h2 : x.2 = 0 := sq_eq_zero_imp_vector_zero h
  ext <;> simp [h1, h2]

/-! ### Connection to Jordan algebra -/

/-- SpinFactor.sq agrees with JordanAlgebra.jsq. -/
private theorem sq_eq_jsq (x : SpinFactor n) : sq x = JordanAlgebra.jsq x := by
  rfl

/-! ### Direct FormallyRealJordan instance -/

/-- The scalar part of a Jordan square. -/
theorem jsq_scalar (x : SpinFactor n) :
    (JordanAlgebra.jsq x).1 = x.1 ^ 2 + @inner ℝ _ _ x.2 x.2 :=
  sq_scalar x

/-- Scalar part of sum of Jordan squares. -/
theorem sum_jsq_scalar {m : ℕ} (a : Fin m → SpinFactor n) :
    (∑ i, JordanAlgebra.jsq (a i)).1 = ∑ i, ((a i).1 ^ 2 + @inner ℝ _ _ (a i).2 (a i).2) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Prod.fst_add, jsq_scalar, ih]

/-- Each scalar part of a Jordan square is non-negative. -/
theorem jsq_scalar_nonneg (x : SpinFactor n) :
    0 ≤ (JordanAlgebra.jsq x).1 := by
  rw [jsq_scalar]
  apply add_nonneg (sq_nonneg _) real_inner_self_nonneg

/-- If sum of squares is zero, each scalar term is zero. -/
theorem sum_jsq_eq_zero_imp_scalar_zero {m : ℕ} (a : Fin m → SpinFactor n)
    (hsum : ∑ i, JordanAlgebra.jsq (a i) = 0) (i : Fin m) :
    (a i).1 ^ 2 + @inner ℝ _ _ (a i).2 (a i).2 = 0 := by
  have hscalar : (∑ i, JordanAlgebra.jsq (a i)).1 = 0 := by simp [hsum]
  rw [sum_jsq_scalar] at hscalar
  have h_nonneg : ∀ j ∈ Finset.univ, 0 ≤ (a j).1 ^ 2 + @inner ℝ _ _ (a j).2 (a j).2 :=
    fun j _ => add_nonneg (sq_nonneg _) real_inner_self_nonneg
  exact Finset.sum_eq_zero_iff_of_nonneg h_nonneg |>.mp hscalar i (Finset.mem_univ i)

/-- If scalar term is zero, both components are zero. -/
theorem scalar_term_zero_imp_zero (x : SpinFactor n)
    (h : x.1 ^ 2 + @inner ℝ _ _ x.2 x.2 = 0) : x = 0 := by
  have hsq : 0 ≤ x.1 ^ 2 := sq_nonneg x.1
  have hinner : 0 ≤ @inner ℝ _ _ x.2 x.2 := real_inner_self_nonneg
  have hx1 : x.1 ^ 2 = 0 := by linarith
  have hx2 : @inner ℝ _ _ x.2 x.2 = 0 := by linarith
  have h1 : x.1 = 0 := sq_eq_zero_iff.mp hx1
  have h2 : x.2 = 0 := inner_self_eq_zero.mp hx2
  ext <;> simp [h1, h2]

/-- Spin factors are formally real Jordan algebras (direct proof). -/
noncomputable instance formallyReal : FormallyRealJordan (SpinFactor n) where
  sum_sq_eq_zero m a hsum i := by
    have h := sum_jsq_eq_zero_imp_scalar_zero a hsum i
    exact scalar_term_zero_imp_zero (a i) h

end SpinFactor
