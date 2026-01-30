/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.SpinFactor.Def
import AfTests.Jordan.FormallyReal.Def

/-!
# Spin Factors are Formally Real

Spin factors V_n are formally real: if x² = 0 then x = 0.

## Main results

* `SpinFactor.sq_eq_zero_iff` - Characterization of when x² = 0
* `SpinFactor.formallyReal` - Instance: SpinFactor n is formally real
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

/-- Spin factors are formally real Jordan algebras. -/
noncomputable instance formallyReal : FormallyRealJordan' (SpinFactor n) where
  sq_eq_zero_imp_zero := fun a h => by
    -- JordanAlgebra.jsq a = jordanMul a a = sq a
    have hsq : sq a = 0 := h
    exact sq_eq_zero_imp_zero hsq

end SpinFactor
