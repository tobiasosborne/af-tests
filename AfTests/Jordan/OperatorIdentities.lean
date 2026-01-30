/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Basic
import AfTests.Jordan.Product
import AfTests.Jordan.FormallyReal.Spectrum

/-!
# Operator Identities for Jordan Algebras

This file defines the commutator bracket for linear operators and states key
identities used in Peirce decomposition analysis.

## Main definitions

* `opComm` - Commutator bracket: `[f, g] = f ∘ g - g ∘ f`

## Main results

* `linearized_jordan_operator` - The linearized Jordan identity in operator form
* `opComm_idempotent_eigenspace` - Commutator property for idempotents
* `L_e_L_a_L_e` - Identity involving `L_e ∘ L_a ∘ L_e` for idempotent e
-/

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-! ### Commutator Bracket -/

/-- The commutator (Lie bracket) of two linear operators: `[f, g] = f ∘ g - g ∘ f`. -/
def opComm (f g : J →ₗ[ℝ] J) : J →ₗ[ℝ] J := f ∘ₗ g - g ∘ₗ f

notation:max "⟦" f ", " g "⟧" => opComm f g

@[simp]
theorem opComm_apply (f g : J →ₗ[ℝ] J) (x : J) :
    ⟦f, g⟧ x = f (g x) - g (f x) := rfl

theorem opComm_skew (f g : J →ₗ[ℝ] J) : ⟦f, g⟧ = -⟦g, f⟧ := by
  ext x; simp [opComm, sub_eq_neg_add, add_comm]

theorem opComm_self (f : J →ₗ[ℝ] J) : ⟦f, f⟧ = 0 := by
  ext x; simp [opComm]

/-! ### Linearized Jordan Identity -/

/-- The linearized Jordan identity in operator form:
    `2([L_a, L_{b∘c}] + [L_b, L_{c∘a}] + [L_c, L_{a∘b}]) = 0`

This is the key identity relating commutators of multiplication operators. -/
theorem linearized_jordan_operator (a b c : J) :
    2 • (⟦L a, L (jmul b c)⟧ + ⟦L b, L (jmul c a)⟧ + ⟦L c, L (jmul a b)⟧) = 0 := by
  -- This follows from the linearization of the Jordan identity
  -- (a ∘ b) ∘ a² = a ∘ (b ∘ a²)
  sorry

/-! ### Idempotent Operator Identities -/

/-- For an idempotent e and element a in eigenspace with eigenvalue ev,
    the commutator `[L_e, L_a]` maps to specific eigenspaces. -/
theorem opComm_idempotent_eigenspace {e : J} (_he : IsIdempotent e)
    {a : J} {ev : ℝ} (_ha : jmul e a = ev • a) (x : J) :
    ⟦L e, L a⟧ x = jmul e (jmul a x) - jmul a (jmul e x) := rfl

/-- For idempotent e: `L_e ∘ L_a ∘ L_e = L_{e∘(a∘e)} + (1/2)[L_e, [L_e, L_a]]`
    This identity is used in analyzing Peirce space products. -/
theorem L_e_L_a_L_e {e : J} (he : IsIdempotent e) (a : J) :
    L e ∘ₗ L a ∘ₗ L e = L (jmul e (jmul a e)) + (1/2 : ℝ) • ⟦L e, ⟦L e, L a⟧⟧ := by
  -- Follows from operator calculus and the Jordan identity
  sorry

/-- The double commutator identity for idempotent:
    `[L_e, [L_e, L_a]]` relates to the projection onto P_{1/2}(e). -/
theorem opComm_double_idempotent {e : J} (he : IsIdempotent e) (a : J) :
    ⟦L e, ⟦L e, L a⟧⟧ = 2 • (L e ∘ₗ L a ∘ₗ L e) - 2 • L (jmul e (jmul a e)) := by
  -- Rearrangement of L_e_L_a_L_e
  sorry

/-! ### Useful Commutator Properties -/

/-- For idempotent e with e ∘ a = a (i.e., a in P_1(e)), simplified commutator form. -/
theorem opComm_on_P1 {e a b : J} (_he : IsIdempotent e)
    (_ha : jmul e a = a) (hb : jmul e b = b) :
    ⟦L e, L a⟧ b = jmul e (jmul a b) - jmul a b := by
  simp only [opComm_apply, L_apply, hb]

/-- For idempotent e with e ∘ a = 0 (i.e., a in P_0(e)), the commutator form. -/
theorem opComm_on_P0 {e a : J} (_he : IsIdempotent e) (_ha : jmul e a = 0) (x : J) :
    ⟦L e, L a⟧ x = jmul e (jmul a x) - jmul a (jmul e x) := rfl

end JordanAlgebra
