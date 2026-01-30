/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Basic
import AfTests.Jordan.Product

/-!
# Quadratic U Operator for Jordan Algebras

This file defines the quadratic U operator, which is fundamental to the theory of
Jordan algebras and gives rise to the fundamental formula.

## Main definitions

* `JordanAlgebra.U` - The quadratic U operator: `U_a(x) = 2(a ∘ (a ∘ x)) - a² ∘ x`

## Main results

* `JordanAlgebra.U_one` - `U_1(x) = x`
* `JordanAlgebra.U_zero_left` - `U_0(x) = 0`
* `JordanAlgebra.U_zero_right` - `U_a(0) = 0`
* `JordanAlgebra.U_smul` - `U_{c•a}(x) = c² • U_a(x)`

## References

* Jacobson, N. "Structure and Representations of Jordan Algebras"
* McCrimmon, K. "A Taste of Jordan Algebras"
-/

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-! ### The Quadratic U Operator -/

/-- The quadratic U operator: `U_a(x) = 2(a ∘ (a ∘ x)) - a² ∘ x`.
This is the fundamental operator in Jordan algebra theory. -/
def U (a x : J) : J := 2 • jmul a (jmul a x) - jmul (jsq a) x

theorem U_def (a x : J) : U a x = 2 • jmul a (jmul a x) - jmul (jsq a) x := rfl

/-! ### Basic Properties -/

/-- U_1(x) = x: the identity is the identity for U. -/
theorem U_one (x : J) : U jone x = x := by
  simp only [U_def, jone_jmul, jsq_def]
  rw [two_smul, add_sub_cancel_right]

/-- U_0(x) = 0: zero annihilates on the left. -/
theorem U_zero_left (x : J) : U 0 x = 0 := by
  simp only [U_def, zero_jmul, smul_zero, jsq_def, sub_self]

/-- U_a(0) = 0: zero annihilates on the right. -/
theorem U_zero_right (a : J) : U a 0 = 0 := by
  simp only [U_def, jmul_zero, smul_zero, sub_self]

/-- U_{c•a}(x) = c² • U_a(x): quadratic scaling in the first argument. -/
theorem U_smul (c : ℝ) (a x : J) : U (c • a) x = c ^ 2 • U a x := by
  simp only [U_def, jmul_smul, smul_jmul, jsq_def, smul_sub]
  -- The goal involves reordering scalar multiplications
  -- 2 • c • c • ... = c² • 2 • ... and c • c • ... = c² • ...
  congr 1
  · -- 2 • c • c • jmul a (jmul a x) = c ^ 2 • 2 • jmul a (jmul a x)
    calc 2 • c • c • jmul a (jmul a x)
        = 2 • (c • c • jmul a (jmul a x)) := by rfl
      _ = 2 • ((c * c) • jmul a (jmul a x)) := by rw [smul_smul]
      _ = (c * c) • 2 • jmul a (jmul a x) := by rw [smul_comm]
      _ = c ^ 2 • 2 • jmul a (jmul a x) := by rw [sq]
  · -- c • c • jmul (jmul a a) x = c ^ 2 • jmul (jmul a a) x
    rw [smul_smul, sq]

/-! ### Linearity in the Second Argument -/

/-- U_a is additive in its second argument. -/
theorem U_add_right (a x y : J) : U a (x + y) = U a x + U a y := by
  simp only [U_def, jmul_add]
  rw [smul_add]
  abel

/-- U_a respects scalar multiplication in its second argument. -/
theorem U_smul_right (a : J) (c : ℝ) (x : J) : U a (c • x) = c • U a x := by
  simp only [U_def, smul_jmul]
  rw [smul_sub, smul_comm]

/-- U_a as a linear map in the second argument. -/
def U_linear (a : J) : J →ₗ[ℝ] J where
  toFun x := U a x
  map_add' := U_add_right a
  map_smul' c x := U_smul_right a c x

@[simp]
theorem U_linear_apply (a x : J) : U_linear a x = U a x := rfl

/-! ### Relationship with L operator -/

/-- U in terms of L operators: U_a = 2L_a² - L_{a²}. -/
theorem U_eq_L (a x : J) : U a x = 2 • L a (L a x) - L (jsq a) x := by
  simp only [U_def, L_apply]

end JordanAlgebra
