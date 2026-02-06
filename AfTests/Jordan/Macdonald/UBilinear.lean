/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Quadratic

/-!
# Bilinearized U Operator

Defines `U_bilinear a b x = {a, x, b}` (the triple product with x in the middle),
viewed as a linear map in x. When `a = b` this recovers the quadratic `U_linear a`.

## Main definitions

* `U_bilinear_linear a b : J →ₗ[ℝ] J` -- the bilinearized U operator as a linear map in x

## Main results

* `U_bilinear_self` -- `U_bilinear_linear a a = U_linear a`
* `U_bilinear_comm` -- `U_bilinear_linear a b = U_bilinear_linear b a`
* Linearity lemmas in a and b (add, smul, zero)
-/

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-! ### The bilinearized U operator -/

/-- `U_bilinear a b x = {a, x, b}`, the triple product linear in x.
This is the bilinearization of the quadratic U operator. -/
def U_bilinear_linear (a b : J) : J →ₗ[ℝ] J where
  toFun x := triple a x b
  map_add' x y := by
    simp only [triple]
    simp only [jmul_add, add_jmul]
    abel
  map_smul' r x := by
    simp only [triple, RingHom.id_apply]
    simp only [smul_jmul, jmul_smul]
    rw [smul_sub, smul_add]

@[simp]
theorem U_bilinear_linear_apply (a b x : J) :
    U_bilinear_linear a b x = triple a x b := rfl

/-! ### Self-application recovers U -/

@[simp]
theorem U_bilinear_self (a : J) : U_bilinear_linear a a = U_linear a := by
  ext x
  simp only [U_bilinear_linear_apply, U_linear_apply]
  exact triple_self_right a x

/-! ### Symmetry in outer arguments -/

@[simp]
theorem U_bilinear_comm (a b : J) :
    U_bilinear_linear a b = U_bilinear_linear b a := by
  ext x
  simp only [U_bilinear_linear_apply]
  exact triple_comm_outer a x b

/-! ### Linearity in the first argument -/

theorem U_bilinear_add_left (a₁ a₂ b : J) :
    U_bilinear_linear (a₁ + a₂) b =
      U_bilinear_linear a₁ b + U_bilinear_linear a₂ b := by
  ext x
  simp only [U_bilinear_linear_apply, LinearMap.add_apply, triple]
  simp only [add_jmul, jmul_add]
  abel

theorem U_bilinear_smul_left (r : ℝ) (a b : J) :
    U_bilinear_linear (r • a) b = r • U_bilinear_linear a b := by
  ext x
  simp only [U_bilinear_linear_apply, LinearMap.smul_apply, triple]
  simp only [jmul_smul, smul_jmul]
  rw [smul_sub, smul_add]

theorem U_bilinear_zero_left (b : J) :
    U_bilinear_linear 0 b = 0 := by
  ext x
  simp only [U_bilinear_linear_apply, LinearMap.zero_apply, triple]
  simp only [zero_jmul, jmul_zero]
  abel

/-! ### Linearity in the second argument -/

theorem U_bilinear_add_right (a b₁ b₂ : J) :
    U_bilinear_linear a (b₁ + b₂) =
      U_bilinear_linear a b₁ + U_bilinear_linear a b₂ := by
  ext x
  simp only [U_bilinear_linear_apply, LinearMap.add_apply, triple]
  simp only [jmul_add]
  abel

theorem U_bilinear_smul_right (r : ℝ) (a b : J) :
    U_bilinear_linear a (r • b) = r • U_bilinear_linear a b := by
  ext x
  simp only [U_bilinear_linear_apply, LinearMap.smul_apply, triple]
  simp only [smul_jmul]
  rw [smul_sub, smul_add]

theorem U_bilinear_zero_right (a : J) :
    U_bilinear_linear a 0 = 0 := by
  ext x
  simp only [U_bilinear_linear_apply, LinearMap.zero_apply, triple]
  simp only [jmul_zero]
  abel

end JordanAlgebra
