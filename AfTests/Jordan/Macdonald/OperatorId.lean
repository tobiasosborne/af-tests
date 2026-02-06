/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.FundamentalFormula
import AfTests.Jordan.Macdonald.UBilinear

/-!
# Operator Identities (2.50) and (2.51)

From Hanche-Olsen & Størmer §2.4:

* (2.50): `U_{x∘z,y} = U_{x,y} ∘ L_z + U_{z,y} ∘ L_x - L_y ∘ U_{x,z}`
* (2.51): `U_{x∘z,y} = L_z ∘ U_{x,y} + L_x ∘ U_{z,y} - U_{x,z} ∘ L_y`

Both are derived from the triple product identities (2.43) and (2.44).
-/

namespace JordanAlgebra
variable {J : Type*} [JordanAlgebra J]

/-- H-O (2.50): `U_{x∘z,y} = U_{x,y} ∘ L_z + U_{z,y} ∘ L_x - L_y ∘ U_{x,z}`.
Follows from triple_product_243 (identity 2.43). -/
theorem U_bilinear_product_250 (x y z : J) :
    U_bilinear_linear (jmul x z) y =
      (U_bilinear_linear x y).comp (L z) +
      (U_bilinear_linear z y).comp (L x) -
      (L y).comp (U_bilinear_linear x z) := by
  ext v
  simp only [U_bilinear_linear_apply, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.sub_apply, L_apply]
  have h := triple_product_243 x v z y
  rw [jmul_comm v z, jmul_comm (triple x v z) y] at h
  -- h : A = B - G + C, goal : G = B + C - A  (where A,B,C,G are the terms)
  rw [show triple (jmul x z) v y =
    triple x (jmul z v) y + triple z (jmul x v) y -
    jmul y (triple x v z) from by rw [h]; abel]

/-- H-O (2.51): `U_{x∘z,y} = L_z ∘ U_{x,y} + L_x ∘ U_{z,y} - U_{x,z} ∘ L_y`.
Follows from triple_product_244 (identity 2.44). -/
theorem U_bilinear_product_251 (x y z : J) :
    U_bilinear_linear (jmul x z) y =
      (L z).comp (U_bilinear_linear x y) +
      (L x).comp (U_bilinear_linear z y) -
      (U_bilinear_linear x z).comp (L y) := by
  ext v
  simp only [U_bilinear_linear_apply, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.sub_apply, L_apply]
  have h := triple_product_244 x v y z
  rw [jmul_comm (triple x v y) z, jmul_comm (triple z v y) x,
      jmul_comm v y] at h
  -- h : L + R = T + G, goal : G = L + R - T
  have key : triple (jmul x z) v y =
    jmul z (triple x v y) + jmul x (triple z v y) -
    triple x (jmul y v) z := by
    have h' := sub_eq_zero.mpr h
    -- h' : (L + R) - (T + G) = 0, so G = L + R - T
    apply eq_of_sub_eq_zero
    calc triple (jmul x z) v y -
        (jmul z (triple x v y) + jmul x (triple z v y) -
         triple x (jmul y v) z)
        = -(jmul z (triple x v y) + jmul x (triple z v y) -
           (triple x (jmul y v) z + triple (jmul x z) v y)) := by
          abel
      _ = 0 := by rw [h']; simp
  rw [key]

/-- H-O (2.47): `T_{aⁿ} U_{aᵐ,b} + T_{aᵐ} U_{aⁿ,b} = U_{aᵐ,aⁿ} T_b + U_{a^{m+n},b}`.
Immediate from `triple_product_244` with a^m, v, b, a^n. -/
theorem operator_identity_247 (a b : J) (m n : ℕ) :
    (L (jpow a n)).comp (U_bilinear_linear (jpow a m) b) +
    (L (jpow a m)).comp (U_bilinear_linear (jpow a n) b) =
    (U_bilinear_linear (jpow a m) (jpow a n)).comp (L b) +
    U_bilinear_linear (jpow a (m + n)) b := by
  ext v
  simp only [LinearMap.comp_apply, LinearMap.add_apply,
    U_bilinear_linear_apply, L_apply]
  have h := triple_product_244 (jpow a m) v b (jpow a n)
  rw [jmul_comm (triple (jpow a m) v b) (jpow a n),
      jmul_comm (triple (jpow a n) v b) (jpow a m),
      jmul_comm v b, jpow_add] at h
  exact h

end JordanAlgebra
