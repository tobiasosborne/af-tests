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

/-- Auxiliary: L_{a^l} commutes with L_{a^m} at element level. -/
private theorem jpow_jmul_comm' (a : J) (l m : ℕ) (x : J) :
    jmul (jpow a l) (jmul (jpow a m) x) = jmul (jpow a m) (jmul (jpow a l) x) := by
  have h := L_jpow_comm_all a l m
  exact congrFun (congrArg DFunLike.coe h.eq) x

/-- H-O (2.48): `2 U_{a^{m+k},b} ∘ T_{a^m} = U_{a^k,b} ∘ U_{a^m} + U_{a^{2m+k},b}`.
Uses (2.50) three times and power-associativity. -/
theorem operator_identity_248 (a b : J) (m k : ℕ) :
    (2 : ℝ) • ((U_bilinear_linear (jpow a (m + k)) b).comp (L (jpow a m))) =
    (U_bilinear_linear (jpow a k) b).comp (U_linear (jpow a m)) +
    U_bilinear_linear (jpow a (m + (m + k))) b := by
  -- Abbreviations for readability
  set am := jpow a m; set ak := jpow a k
  -- (I) U_{a^{m+k},b} = U_{a^m,b}∘L_{a^k} + U_{a^k,b}∘L_{a^m} - L_b∘U_{a^m,a^k}
  have h1 := U_bilinear_product_250 am b ak
  rw [show jmul am ak = jpow a (m + k) from jpow_add a m k] at h1
  -- (II) U_{a^{2m},b} = 2·U_{a^m,b}∘L_{a^m} - L_b∘U_{a^m}
  have h2 := U_bilinear_product_250 am b am
  rw [show jmul am am = jpow a (m + m) from jpow_add a m m, U_bilinear_self] at h2
  -- (III) U_{a^{2m},a^k} = 2·U_{a^m,a^k}∘L_{a^m} - L_{a^k}∘U_{a^m}
  have h3 := U_bilinear_product_250 am (ak) am
  rw [show jmul am am = jpow a (m + m) from jpow_add a m m, U_bilinear_self] at h3
  -- (IV) U_{a^{2m+k},b} = U_{a^{2m},b}∘L_{a^k} + U_{a^k,b}∘L_{a^{2m}} - L_b∘U_{a^{2m},a^k}
  have h4 := U_bilinear_product_250 (jpow a (m + m)) b ak
  rw [show jmul (jpow a (m + m)) ak = jpow a (m + (m + k)) from by
    rw [jpow_add]; ring_nf] at h4
  -- Substitute h1 into LHS
  rw [h1]
  simp only [LinearMap.add_comp, LinearMap.sub_comp]
  -- Need: 2•(U_{m,b}∘L_k∘L_m + U_{k,b}∘L_m∘L_m - L_b∘U_{m,k}∘L_m)
  --     = U_{k,b}∘U_m + U_{2m,b}∘L_k + U_{k,b}∘L_{2m} - L_b∘U_{2m,k}
  -- Substitute h2 and h3 into RHS (via h4)
  rw [h4, h2, h3]
  -- Now everything is in base operators: U_{m,b}, U_{k,b}, U_{m,k}, L_m, L_k, L_b, U_m
  -- Use L_m∘L_k = L_k∘L_m
  have hLc : (L am).comp (L ak) = (L ak).comp (L am) :=
    (L_jpow_comm_all a m k).eq
  -- Use U_m∘L_k = L_k∘U_m (U_{a^m} = 2L_m² - L_{2m}, all commute with L_k)
  -- Reduce to element level
  ext v
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.sub_apply, U_bilinear_linear_apply, U_linear_apply,
    L_apply, U_def, jsq_def, triple_def]
  -- Fold jmul am am = jpow a (m+m)
  rw [show jmul am am = jpow a (m + m) from jpow_add a m m]
  -- Commutativity: jmul(a^m, jmul(a^k, w)) = jmul(a^k, jmul(a^m, w))
  have hc : ∀ w : J, jmul am (jmul ak w) = jmul ak (jmul am w) :=
    jpow_jmul_comm' a m k
  -- jmul(a^{2m}, jmul(a^k, w)) = jmul(a^k, jmul(a^{2m}, w))
  have hc2 : ∀ w : J, jmul (jpow a (m + m)) (jmul ak w) =
      jmul ak (jmul (jpow a (m + m)) w) := jpow_jmul_comm' a (m + m) k
  -- Distribute jmul over sub/add and nsmul
  simp only [jmul_sub, sub_jmul, jmul_add, add_jmul,
    smul_sub, smul_add, two_smul, hc, hc2]
  abel

/-- H-O (2.49): `2 T_{a^m} ∘ U_{a^{m+k},b} = U_{a^m} ∘ U_{a^k,b} + U_{a^{2m+k},b}`.
Uses (2.51) three times and power-associativity. -/
theorem operator_identity_249 (a b : J) (m k : ℕ) :
    (2 : ℝ) • ((L (jpow a m)).comp (U_bilinear_linear (jpow a (m + k)) b)) =
    (U_linear (jpow a m)).comp (U_bilinear_linear (jpow a k) b) +
    U_bilinear_linear (jpow a (m + (m + k))) b := by
  set am := jpow a m; set ak := jpow a k
  -- (I) U_{a^{m+k},b} via (2.51)
  have h1 := U_bilinear_product_251 am b ak
  rw [show jmul am ak = jpow a (m + k) from jpow_add a m k] at h1
  -- (II) U_{a^{2m},b} via (2.51)
  have h2 := U_bilinear_product_251 am b am
  rw [show jmul am am = jpow a (m + m) from jpow_add a m m, U_bilinear_self] at h2
  -- (III) U_{a^{2m},a^k} via (2.51)
  have h3 := U_bilinear_product_251 am ak am
  rw [show jmul am am = jpow a (m + m) from jpow_add a m m, U_bilinear_self] at h3
  -- (IV) U_{a^{2m+k},b} via (2.51)
  have h4 := U_bilinear_product_251 (jpow a (m + m)) b ak
  rw [show jmul (jpow a (m + m)) ak = jpow a (m + (m + k)) from by
    rw [jpow_add]; ring_nf] at h4
  -- Substitute h1
  rw [h1]
  simp only [LinearMap.comp_add, LinearMap.comp_sub]
  -- Substitute h4
  rw [h4, h2, h3]
  -- Element level
  ext v
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.sub_apply, U_bilinear_linear_apply, U_linear_apply,
    L_apply, U_def, jsq_def, triple_def]
  rw [show jmul am am = jpow a (m + m) from jpow_add a m m]
  have hc : ∀ w : J, jmul am (jmul ak w) = jmul ak (jmul am w) :=
    jpow_jmul_comm' a m k
  have hc2 : ∀ w : J, jmul (jpow a (m + m)) (jmul ak w) =
      jmul ak (jmul (jpow a (m + m)) w) := jpow_jmul_comm' a (m + m) k
  simp only [jmul_sub, jmul_add,
    smul_sub, smul_add, two_smul, hc, hc2]
  abel

end JordanAlgebra
