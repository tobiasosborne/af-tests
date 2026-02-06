/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Macdonald.UBilinear
import AfTests.Jordan.LinearizedJordan

/-!
# Generator Lemma (H-O 2.4.23, Macdonald Step 9)

Expresses the bilinearized U operator in terms of L (multiplication) operators,
and provides the T-product formula (rearranged operator_formula).

## Main results

* `U_bilinear_eq_L` — `U_{a,b} = L_b ∘ L_a + L_a ∘ L_b - L_{a∘b}`
* `U_bilinear_one_right` — `U_{a,1} = L_a`
* `T_product_formula` — `L_{a∘(b∘c)} = L_a∘L_{b∘c} + L_b∘L_{c∘a} + L_c∘L_{a∘b} - L_b∘L_a∘L_c - L_c∘L_a∘L_b`

## References

* Hanche-Olsen & Størmer, "Jordan Operator Algebras" (1984), §2.4
-/

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-! ### U_{a,b} in terms of L operators -/

/-- U_{a,b} = L_b ∘ L_a + L_a ∘ L_b - L_{a∘b}.

Proof: triple a x b = (a∘x)∘b + a∘(x∘b) - x∘(a∘b)
  = b∘(a∘x) + a∘(b∘x) - (a∘b)∘x  [by jmul_comm]
  = (L_b∘L_a + L_a∘L_b - L_{a∘b})(x). -/
theorem U_bilinear_eq_L (a b : J) :
    U_bilinear_linear a b =
      (L b).comp (L a) + (L a).comp (L b) - L (jmul a b) := by
  ext x
  simp only [U_bilinear_linear_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.comp_apply, L_apply]
  -- triple a x b = jmul (jmul a x) b + jmul a (jmul x b) - jmul x (jmul a b)
  simp only [triple]
  -- Apply commutativity to match L composition form
  rw [jmul_comm (jmul a x) b, jmul_comm x b, jmul_comm x (jmul a b)]

/-- U_{a,1} = L_a: the bilinearized U with jone on the right is just multiplication. -/
theorem U_bilinear_one_right (a : J) :
    U_bilinear_linear a jone = L a := by
  ext x
  simp only [U_bilinear_linear_apply, L_apply, triple]
  -- jmul (jmul a x) jone + jmul a (jmul x jone) - jmul x (jmul a jone)
  rw [jmul_jone, jmul_jone, jmul_jone]
  -- jmul a x + jmul a x - jmul x a = jmul a x + jmul a x - jmul a x
  rw [jmul_comm x a]
  abel

/-- U_{1,b} = L_b: the bilinearized U with jone on the left is just multiplication. -/
theorem U_bilinear_one_left (b : J) :
    U_bilinear_linear jone b = L b := by
  rw [U_bilinear_comm, U_bilinear_one_right]

/-! ### T-product formula (rearranged operator_formula) -/

/-- The T-product formula: L_{a∘(b∘c)} expressed in terms of compositions of L operators.
This is a rearrangement of `operator_formula` (H-O 2.35):

  `L_{a∘(b∘c)} = L_a∘L_{b∘c} + L_b∘L_{c∘a} + L_c∘L_{a∘b} - L_b∘L_a∘L_c - L_c∘L_a∘L_b`

This shows that every T_p for a product p = a∘(b∘c) can be expressed as
a polynomial in T operators of the factors. -/
theorem T_product_formula (a b c : J) :
    L (jmul a (jmul b c)) =
      L a ∘ₗ L (jmul b c) + L b ∘ₗ L (jmul c a) + L c ∘ₗ L (jmul a b)
      - L b ∘ₗ L a ∘ₗ L c - L c ∘ₗ L a ∘ₗ L b := by
  have h := operator_formula a b c
  -- h : L a ∘ₗ L (jmul b c) + L b ∘ₗ L (jmul c a) + L c ∘ₗ L (jmul a b) =
  --      L (jmul a (jmul b c)) + L b ∘ₗ L a ∘ₗ L c + L c ∘ₗ L a ∘ₗ L b
  -- Rearrange: L_{a∘(b∘c)} = LHS - L_b∘L_a∘L_c - L_c∘L_a∘L_b
  -- h : LHS = L_p + B + C, so L_p = LHS - B - C
  ext x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, L_apply,
    LinearMap.sub_apply]
  have hx := congrFun (congrArg DFunLike.coe h) x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, L_apply] at hx
  -- hx : a(bc·x) + b(ca·x) + c(ab·x) = (a(bc))x + b(a(cx)) + c(a(bx))
  -- goal: (a(bc))x = a(bc·x) + b(ca·x) + c(ab·x) - b(a(cx)) - c(a(bx))
  have : jmul (jmul a (jmul b c)) x =
    jmul a (jmul (jmul b c) x) + jmul b (jmul (jmul c a) x) + jmul c (jmul (jmul a b) x)
    - jmul b (jmul a (jmul c x)) - jmul c (jmul a (jmul b x)) := by
    have h' : jmul (jmul a (jmul b c)) x + jmul b (jmul a (jmul c x)) + jmul c (jmul a (jmul b x)) =
      jmul a (jmul (jmul b c) x) + jmul b (jmul (jmul c a) x) + jmul c (jmul (jmul a b) x) := by
      rw [← hx]
    calc jmul (jmul a (jmul b c)) x
        = jmul (jmul a (jmul b c)) x + jmul b (jmul a (jmul c x)) + jmul c (jmul a (jmul b x))
          - jmul b (jmul a (jmul c x)) - jmul c (jmul a (jmul b x)) := by abel
      _ = jmul a (jmul (jmul b c) x) + jmul b (jmul (jmul c a) x) + jmul c (jmul (jmul a b) x)
          - jmul b (jmul a (jmul c x)) - jmul c (jmul a (jmul b x)) := by rw [h']
  exact this

end JordanAlgebra
