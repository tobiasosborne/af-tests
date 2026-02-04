/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Basic
import AfTests.Jordan.Product
import AfTests.Jordan.FormallyReal.Spectrum
import AfTests.Jordan.Peirce

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

/-! ### U Operator Properties -/

/-- U_a(a) = a ∘ (a ∘ a) = a ∘ a². -/
theorem U_self (a : J) : U a a = jmul a (jsq a) := by
  -- U a a = 2 • jmul a (jmul a a) - jmul (jsq a) a
  -- = 2 • jmul a (jsq a) - jmul (jsq a) a
  -- = 2 • jmul a (jsq a) - jmul a (jsq a)  [by commutativity]
  -- = jmul a (jsq a)
  rw [U_def, jsq_def]
  rw [jmul_comm (jmul a a) a]
  rw [two_smul]
  abel

/-- For idempotent e, U_e(e) = e. -/
theorem U_idempotent_self (e : J) (he : IsIdempotent e) : U e e = e := by
  rw [U_self]
  -- jsq e = e by idempotency, so jmul e (jsq e) = jmul e e = jsq e = e
  rw [he.jsq_eq_self]
  -- Now goal is jmul e e = e, which is jsq_def ▸ he
  rw [← jsq_def]
  exact he.jsq_eq_self

/-- U_e is idempotent as an operator when e is idempotent: U_e ∘ U_e = U_e. -/
theorem U_idempotent_comp (e : J) (he : IsIdempotent e) :
    U_linear e ∘ₗ U_linear e = U_linear e := by
  -- Key insight: For idempotent e, U_e = 2L_e² - L_e = peirceProj₁ e
  -- Since peirceProj₁ is a projection, it's idempotent.
  -- Step 1: Show U_linear e = peirceProj₁ e
  have hU_eq : U_linear e = peirceProj₁ e := by
    ext x
    simp only [U_linear_apply, U_def, peirceProj₁, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.comp_apply, L_apply]
    -- U_e(x) = 2(e∘(e∘x)) - e²∘x = 2L²(x) - L_e(x) since e² = e
    -- Note: U uses nsmul 2, peirceProj₁ uses (2:ℝ) • ...
    simp only [he.jsq_eq_self, ← Nat.cast_smul_eq_nsmul ℝ 2]
    norm_cast
  -- Step 2: Show peirceProj₁ e ∘ peirceProj₁ e = peirceProj₁ e
  -- This follows because peirceProj₁ maps to P₁(e) and is identity there.
  rw [hU_eq]
  ext x
  simp only [LinearMap.comp_apply]
  -- Let y = peirceProj₁ e x. Need: peirceProj₁ e y = y.
  set y := peirceProj₁ e x with hy_def
  -- y ∈ P₁(e), so L_e(y) = y
  have hy_in_P1 : y ∈ PeirceSpace e 1 := peirceProj₁_mem he x
  rw [mem_peirceSpace_one_iff] at hy_in_P1
  -- peirceProj₁ e y = (2L² - L)(y) = 2L(L(y)) - L(y) = 2L(y) - y = 2y - y = y
  simp only [peirceProj₁, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, L_apply]
  rw [hy_in_P1, hy_in_P1]
  -- 2 • y - y = y in a module
  rw [two_smul, add_sub_cancel_right]

/-- U commutes with L in a specific way: U_a(L_a(x)) = L_a(U_a(x)). -/
theorem U_L_comm (a x : J) : U a (L a x) = L a (U a x) := by
  simp only [L_apply, U_def]
  -- LHS: 2 • jmul a (jmul a (jmul a x)) - jmul (jsq a) (jmul a x)
  -- RHS: jmul a (2 • jmul a (jmul a x) - jmul (jsq a) x)
  -- Expand both sides using bilinearity
  rw [jmul_sub]
  -- RHS is now: jmul a (2 • jmul a (jmul a x)) - jmul a (jmul (jsq a) x)
  -- Expand 2 • ... as ... + ... for both sides
  simp only [two_smul, jmul_add]
  -- Now need to show the subtracted terms match
  simp only [jsq_def]
  -- Use Jordan identity: jmul (jmul a a) (jmul a x) = jmul a (jmul (jmul a a) x)
  have h1 : jmul (jmul a a) (jmul a x) = jmul a (jmul (jmul a a) x) := by
    -- (a²)∘(a∘x) = (a∘x)∘(a²) by commutativity
    rw [jmul_comm (jmul a a) (jmul a x)]
    -- = a∘(x∘(a²)) by Jordan identity
    rw [jordan_identity a x]
    -- = a∘((a²)∘x) by commutativity
    rw [jmul_comm x (jmul a a)]
  rw [h1]

/-! ### The Jordan Triple Product -/

/-- The Jordan triple product {a,b,c} = (a∘b)∘c + a∘(b∘c) - b∘(a∘c).
Satisfies {a,b,a} = U_a(b). Reference: Hanche-Olsen & Størmer, Definition 3.1.1. -/
def triple (a b c : J) : J :=
  jmul (jmul a b) c + jmul a (jmul b c) - jmul b (jmul a c)

theorem triple_def (a b c : J) :
    triple a b c = jmul (jmul a b) c + jmul a (jmul b c) - jmul b (jmul a c) := rfl

/-- {a,b,a} = U_a(b): the triple product recovers the U operator. -/
theorem triple_self_right (a b : J) : triple a b a = U a b := by
  simp only [triple, U_def, jsq_def]
  have h1 : jmul (jmul a b) a = jmul a (jmul a b) := jmul_comm _ _
  have h2 : jmul a (jmul b a) = jmul a (jmul a b) := by rw [jmul_comm b a]
  have h3 : jmul b (jmul a a) = jmul (jmul a a) b := jmul_comm _ _
  rw [h1, h2, h3, two_smul]

/-- Symmetry in outer variables: {a,b,c} = {c,b,a}. -/
theorem triple_comm_outer (a b c : J) : triple a b c = triple c b a := by
  simp only [triple]
  have h1 : jmul (jmul c b) a = jmul a (jmul b c) := by rw [jmul_comm c b, jmul_comm _ a]
  have h2 : jmul c (jmul b a) = jmul (jmul a b) c := by rw [jmul_comm b a, jmul_comm c _]
  have h3 : jmul b (jmul c a) = jmul b (jmul a c) := by rw [jmul_comm c a]
  rw [h1, h2, h3]; abel

/-- The V operator V_{a,b} as a linear map: V_{a,b}(x) = {a,b,x}. -/
def V_linear (a b : J) : J →ₗ[ℝ] J where
  toFun x := triple a b x
  map_add' x y := by simp only [triple, jmul_add]; abel
  map_smul' r x := by
    simp only [triple, RingHom.id_apply, smul_jmul, smul_sub, smul_add]

@[simp]
theorem V_linear_apply (a b x : J) : V_linear a b x = triple a b x := rfl

/-- V_{a,a}(x) = a²∘x: the self-V is multiplication by the square. -/
theorem V_self (a x : J) : V_linear a a x = jmul (jsq a) x := by
  simp only [V_linear_apply, triple, jsq_def]; abel

end JordanAlgebra
