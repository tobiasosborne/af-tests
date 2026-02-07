/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Macdonald.FreeSpecialJordan
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module

/-!
# Fundamental Formula in Special (Associative) Jordan Algebras

Macdonald Step 7: Proves the fundamental formula `U_{U_a(b)} = U_a U_b U_a`
in any associative algebra. This is trivially true since `U_a(b) = aba` and
`(aba)x(aba) = a(b(axa)b)a` by associativity.

## Main results

* `assocU` -- the associative U operator: `U_a(b) = aba`
* `assoc_fundamental_formula` -- `(aba)x(aba) = a(b(axa)b)a` by `noncomm_ring`
* `FreeJordanAlg.evalAssoc_U` -- `evalAssoc` maps Jordan U to associative U
* `special_fundamental_formula` -- FF holds for all `FreeJordanAlg` elements
  evaluated in any associative algebra

## References

* Hanche-Olsen & Stormer, "Jordan Operator Algebras" (1984), Section 2.4
-/

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-! ### The associative U operator -/

/-- The associative U operator: `U_a(b) = aba`. In any associative algebra
with Jordan product `a circ b = 1/2(ab+ba)`, the Jordan U operator
`U_a(b) = 2 a circ (a circ b) - a^2 circ b` reduces to `aba`. -/
def assocU (a b : A) : A := a * b * a

/-- The fundamental formula in associative algebras: `(aba)x(aba) = a(b(axa)b)a`.
This is immediate from associativity of multiplication. -/
theorem assoc_fundamental_formula {B : Type*} [Ring B] (a b x : B) :
    assocU (assocU a b) x = assocU a (assocU b (assocU a x)) := by
  unfold assocU; noncomm_ring

/-! ### evalAssoc compatibility lemmas -/

theorem FreeJordanAlg.evalAssoc_neg (a b : A) (u : FreeJordanAlg) :
    FreeJordanAlg.evalAssoc a b (-u) =
    -FreeJordanAlg.evalAssoc a b u := by
  have : -u = (-1 : ℝ) • u := by simp
  rw [this, FreeJordanAlg.evalAssoc_smul, neg_one_smul]

theorem FreeJordanAlg.evalAssoc_sub (a b : A) (u v : FreeJordanAlg) :
    FreeJordanAlg.evalAssoc a b (u - v) =
    FreeJordanAlg.evalAssoc a b u -
    FreeJordanAlg.evalAssoc a b v := by
  rw [sub_eq_add_neg, evalAssoc_add, evalAssoc_neg, ← sub_eq_add_neg]

/-! ### Jordan U on the free Jordan algebra -/

/-- The Jordan U operator on `FreeJordanAlg`:
`U_a(b) = 2 * a circ (a circ b) - a^2 circ b`. -/
noncomputable def FreeJordanAlg.U
    (a b : FreeJordanAlg) : FreeJordanAlg :=
  (2 : ℝ) • FreeJordanAlg.mul a (FreeJordanAlg.mul a b) -
    FreeJordanAlg.mul (FreeJordanAlg.mul a a) b

/-- `evalAssoc` maps the Jordan U operator to the associative U operator:
`evalAssoc(U_a(b)) = a' * b' * a'` where `a' = evalAssoc(a)`, `b' = evalAssoc(b)`.
This is the key link between Jordan and associative U operators. -/
theorem FreeJordanAlg.evalAssoc_U (a' b' : A)
    (u v : FreeJordanAlg) :
    FreeJordanAlg.evalAssoc a' b' (FreeJordanAlg.U u v) =
    assocU (evalAssoc a' b' u) (evalAssoc a' b' v) := by
  set p := FreeJordanAlg.evalAssoc a' b' u
  set q := FreeJordanAlg.evalAssoc a' b' v
  unfold FreeJordanAlg.U assocU
  rw [evalAssoc_sub, evalAssoc_smul,
      evalAssoc_mul, evalAssoc_mul,
      evalAssoc_mul, evalAssoc_mul]
  simp only [mul_add, add_mul, smul_add, smul_mul_assoc,
    mul_smul_comm, smul_smul, mul_assoc]
  rw [show (2 : ℝ) * (1 / 2 * (1 / 2)) = (1 / 2 : ℝ) from by norm_num]
  module

/-! ### The fundamental formula in special algebras -/

/-- The fundamental formula holds for all `FreeJordanAlg` elements when
evaluated in any associative algebra: `evalAssoc(U_{U_a(b)}(x))` equals
`evalAssoc(U_a(U_b(U_a(x))))`. This is the content of "FF holds in
special Jordan algebras". -/
theorem special_fundamental_formula (a' b' : A)
    (u v w : FreeJordanAlg) :
    FreeJordanAlg.evalAssoc a' b'
      (FreeJordanAlg.U (FreeJordanAlg.U u v) w) =
    FreeJordanAlg.evalAssoc a' b'
      (FreeJordanAlg.U u (FreeJordanAlg.U v (FreeJordanAlg.U u w))) := by
  simp only [FreeJordanAlg.evalAssoc_U]
  exact assoc_fundamental_formula _ _ _
