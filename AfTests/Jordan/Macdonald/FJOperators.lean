/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Macdonald.SpecialFF

/-!
# Operators on the Free Jordan Algebra

Defines powers and multiplication operators (T, U, U_bilinear) on `FreeJordanAlg`,
needed for the M_{p,q} construction in H-O 2.4.24.

## Main definitions

* `FreeJordanAlg.pow` — Jordan powers: a^0 = 1, a^(n+1) = a ∘ a^n
* `FreeJordanAlg.T` — Left multiplication operator: T_a(v) = a ∘ v
* `FreeJordanAlg.U_bilinear` — Bilinearized U: U_{a,b}(v) = {a,v,b}
                                 = a∘(b∘v) + b∘(a∘v) - (a∘b)∘v

## Main results

* `FreeJordanAlg.pow_zero`, `pow_succ` — unfolding lemmas
* `FreeJordanAlg.T_apply` — T_a(v) = mul a v
* `FreeJordanAlg.U_bilinear_apply` — U_{a,b}(v) = mul a (mul b v) + mul b (mul a v) - mul (mul a b) v
* `FreeJordanAlg.U_bilinear_self` — U_{a,a} = U_a

## References

* Hanche-Olsen & Størmer, "Jordan Operator Algebras", §2.4
-/

namespace FreeJordanAlg

/-! ### Unit laws for FreeJordanAlg.mul -/

/-- Right unit law: mul a 1 = a. -/
theorem mul_one_eq (a : FreeJordanAlg) : mul a 1 = a := by
  induction a using Quotient.ind
  show mk (FreeNAAlg.mul _ FreeNAAlg.e) = mk _
  congr 1; exact FreeNAAlg.mul_e _

/-- Left unit law: mul 1 a = a. -/
theorem one_mul_eq (a : FreeJordanAlg) : mul 1 a = a := by
  induction a using Quotient.ind
  show mk (FreeNAAlg.mul FreeNAAlg.e _) = mk _
  congr 1; exact FreeNAAlg.e_mul _

/-! ### Powers -/

/-- Jordan powers in FreeJordanAlg: a^0 = 1, a^(n+1) = a ∘ a^n. -/
noncomputable def pow (a : FreeJordanAlg) : ℕ → FreeJordanAlg
  | 0 => 1
  | n + 1 => mul a (pow a n)

@[simp] theorem pow_zero (a : FreeJordanAlg) : pow a 0 = 1 := rfl
@[simp] theorem pow_succ (a : FreeJordanAlg) (n : ℕ) :
    pow a (n + 1) = mul a (pow a n) := rfl

theorem pow_one (a : FreeJordanAlg) : pow a 1 = a := by
  simp [mul_one_eq]

/-! ### Left multiplication operator T -/

/-- T_a(v) = a ∘ v, left multiplication by a. -/
noncomputable def T (a : FreeJordanAlg) (v : FreeJordanAlg) : FreeJordanAlg :=
  mul a v

@[simp] theorem T_apply (a v : FreeJordanAlg) : T a v = mul a v := rfl

/-! ### Bilinearized U operator -/

/-- U_{a,b}(v) = a∘(b∘v) + b∘(a∘v) - (a∘b)∘v.
    This is the "triple product" {a,v,b} in the free Jordan algebra. -/
noncomputable def U_bilinear (a b v : FreeJordanAlg) : FreeJordanAlg :=
  mul a (mul b v) + mul b (mul a v) - mul (mul a b) v

@[simp] theorem U_bilinear_apply (a b v : FreeJordanAlg) :
    U_bilinear a b v = mul a (mul b v) + mul b (mul a v) - mul (mul a b) v := rfl

/-- U_{a,a}(v) = U_a(v): bilinearized U at equal arguments recovers quadratic U. -/
theorem U_bilinear_self (a v : FreeJordanAlg) :
    U_bilinear a a v = U a v := by
  simp only [U_bilinear_apply, U]
  -- U a v = (2:ℝ) • mul a (mul a v) - mul (mul a a) v
  -- U_bilinear a a v = mul a (mul a v) + mul a (mul a v) - mul (mul a a) v
  -- Need: x + x = (2:ℝ) • x
  rw [show mul a (mul a v) + mul a (mul a v) = (2 : ℝ) • mul a (mul a v) from by
    rw [two_smul]]

/-- Symmetry: U_{a,b} = U_{b,a}. -/
theorem U_bilinear_comm (a b v : FreeJordanAlg) :
    U_bilinear a b v = U_bilinear b a v := by
  simp only [U_bilinear_apply]
  rw [mul_comm a b]
  abel

/-- U_{a,1}(v) = T_a(v) = a ∘ v. -/
theorem U_bilinear_one_right (a v : FreeJordanAlg) :
    U_bilinear a 1 v = T a v := by
  simp only [U_bilinear_apply, T_apply]
  rw [one_mul_eq v, one_mul_eq (mul a v), mul_one_eq a]
  abel

end FreeJordanAlg
