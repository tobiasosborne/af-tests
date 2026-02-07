/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Macdonald.SpecialFF
import AfTests.Jordan.Basic
import AfTests.Jordan.Product

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

/-! ### Bilinearity of FreeJordanAlg.mul -/

/-- Right distributivity: mul (a + b) c = mul a c + mul b c. -/
theorem mul_add_left (a b c : FreeJordanAlg) : mul (a + b) c = mul a c + mul b c := by
  induction a using Quotient.ind; induction b using Quotient.ind; induction c using Quotient.ind
  show mk _ = mk _; congr 1; exact FreeNAAlg.add_mul _ _ _

/-- Left distributivity: mul a (b + c) = mul a b + mul a c. -/
theorem mul_add_right (a b c : FreeJordanAlg) : mul a (b + c) = mul a b + mul a c := by
  induction a using Quotient.ind; induction b using Quotient.ind; induction c using Quotient.ind
  show mk _ = mk _; congr 1; exact FreeNAAlg.mul_add _ _ _

/-- Left scalar compatibility: mul (r • a) b = r • mul a b. -/
theorem smul_mul_left (r : ℝ) (a b : FreeJordanAlg) : mul (r • a) b = r • mul a b := by
  induction a using Quotient.ind; induction b using Quotient.ind
  show mk _ = mk _; congr 1; exact FreeNAAlg.smul_mul _ _ _

/-- Right scalar compatibility: mul a (r • b) = r • mul a b. -/
theorem smul_mul_right (r : ℝ) (a b : FreeJordanAlg) : mul a (r • b) = r • mul a b := by
  induction a using Quotient.ind; induction b using Quotient.ind
  show mk _ = mk _; congr 1; exact FreeNAAlg.mul_smul _ _ _

/-- Left zero: mul 0 b = 0. -/
theorem mul_zero_left (b : FreeJordanAlg) : mul 0 b = 0 := by
  have h : mul 0 b = mul 0 b + mul 0 b := by
    calc mul 0 b = mul (0 + 0) b := by rw [add_zero]
      _ = mul 0 b + mul 0 b := mul_add_left 0 0 b
  calc mul 0 b = (mul 0 b + mul 0 b) - mul 0 b := by rw [add_sub_cancel_right]
    _ = mul 0 b - mul 0 b := by rw [← h]
    _ = 0 := sub_self _

/-- Right zero: mul a 0 = 0. -/
theorem mul_zero_right (a : FreeJordanAlg) : mul a 0 = 0 := by
  rw [mul_comm, mul_zero_left]

/-! ### Linearity of T -/

/-- T is additive in its first argument. -/
theorem T_add (a b v : FreeJordanAlg) : T (a + b) v = T a v + T b v := by
  simp only [T_apply]; exact mul_add_left a b v

/-- T is scalar-compatible in its first argument. -/
theorem T_smul (r : ℝ) (a v : FreeJordanAlg) : T (r • a) v = r • T a v := by
  simp only [T_apply]; exact smul_mul_left r a v

/-- T at zero is zero. -/
theorem T_zero (v : FreeJordanAlg) : T 0 v = 0 := by
  simp only [T_apply]; exact mul_zero_left v

end FreeJordanAlg

/-! ### JordanAlgebra instance for FreeJordanAlg -/

/-- FreeJordanAlg is a JordanAlgebra: it has commutative multiplication satisfying
    the Jordan identity, with unit, bilinearity, and scalar compatibility. -/
noncomputable instance : JordanAlgebra FreeJordanAlg where
  jmul := FreeJordanAlg.mul
  jmul_comm := FreeJordanAlg.mul_comm
  jordan_identity := FreeJordanAlg.jordan_identity
  jone := 1
  jone_jmul := FreeJordanAlg.one_mul_eq
  jmul_add := FreeJordanAlg.mul_add_right
  jmul_smul := FreeJordanAlg.smul_mul_left

/-! ### Bridge lemmas: JordanAlgebra ↔ FreeJordanAlg operators -/

@[simp] theorem FJ_jmul_eq_mul (a b : FreeJordanAlg) :
    JordanAlgebra.jmul a b = FreeJordanAlg.mul a b := rfl

@[simp] theorem FJ_jone_eq_one :
    (JordanAlgebra.jone : FreeJordanAlg) = 1 := rfl

theorem FJ_jpow_eq_pow (a : FreeJordanAlg) (n : ℕ) :
    JordanAlgebra.jpow a n = FreeJordanAlg.pow a n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [JordanAlgebra.jpow, FreeJordanAlg.pow, ih]

@[simp] theorem FJ_L_apply (a v : FreeJordanAlg) :
    JordanAlgebra.L a v = FreeJordanAlg.T a v := rfl
