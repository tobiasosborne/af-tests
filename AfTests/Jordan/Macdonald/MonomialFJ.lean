/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Macdonald.FreeSpecialJordan

/-!
# M_{p,q} Monomials in the Free Jordan Algebra

Macdonald Step 10: Define M_{p,q} as elements of FreeJordanAlg and prove
base cases and evalAssoc compatibility.

## Main definitions

* `M_eval_FJ` — M_{p,q} evaluated in FreeJordanAlg using generators x,y

## Main results

* `M_eval_FJ_zero_zero` — M_{0,0} = 1
* `M_eval_FJ_one_zero` — M_{1,0} = x
* `M_eval_FJ_zero_one` — M_{0,1} = y
* `evalAssoc_M_eval_FJ_one_zero` — evalAssoc(M_{1,0}) = a
* `evalAssoc_M_eval_FJ_zero_one` — evalAssoc(M_{0,1}) = b
* `evalAssoc_M_eval_FJ_two_zero` — evalAssoc(M_{2,0}) = a^2
* `evalAssoc_M_eval_FJ_one_one` — evalAssoc(M_{1,1}) = 1/2(ab + ba)
* `evalAssoc_M_eval_FJ_zero_two` — evalAssoc(M_{0,2}) = b^2

## References

* Hanche-Olsen & Stormer, "Jordan Operator Algebras", 2.4.22-2.4.24
-/

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-! ### Definition -/

/-- M_{p,q} as an element of the free Jordan algebra FJ{x,y}.
    Mirrors `JordanAlgebra.M_eval` but uses FreeJordanAlg operations:
    - M_{0,0} = 1
    - M_{p+1,q} = x * M_{p,q}   (left Jordan multiply by x)
    - M_{0,q+1} = M_{0,q} * y   (right Jordan multiply by y) -/
noncomputable def M_eval_FJ : ℕ → ℕ → FreeJordanAlg
  | 0, 0 => 1
  | p + 1, q => FreeJordanAlg.mul FreeJordanAlg.x (M_eval_FJ p q)
  | 0, q + 1 => FreeJordanAlg.mul (M_eval_FJ 0 q) FreeJordanAlg.y

/-! ### Unfolding lemmas -/

@[simp] theorem M_eval_FJ_zero_zero : M_eval_FJ 0 0 = 1 := by
  unfold M_eval_FJ; rfl

@[simp] theorem M_eval_FJ_succ_left (p q : ℕ) :
    M_eval_FJ (p + 1) q =
    FreeJordanAlg.mul FreeJordanAlg.x (M_eval_FJ p q) := by
  simp only [M_eval_FJ]

@[simp] theorem M_eval_FJ_zero_succ (q : ℕ) :
    M_eval_FJ 0 (q + 1) =
    FreeJordanAlg.mul (M_eval_FJ 0 q) FreeJordanAlg.y := by
  simp only [M_eval_FJ]

/-! ### Base cases -/

theorem M_eval_FJ_one_zero : M_eval_FJ 1 0 = FreeJordanAlg.x := by
  simp only [M_eval_FJ_succ_left, M_eval_FJ_zero_zero]
  unfold FreeJordanAlg.x FreeJordanAlg.mul
  show FreeJordanAlg.mk (FreeNAAlg.mul FreeNAAlg.x FreeNAAlg.e) =
       FreeJordanAlg.mk FreeNAAlg.x
  congr 1; exact FreeNAAlg.mul_e _

theorem M_eval_FJ_zero_one : M_eval_FJ 0 1 = FreeJordanAlg.y := by
  simp only [M_eval_FJ_zero_succ, M_eval_FJ_zero_zero]
  unfold FreeJordanAlg.y FreeJordanAlg.mul
  show FreeJordanAlg.mk (FreeNAAlg.mul FreeNAAlg.e FreeNAAlg.y) =
       FreeJordanAlg.mk FreeNAAlg.y
  congr 1; exact FreeNAAlg.e_mul _

/-! ### evalAssoc on 1 -/

theorem evalAssoc_one (a b : A) :
    FreeJordanAlg.evalAssoc a b (1 : FreeJordanAlg) = 1 := by
  change FreeNAAlg.evalJordanFun a b FreeNAAlg.e = 1
  rw [FreeNAAlg.e, FreeNAAlg.evalJordanFun_ι]
  exact FreeMagma.evalJordan_one a b

/-! ### evalAssoc compatibility for base cases -/

theorem evalAssoc_M_eval_FJ_one_zero (a b : A) :
    FreeJordanAlg.evalAssoc a b (M_eval_FJ 1 0) = a := by
  rw [M_eval_FJ_one_zero]; exact FreeJordanAlg.evalAssoc_x a b

theorem evalAssoc_M_eval_FJ_zero_one (a b : A) :
    FreeJordanAlg.evalAssoc a b (M_eval_FJ 0 1) = b := by
  rw [M_eval_FJ_zero_one]; exact FreeJordanAlg.evalAssoc_y a b

/-- evalAssoc(M_{2,0}) = a*a. -/
theorem evalAssoc_M_eval_FJ_two_zero (a b : A) :
    FreeJordanAlg.evalAssoc a b (M_eval_FJ 2 0) = a * a := by
  simp only [M_eval_FJ_succ_left, M_eval_FJ_zero_zero]
  rw [FreeJordanAlg.evalAssoc_mul, FreeJordanAlg.evalAssoc_mul,
      evalAssoc_one]
  simp only [FreeJordanAlg.evalAssoc_x, mul_one, one_mul]
  rw [← two_smul ℝ a, smul_smul]
  simp only [show (1 / 2 : ℝ) * 2 = 1 from by norm_num, one_smul]
  rw [← two_smul ℝ (a * a), smul_smul]
  simp only [show (1 / 2 : ℝ) * 2 = 1 from by norm_num, one_smul]

/-- evalAssoc(M_{1,1}) = 1/2(ab + ba), the symmetrized product. -/
theorem evalAssoc_M_eval_FJ_one_one (a b : A) :
    FreeJordanAlg.evalAssoc a b (M_eval_FJ 1 1) =
    (1/2 : ℝ) • (a * b + b * a) := by
  simp only [M_eval_FJ_succ_left, M_eval_FJ_zero_succ, M_eval_FJ_zero_zero]
  rw [FreeJordanAlg.evalAssoc_mul, FreeJordanAlg.evalAssoc_mul,
      evalAssoc_one]
  simp only [FreeJordanAlg.evalAssoc_x, FreeJordanAlg.evalAssoc_y,
             one_mul, mul_one]
  rw [← two_smul ℝ b, smul_smul]
  simp only [show (1 / 2 : ℝ) * 2 = 1 from by norm_num, one_smul]

/-- evalAssoc(M_{0,2}) = b*b. -/
theorem evalAssoc_M_eval_FJ_zero_two (a b : A) :
    FreeJordanAlg.evalAssoc a b (M_eval_FJ 0 2) = b * b := by
  simp only [M_eval_FJ_zero_succ, M_eval_FJ_zero_zero]
  rw [FreeJordanAlg.evalAssoc_mul, FreeJordanAlg.evalAssoc_mul,
      evalAssoc_one]
  simp only [FreeJordanAlg.evalAssoc_y, one_mul, mul_one]
  rw [← two_smul ℝ b, smul_smul]
  simp only [show (1 / 2 : ℝ) * 2 = 1 from by norm_num, one_smul]
  rw [← two_smul ℝ (b * b), smul_smul]
  simp only [show (1 / 2 : ℝ) * 2 = 1 from by norm_num, one_smul]
