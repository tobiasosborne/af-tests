/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import AfTests.Jordan.Basic

/-!
# Spin Factors

The spin factor V_n is a Jordan algebra defined on ℝ × ℝⁿ with the product
`(α, v) ∘ (β, w) = (αβ + ⟨v, w⟩, αw + βv)`.

## Main definitions

* `SpinFactor n` - The type ℝ × EuclideanSpace ℝ (Fin n)
* `SpinFactor.jordanMul` - The Jordan product on spin factors
* `SpinFactor.one` - The identity element (1, 0)

## Main results

* `SpinFactor.jordanMul_comm` - Jordan product is commutative
* `SpinFactor.jordanAlgebra` - Spin factor is a Jordan algebra

## References

* Faraut-Korányi "Analysis on Symmetric Cones"
-/

/-- The spin factor V_n: ℝ × ℝⁿ with Jordan product. -/
abbrev SpinFactor (n : ℕ) := ℝ × EuclideanSpace ℝ (Fin n)

namespace SpinFactor

variable {n : ℕ}

/-! ### Basic instances -/

instance : Inhabited (SpinFactor n) := ⟨(0, 0)⟩

/-! ### Jordan product -/

/-- The Jordan product on spin factors:
  `(α, v) ∘ (β, w) = (αβ + ⟨v, w⟩, αw + βv)` -/
noncomputable def jordanMul (x y : SpinFactor n) : SpinFactor n :=
  (x.1 * y.1 + @inner ℝ _ _ x.2 y.2, x.1 • y.2 + y.1 • x.2)

/-- The identity element (1, 0). -/
def one : SpinFactor n := (1, 0)

/-! ### Component accessors -/

/-- The scalar component of a spin factor element. -/
def scalar (x : SpinFactor n) : ℝ := x.1

/-- The vector component of a spin factor element. -/
def vector (x : SpinFactor n) : EuclideanSpace ℝ (Fin n) := x.2

/-! ### Basic properties -/

theorem jordanMul_comm (x y : SpinFactor n) : jordanMul x y = jordanMul y x := by
  unfold jordanMul
  congr 1
  · rw [real_inner_comm]; ring
  · apply PiLp.ext; intro i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring

theorem one_jordanMul (x : SpinFactor n) : jordanMul one x = x := by
  unfold jordanMul one
  simp only [one_mul, inner_zero_left, add_zero, one_smul, smul_zero, add_zero]

theorem jordanMul_one (x : SpinFactor n) : jordanMul x one = x := by
  rw [jordanMul_comm, one_jordanMul]

theorem jordanMul_add (x y z : SpinFactor n) :
    jordanMul x (y + z) = jordanMul x y + jordanMul x z := by
  unfold jordanMul
  simp only [Prod.fst_add, Prod.snd_add, inner_add_right, smul_add, Prod.mk_add_mk]
  congr 1
  · ring
  · apply PiLp.ext; intro i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring

theorem jordanMul_smul (r : ℝ) (x y : SpinFactor n) :
    jordanMul (r • x) y = r • jordanMul x y := by
  unfold jordanMul
  simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_left, RCLike.conj_to_real,
    smul_smul, Prod.smul_mk]
  congr 1
  · simp only [smul_eq_mul]; ring
  · apply PiLp.ext; intro i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring

/-- The square of a spin factor element. -/
noncomputable def sq (x : SpinFactor n) : SpinFactor n := jordanMul x x

theorem sq_def (x : SpinFactor n) : sq x = jordanMul x x := rfl

theorem sq_scalar (x : SpinFactor n) :
    (sq x).1 = x.1 ^ 2 + @inner ℝ _ _ x.2 x.2 := by
  unfold sq jordanMul
  ring

theorem sq_vector (x : SpinFactor n) :
    (sq x).2 = (2 * x.1) • x.2 := by
  unfold sq jordanMul
  apply PiLp.ext; intro i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-! ### Jordan identity -/

/-- The Jordan identity for spin factors.
  This is the key axiom: `(x ∘ y) ∘ x² = x ∘ (y ∘ x²)` -/
theorem jordan_identity (x y : SpinFactor n) :
    jordanMul (jordanMul x y) (sq x) = jordanMul x (jordanMul y (sq x)) := by
  -- Let α = x.1, β = y.1, v = x.2, w = y.2
  -- sq x = (α² + ⟨v,v⟩, 2αv)
  -- LHS: ((αβ + ⟨v,w⟩, αw + βv) ∘ (α² + ⟨v,v⟩, 2αv))
  -- RHS: (α,v) ∘ ((β,w) ∘ (α² + ⟨v,v⟩, 2αv))
  simp only [sq, jordanMul]
  simp only [inner_add_left, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
    inner_add_right, smul_add, smul_smul]
  congr 1
  · ring
  · apply PiLp.ext; intro i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [real_inner_comm x.2 y.2]
    ring

/-! ### Jordan algebra instance -/

noncomputable instance jordanAlgebra : JordanAlgebra (SpinFactor n) where
  jmul := jordanMul
  jmul_comm := jordanMul_comm
  jordan_identity := jordan_identity
  jone := one
  jone_jmul := one_jordanMul
  jmul_add := jordanMul_add
  jmul_smul := jordanMul_smul

/-! ### Notation -/

scoped infixl:70 " ∘ᵥ " => jordanMul

end SpinFactor
