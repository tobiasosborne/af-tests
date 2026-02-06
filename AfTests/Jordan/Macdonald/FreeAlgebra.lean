/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# Free Nonassociative Algebra with Unit

Macdonald Step 4: Define the free nonassociative ℝ-algebra with unit on two generators.

## Main definitions

* `FreeMagma` - Free nonassociative magma with unit on generators `Fin 2`
* `FreeNAAlg` - Free nonassociative ℝ-algebra = formal ℝ-linear combinations of `FreeMagma`
* `FreeNAAlg.x`, `FreeNAAlg.y` - The two generators as algebra elements
* `FreeNAAlg.mul` - Bilinear extension of magma multiplication

## Design notes

For Macdonald's theorem we need only 2 generators (x and y). The free algebra FA{x,y}
is the key object. We quotient it by the Jordan identity to get FJ{x,y}, and embed into
an associative algebra to get FS{x,y}.
-/

/-- Free nonassociative magma with unit on generators indexed by `Fin 2`.
    Elements are binary trees with leaves labeled by generators or the unit. -/
inductive FreeMagma where
  | gen : Fin 2 → FreeMagma
  | one : FreeMagma
  | mul : FreeMagma → FreeMagma → FreeMagma
  deriving DecidableEq

instance : Mul FreeMagma := ⟨FreeMagma.mul⟩
instance : One FreeMagma := ⟨FreeMagma.one⟩

@[simp] theorem FreeMagma.mul_eq (a b : FreeMagma) : FreeMagma.mul a b = a * b := rfl
@[simp] theorem FreeMagma.one_eq : FreeMagma.one = (1 : FreeMagma) := rfl

/-- Multiplication with unit normalization: 1 * m = m, m * 1 = m. -/
def FreeMagma.unitMul : FreeMagma → FreeMagma → FreeMagma
  | .one, m => m
  | m, .one => m
  | m₁, m₂ => .mul m₁ m₂

@[simp] theorem FreeMagma.one_unitMul (m : FreeMagma) : (1 : FreeMagma).unitMul m = m := rfl

@[simp] theorem FreeMagma.unitMul_one (m : FreeMagma) : m.unitMul (1 : FreeMagma) = m := by
  cases m <;> rfl

/-- The free nonassociative ℝ-algebra with unit on two generators.
    Elements are formal ℝ-linear combinations of `FreeMagma` words. -/
noncomputable abbrev FreeNAAlg := FreeMagma →₀ ℝ

namespace FreeNAAlg

/-- Embedding of a magma element as an algebra element (basis vector). -/
noncomputable def ι (m : FreeMagma) : FreeNAAlg := Finsupp.single m 1

/-- Generator x. -/
noncomputable def x : FreeNAAlg := ι (FreeMagma.gen 0)

/-- Generator y. -/
noncomputable def y : FreeNAAlg := ι (FreeMagma.gen 1)

/-- The unit element of the free algebra. -/
noncomputable def e : FreeNAAlg := ι FreeMagma.one

-- Inherited structure from Finsupp
noncomputable instance : Module ℝ FreeNAAlg := inferInstance
noncomputable instance : AddCommGroup FreeNAAlg := inferInstance

/-- Multiplication on the free algebra, extending magma multiplication bilinearly.
    Uses `unitMul` to normalize unit: `1 * m = m` and `m * 1 = m`.
    `mul (∑ rᵢ • mᵢ) (∑ sⱼ • nⱼ) = ∑ᵢⱼ (rᵢ * sⱼ) • (mᵢ ·ᵤ nⱼ)` -/
noncomputable def mul (f g : FreeNAAlg) : FreeNAAlg :=
  f.sum fun m₁ r₁ => g.sum fun m₂ r₂ => Finsupp.single (m₁.unitMul m₂) (r₁ * r₂)

/-- Multiplication on basis elements. -/
@[simp]
theorem mul_ι (m₁ m₂ : FreeMagma) : mul (ι m₁) (ι m₂) = ι (m₁.unitMul m₂) := by
  unfold mul ι
  rw [Finsupp.sum_single_index]
  · rw [Finsupp.sum_single_index] <;> simp
  · simp

/-- Left distributivity. -/
theorem mul_add (f g₁ g₂ : FreeNAAlg) : mul f (g₁ + g₂) = mul f g₁ + mul f g₂ := by
  unfold mul
  conv_lhs =>
    arg 2
    ext m₁ r₁
    rw [Finsupp.sum_add_index
      (by intro m₂ _; simp)
      (by intro m₂ _ b₁ b₂; simp [_root_.mul_add])]
  rw [Finsupp.sum_add]

/-- Right distributivity. -/
theorem add_mul (f₁ f₂ g : FreeNAAlg) : mul (f₁ + f₂) g = mul f₁ g + mul f₂ g := by
  unfold mul
  rw [Finsupp.sum_add_index
    (by intro m₁ _; simp)
    (by intro m₁ _ b₁ b₂
        rw [← Finsupp.sum_add]
        congr 1
        ext m₂ r₂
        simp [_root_.add_mul])]

/-- Left scalar compatibility. -/
theorem smul_mul (r : ℝ) (f g : FreeNAAlg) : mul (r • f) g = r • mul f g := by
  unfold mul
  rw [Finsupp.sum_smul_index (by intro i; simp)]
  simp_rw [Finsupp.sum, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul, mul_assoc]

/-- Right scalar compatibility. -/
theorem mul_smul (r : ℝ) (f g : FreeNAAlg) : mul f (r • g) = r • mul f g := by
  unfold mul
  conv_lhs =>
    arg 2
    ext m₁ r₁
    rw [Finsupp.sum_smul_index (by intro i; simp)]
  simp_rw [Finsupp.sum, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul, mul_left_comm]

/-- Left unit law. -/
theorem e_mul (f : FreeNAAlg) : mul e f = f := by
  unfold mul e ι
  rw [Finsupp.sum_single_index (by simp)]
  change (f.sum fun m₂ r₂ => Finsupp.single ((1 : FreeMagma).unitMul m₂) (1 * r₂)) = f
  simp_rw [FreeMagma.one_unitMul, one_mul]
  exact Finsupp.sum_single f

/-- Right unit law. -/
theorem mul_e (f : FreeNAAlg) : mul f e = f := by
  unfold mul e ι
  conv_lhs =>
    arg 2
    ext m₁ r₁
    rw [Finsupp.sum_single_index (by simp)]
  change (f.sum fun m₁ r₁ => Finsupp.single (m₁.unitMul (1 : FreeMagma)) (r₁ * 1)) = f
  simp_rw [FreeMagma.unitMul_one, mul_one]
  exact Finsupp.sum_single f

/-- Generators are distinct from the unit. -/
theorem x_ne_e : x ≠ e := by
  unfold x e ι
  intro h
  exact absurd (Finsupp.single_left_injective (show (1:ℝ) ≠ 0 by norm_num) h) (by decide)

theorem y_ne_e : y ≠ e := by
  unfold y e ι
  intro h
  exact absurd (Finsupp.single_left_injective (show (1:ℝ) ≠ 0 by norm_num) h) (by decide)

theorem x_ne_y : x ≠ y := by
  unfold x y ι
  intro h
  exact absurd (Finsupp.single_left_injective (show (1:ℝ) ≠ 0 by norm_num) h) (by decide)

end FreeNAAlg
