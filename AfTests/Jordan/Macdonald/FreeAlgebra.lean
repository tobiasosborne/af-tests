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
    `mul (∑ rᵢ • mᵢ) (∑ sⱼ • nⱼ) = ∑ᵢⱼ (rᵢ * sⱼ) • (mᵢ * nⱼ)` -/
noncomputable def mul (f g : FreeNAAlg) : FreeNAAlg :=
  f.sum fun m₁ r₁ => g.sum fun m₂ r₂ => Finsupp.single (m₁ * m₂) (r₁ * r₂)

/-- Multiplication on basis elements. -/
@[simp]
theorem mul_ι (m₁ m₂ : FreeMagma) : mul (ι m₁) (ι m₂) = ι (m₁ * m₂) := by
  unfold mul ι
  rw [Finsupp.sum_single_index]
  · rw [Finsupp.sum_single_index] <;> simp
  · simp

/-- Left distributivity. -/
theorem mul_add (f g₁ g₂ : FreeNAAlg) : mul f (g₁ + g₂) = mul f g₁ + mul f g₂ := by
  sorry -- bilinearity of Finsupp.sum

/-- Right distributivity. -/
theorem add_mul (f₁ f₂ g : FreeNAAlg) : mul (f₁ + f₂) g = mul f₁ g + mul f₂ g := by
  sorry -- bilinearity of Finsupp.sum

/-- Left scalar compatibility. -/
theorem smul_mul (r : ℝ) (f g : FreeNAAlg) : mul (r • f) g = r • mul f g := by
  sorry -- scalar pulling through Finsupp.sum

/-- Right scalar compatibility. -/
theorem mul_smul (r : ℝ) (f g : FreeNAAlg) : mul f (r • g) = r • mul f g := by
  sorry -- scalar pulling through Finsupp.sum

/-- Left unit law. -/
theorem e_mul (f : FreeNAAlg) : mul e f = f := by
  sorry -- reduce to FreeMagma.one * m = m (needs unit law on FreeMagma)

/-- Right unit law. -/
theorem mul_e (f : FreeNAAlg) : mul f e = f := by
  sorry -- reduce to m * FreeMagma.one = m (needs unit law on FreeMagma)

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
