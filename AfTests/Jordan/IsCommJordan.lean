/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Product
import Mathlib.Algebra.Jordan.Basic

/-!
# Bridge to Mathlib's IsCommJordan

This file provides instances connecting our bundled `JordanAlgebra` class to Mathlib's
`IsCommJordan` typeclass. This unlocks access to Mathlib's Jordan algebra lemmas,
particularly the linearized Jordan identity.

## Main results

* `JordanAlgebra.instMul` - Multiplication instance from `jmul`
* `JordanAlgebra.instNonUnitalNonAssocCommRing` - Ring structure
* `JordanAlgebra.instIsCommJordan` - The `IsCommJordan` instance

## Key lemma unlocked

* `two_nsmul_lie_lmul_lmul_add_add_eq_zero` - The linearized Jordan identity
-/

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-! ### Multiplication Instance -/

/-- Define multiplication on J using the Jordan product. -/
instance instMul : Mul J where
  mul := jmul

theorem mul_eq_jmul (a b : J) : a * b = jmul a b := rfl

/-! ### Ring Structure -/

/-- NonUnitalNonAssocRing instance from JordanAlgebra. -/
instance instNonUnitalNonAssocRing : NonUnitalNonAssocRing J :=
  NonUnitalNonAssocRing.mk
    (left_distrib := fun a b c => jmul_add a b c)
    (right_distrib := fun a b c => add_jmul a b c)
    (zero_mul := fun a => zero_jmul a)
    (mul_zero := fun a => jmul_zero a)

/-- NonUnitalNonAssocCommRing instance from JordanAlgebra. -/
instance instNonUnitalNonAssocCommRing : NonUnitalNonAssocCommRing J :=
  NonUnitalNonAssocCommRing.mk (mul_comm := fun a b => jmul_comm a b)

/-! ### IsCommJordan Instance -/

/-- IsCommJordan instance from JordanAlgebra.
The Jordan identity (a ∘ b) ∘ a² = a ∘ (b ∘ a²) is exactly what IsCommJordan requires. -/
instance instIsCommJordan : IsCommJordan J :=
  IsCommJordan.mk (lmul_comm_rmul_rmul := fun a b => jordan_identity a b)

/-! ### The Linearized Jordan Identity -/

/-- The linearized Jordan identity from Mathlib.
`2 • ([L_a, L_{bc}] + [L_b, L_{ca}] + [L_c, L_{ab}]) = 0`
where `[f, g]` is the Lie bracket (commutator) on AddMonoid.End. -/
theorem linearized_jordan_mathlib (a b c : J) :
    2 • (⁅AddMonoid.End.mulLeft a, AddMonoid.End.mulLeft (b * c)⁆ +
         ⁅AddMonoid.End.mulLeft b, AddMonoid.End.mulLeft (c * a)⁆ +
         ⁅AddMonoid.End.mulLeft c, AddMonoid.End.mulLeft (a * b)⁆) = 0 :=
  two_nsmul_lie_lmul_lmul_add_add_eq_zero a b c

/-- Version with jmul instead of * for consistency with our API. -/
theorem linearized_jordan_jmul (a b c : J) :
    2 • (⁅AddMonoid.End.mulLeft a, AddMonoid.End.mulLeft (jmul b c)⁆ +
         ⁅AddMonoid.End.mulLeft b, AddMonoid.End.mulLeft (jmul c a)⁆ +
         ⁅AddMonoid.End.mulLeft c, AddMonoid.End.mulLeft (jmul a b)⁆) = 0 :=
  linearized_jordan_mathlib a b c

/-! ### Connection: AddMonoid.End.mulLeft to L operator -/

/-- AddMonoid.End.mulLeft a applied to x equals jmul a x. -/
@[simp]
theorem mulLeft_apply (a x : J) : AddMonoid.End.mulLeft a x = jmul a x := rfl

/-- AddMonoid.End.mulLeft a applied to x equals L a x. -/
theorem mulLeft_eq_L_apply (a x : J) : AddMonoid.End.mulLeft a x = L a x := rfl

/-- The Lie bracket of mulLeft operators is the commutator on elements. -/
theorem lie_mulLeft_apply (f g : J) (x : J) :
    ⁅AddMonoid.End.mulLeft f, AddMonoid.End.mulLeft g⁆ x =
    jmul f (jmul g x) - jmul g (jmul f x) := by
  simp only [Ring.lie_def]
  rfl

end JordanAlgebra
