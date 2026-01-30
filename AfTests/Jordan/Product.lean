/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Basic
import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# Jordan Algebra Multiplication Operators

This file defines the left multiplication operator for Jordan algebras and proves
that left multiplication by `a` and `a²` commute (the linearized Jordan identity).

## Main definitions

* `JordanAlgebra.L` - Left multiplication operator `L_a(b) = a ∘ b`
* `JordanAlgebra.Lsq` - Squaring operator `L_sq(a) = a²`

## Main results

* `JordanAlgebra.L_comm_L_sq` - `L_a ∘ L_{a²} = L_{a²} ∘ L_a`
-/

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-! ### Left Multiplication Operator -/

/-- Left multiplication by `a` as a linear map. -/
def L (a : J) : J →ₗ[ℝ] J where
  toFun b := jmul a b
  map_add' b c := jmul_add a b c
  map_smul' r b := smul_jmul r a b

@[simp]
theorem L_apply (a b : J) : L a b = jmul a b := rfl

theorem L_one : L (jone : J) = LinearMap.id := by
  ext b
  simp [jone_jmul]

theorem L_comm (a : J) : L a = L a := rfl

/-- The squaring map as a function. -/
def Lsq (a : J) : J := jsq a

theorem Lsq_eq_L_apply (a : J) : Lsq a = L a a := by
  simp [Lsq, jsq_def]

/-! ### Jordan Identity for Operators -/

/-- Key theorem: L_a and L_{a²} commute.
This is the operator form of the Jordan identity. -/
theorem L_comm_L_sq (a : J) : L a ∘ₗ L (jsq a) = L (jsq a) ∘ₗ L a := by
  ext b
  simp only [LinearMap.comp_apply, L_apply, jsq_def]
  -- Need to show: jmul a (jmul (jmul a a) b) = jmul (jmul a a) (jmul a b)
  -- By commutativity: jmul (jmul a a) b = jmul b (jmul a a)
  -- Jordan identity gives: jmul (jmul a b) (jmul a a) = jmul a (jmul b (jmul a a))
  rw [jmul_comm (jmul a a) b]
  rw [← jordan_identity a b]
  rw [jmul_comm]

/-- Commute version of L_comm_L_sq using Commute. -/
theorem L_commute_L_sq (a : J) : Commute (L a) (L (jsq a)) := L_comm_L_sq a

/-! ### Power Properties -/

theorem jpow_add_one (a : J) (n : ℕ) : jpow a (n + 1) = jmul a (jpow a n) := rfl

theorem L_jpow_succ (a : J) (n : ℕ) : jpow a (n + 1) = L a (jpow a n) := rfl

/-- Powers associate: a ∘ (a^n) = a^(n+1) -/
theorem jmul_jpow (a : J) (n : ℕ) : jmul a (jpow a n) = jpow a (n + 1) := rfl

/-- Square in terms of L. -/
theorem jsq_eq_L (a : J) : jsq a = L a a := rfl

end JordanAlgebra
