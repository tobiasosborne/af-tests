/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import Mathlib.Algebra.Jordan.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic

/-!
# Bundled Jordan Algebras

This file defines a bundled `JordanAlgebra` structure over the reals.

## Main definitions

* `JordanAlgebra` - A unital, commutative Jordan algebra over ℝ
* `JordanAlgebra.jmul` - The Jordan product
* `JordanAlgebra.jone` - The multiplicative identity

## Implementation Notes

Mathlib provides `IsCommJordan` as a property on rings. We define a bundled structure
that includes the Jordan product as part of the data, rather than inheriting from
a ring structure. This is more natural for Jordan algebras that don't arise from
associative algebras (e.g., exceptional Jordan algebras).

The Jordan identity is: `(a ∘ b) ∘ a² = a ∘ (b ∘ a²)`
-/

/-- A unital commutative Jordan algebra over ℝ. -/
class JordanAlgebra (J : Type*) extends AddCommGroup J, Module ℝ J where
  /-- The Jordan product. -/
  jmul : J → J → J
  /-- Jordan product is commutative. -/
  jmul_comm : ∀ a b, jmul a b = jmul b a
  /-- The Jordan identity: (a ∘ b) ∘ a² = a ∘ (b ∘ a²). -/
  jordan_identity : ∀ a b, jmul (jmul a b) (jmul a a) = jmul a (jmul b (jmul a a))
  /-- The multiplicative identity. -/
  jone : J
  /-- Left identity. -/
  jone_jmul : ∀ a, jmul jone a = a
  /-- Bilinearity: left addition. -/
  jmul_add : ∀ a b c, jmul a (b + c) = jmul a b + jmul a c
  /-- Bilinearity: scalar multiplication. -/
  jmul_smul : ∀ (r : ℝ) a b, jmul (r • a) b = r • jmul a b

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-! ### Basic Properties -/

theorem jmul_jone (a : J) : jmul a jone = a := by
  rw [jmul_comm, jone_jmul]

theorem add_jmul (a b c : J) : jmul (a + b) c = jmul a c + jmul b c := by
  rw [jmul_comm, jmul_add, jmul_comm c a, jmul_comm c b]

theorem smul_jmul (r : ℝ) (a b : J) : jmul a (r • b) = r • jmul a b := by
  rw [jmul_comm, jmul_smul, jmul_comm]

theorem jmul_zero (a : J) : jmul a 0 = 0 := by
  have h : jmul a 0 + jmul a 0 = jmul a 0 := by
    calc jmul a 0 + jmul a 0 = jmul a (0 + 0) := (jmul_add a 0 0).symm
    _ = jmul a 0 := by rw [add_zero]
  simpa using h

theorem zero_jmul (a : J) : jmul 0 a = 0 := by
  rw [jmul_comm, jmul_zero]

theorem jmul_neg (a b : J) : jmul a (-b) = -jmul a b := by
  have h : jmul a b + jmul a (-b) = 0 := by
    calc jmul a b + jmul a (-b) = jmul a (b + (-b)) := (jmul_add a b (-b)).symm
    _ = jmul a 0 := by rw [add_neg_cancel]
    _ = 0 := jmul_zero a
  exact (neg_eq_of_add_eq_zero_right h).symm

theorem neg_jmul (a b : J) : jmul (-a) b = -jmul a b := by
  rw [jmul_comm, jmul_neg, jmul_comm]

theorem jmul_sub (a b c : J) : jmul a (b - c) = jmul a b - jmul a c := by
  rw [sub_eq_add_neg, jmul_add, jmul_neg, ← sub_eq_add_neg]

theorem sub_jmul (a b c : J) : jmul (a - b) c = jmul a c - jmul b c := by
  rw [jmul_comm, jmul_sub, jmul_comm c a, jmul_comm c b]

/-! ### Square and Powers -/

/-- The square of an element. -/
def jsq (a : J) : J := jmul a a

theorem jsq_def (a : J) : jsq a = jmul a a := rfl

/-- Jordan identity in terms of square. -/
theorem jordan_identity' (a b : J) : jmul (jmul a b) (jsq a) = jmul a (jmul b (jsq a)) :=
  jordan_identity a b

/-- Powers of an element. -/
def jpow (a : J) : ℕ → J
  | 0 => jone
  | n + 1 => jmul a (jpow a n)

@[simp]
theorem jpow_zero (a : J) : jpow a 0 = jone := rfl

theorem jpow_succ (a : J) (n : ℕ) : jpow a (n + 1) = jmul a (jpow a n) := rfl

@[simp]
theorem jpow_one (a : J) : jpow a 1 = a := by
  rw [jpow_succ, jpow_zero, jmul_jone]

theorem jpow_two (a : J) : jpow a 2 = jsq a := by
  rw [jpow_succ, jpow_one, jsq_def]

end JordanAlgebra
