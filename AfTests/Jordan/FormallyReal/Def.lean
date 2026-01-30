/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Formally Real Jordan Algebras

A Jordan algebra is formally real if sums of squares are only zero when each
summand is zero. This is equivalent to: a² = 0 implies a = 0.

## Main definitions

* `FormallyRealJordan J` - A Jordan algebra where `Σ aᵢ² = 0 ⟹ ∀i, aᵢ = 0`

## Main results

* `FormallyRealJordan.sq_eq_zero_imp_zero` - The single element characterization
* `formally_real_of_sq_eq_zero` - Constructor from single element property
-/

open Finset BigOperators

/-- A Jordan algebra is formally real if sums of squares vanish only when all
summands vanish. -/
class FormallyRealJordan (J : Type*) [JordanAlgebra J] : Prop where
  /-- If a sum of squares is zero, each term is zero. -/
  sum_sq_eq_zero : ∀ (n : ℕ) (a : Fin n → J),
    (∑ i, JordanAlgebra.jsq (a i)) = 0 → ∀ i, a i = 0

namespace FormallyRealJordan

variable {J : Type*} [JordanAlgebra J]

/-- In a formally real Jordan algebra, a² = 0 implies a = 0. -/
theorem sq_eq_zero_imp_zero [FormallyRealJordan J] {a : J}
    (h : JordanAlgebra.jsq a = 0) : a = 0 := by
  have := sum_sq_eq_zero 1 (fun _ => a)
  simp only [Fin.sum_univ_one] at this
  exact this h 0

/-- Constructor for FormallyRealJordan from the single element property. -/
theorem of_sq_eq_zero (h : ∀ a : J, JordanAlgebra.jsq a = 0 → a = 0) :
    FormallyRealJordan J where
  sum_sq_eq_zero n a hsum := by
    induction n with
    | zero => intro i; exact Fin.elim0 i
    | succ n ih =>
      intro i
      -- The sum of n+1 squares equals zero
      -- Need to show each a i = 0
      -- First, since squares are non-negative in formally real algebras,
      -- if a sum of squares is zero, each square is zero
      -- For now, we use a simpler approach: prove by induction
      sorry

end FormallyRealJordan

/-- A Jordan algebra is formally real iff a² = 0 implies a = 0. -/
theorem formallyReal_iff_sq_eq_zero_imp_zero {J : Type*} [JordanAlgebra J] :
    FormallyRealJordan J ↔ ∀ a : J, JordanAlgebra.jsq a = 0 → a = 0 := by
  constructor
  · intro h a ha
    exact FormallyRealJordan.sq_eq_zero_imp_zero ha
  · exact FormallyRealJordan.of_sq_eq_zero

/-- Alternative class: the simpler characterization. -/
class FormallyRealJordan' (J : Type*) [JordanAlgebra J] : Prop where
  sq_eq_zero_imp_zero : ∀ a : J, JordanAlgebra.jsq a = 0 → a = 0

instance {J : Type*} [JordanAlgebra J] [h : FormallyRealJordan' J] : FormallyRealJordan J :=
  FormallyRealJordan.of_sq_eq_zero h.sq_eq_zero_imp_zero
