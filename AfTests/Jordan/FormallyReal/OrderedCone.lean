/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.FormallyReal.Properties
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Positivity Cone in Formally Real Jordan Algebras

A formally real Jordan algebra has a natural positive cone: the set of sums of squares.
This cone induces a partial order making the algebra an ordered module.

## Main definitions

* `JordanAlgebra.positiveCone` - The cone of sums of squares
* `JordanAlgebra.PositiveElement` - Predicate for being a sum of squares

## Main results

* `positiveCone_pointed` - 0 is in the positive cone
* `positiveCone_salient` - Cone is salient in a formally real JA
-/

open Finset BigOperators

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-! ### Positive Elements -/

/-- An element is positive if it's a sum of squares. -/
def PositiveElement (a : J) : Prop :=
  ∃ (n : ℕ) (b : Fin n → J), a = ∑ i, jsq (b i)

/-- Zero is positive (empty sum). -/
theorem positiveElement_zero : PositiveElement (0 : J) :=
  ⟨0, Fin.elim0, by simp⟩

/-- Squares are positive. -/
theorem positiveElement_jsq (a : J) : PositiveElement (jsq a) :=
  ⟨1, fun _ => a, by simp⟩

/-- Sum of positive elements is positive. -/
theorem positiveElement_add {a b : J} (ha : PositiveElement a) (hb : PositiveElement b) :
    PositiveElement (a + b) := by
  obtain ⟨n, f, hf⟩ := ha
  obtain ⟨m, g, hg⟩ := hb
  refine ⟨n + m, Fin.addCases f g, ?_⟩
  rw [hf, hg, Fin.sum_univ_add]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> simp [Fin.addCases]

/-- Positive multiples of positive elements are positive. -/
theorem positiveElement_smul {a : J} (ha : PositiveElement a) {r : ℝ} (hr : 0 < r) :
    PositiveElement (r • a) := by
  obtain ⟨n, b, hb⟩ := ha
  refine ⟨n, fun i => Real.sqrt r • b i, ?_⟩
  rw [hb, smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [jsq_def, jmul_smul, smul_jmul, smul_smul]
  congr 1
  exact (Real.mul_self_sqrt (le_of_lt hr)).symm

/-! ### Positive Cone -/

/-- The positive cone in a Jordan algebra: sums of squares. -/
def positiveCone (J : Type*) [JordanAlgebra J] : ConvexCone ℝ J where
  carrier := {a | PositiveElement a}
  smul_mem' := by
    intro c hc x hx
    exact positiveElement_smul hx hc
  add_mem' := by
    intro x hx y hy
    exact positiveElement_add hx hy

theorem mem_positiveCone {a : J} : a ∈ positiveCone J ↔ PositiveElement a := Iff.rfl

/-- The positive cone is pointed (contains 0). -/
theorem positiveCone_pointed : (positiveCone J).Pointed :=
  positiveElement_zero

/-- In a formally real Jordan algebra, the positive cone is salient. -/
theorem positiveCone_salient [FormallyRealJordan J] : (positiveCone J).Salient := by
  intro a ha hane hneg
  -- a is a sum of squares, -a is a sum of squares, a ≠ 0
  -- Then Σ bᵢ² + Σ cⱼ² = a + (-a) = 0
  -- By formally real, each bᵢ = 0 and cⱼ = 0, so a = 0, contradiction
  obtain ⟨n, b, hb⟩ := ha
  obtain ⟨m, c, hc⟩ := hneg
  have hsum : (∑ i, jsq (b i)) + (∑ j, jsq (c j)) = 0 := by
    rw [← hb, ← hc, add_neg_cancel]
  -- Combine into one sum using Fin.addCases
  let bc : Fin (n + m) → J := Fin.addCases b c
  have hcombined : ∑ k : Fin (n + m), jsq (bc k) = 0 := by
    simp only [bc, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
    exact hsum
  -- By formally real property, each element is zero
  have hall := FormallyRealJordan.sum_sq_eq_zero (n + m) bc hcombined
  -- In particular, all b i = 0
  have hballzero : ∀ i, b i = 0 := fun i => by
    have := hall (Fin.castAdd m i)
    simp only [bc, Fin.addCases_left] at this
    exact this
  -- So a = Σ 0² = 0, contradicting hane
  have ha_zero : a = 0 := by
    rw [hb]
    simp only [hballzero, jsq_def, jmul_zero, Finset.sum_const_zero]
  exact hane ha_zero

end JordanAlgebra
