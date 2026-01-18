/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Core
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic.FinCases

/-!
# Lemma 5: Transitivity of H on Omega

The group H = ⟨g₁, g₂, g₃⟩ acts transitively on Ω = Fin(6+n+k+m).

## Main Results

* `H_isPretransitive` - H acts transitively on Omega

## Proof Strategy

The proof proceeds by showing the support graph Γ is connected:
1. Identify edges from each generator (consecutive elements in cycles)
2. Show the Core {0,1,2,3,4,5} forms a connected subgraph
3. Show each tail vertex connects to the Core
4. Conclude Γ is connected, hence H acts transitively

## Reference

See `examples/lemmas/lemma05_transitivity.md` for the natural language proof.
-/

namespace AfTests.Transitivity

open Equiv Equiv.Perm

/-! ### Base Case: n = k = m = 0

For the base case, H₆ acts transitively on Fin 6.
The generators are:
- g₁ = (0 5 3 2): 0→5→3→2→0
- g₂ = (1 3 4 0): 1→3→4→0→1, so 0→1
- g₃ = (2 4 5 1): 2→4→5→1→2

From element 0, we can reach:
- 1 via g₂(0) = 1
- 2 via g₁³(0) = 2
- 3 via g₁²(0) = 3
- 4 via g₂³(0) = 4
- 5 via g₁(0) = 5
-/

-- ============================================
-- BASE CASE GENERATOR ACTIONS
-- ============================================

/-- g₁(0) = 5 -/
theorem g₁_action_0 : (g₁ 0 0 0 : Perm (Fin 6)) 0 = 5 := by native_decide

/-- g₁(5) = 3 -/
theorem g₁_action_5 : (g₁ 0 0 0 : Perm (Fin 6)) 5 = 3 := by native_decide

/-- g₁(3) = 2 -/
theorem g₁_action_3 : (g₁ 0 0 0 : Perm (Fin 6)) 3 = 2 := by native_decide

/-- g₂(0) = 1 -/
theorem g₂_action_0 : (g₂ 0 0 0 : Perm (Fin 6)) 0 = 1 := by native_decide

/-- g₂(1) = 3 -/
theorem g₂_action_1 : (g₂ 0 0 0 : Perm (Fin 6)) 1 = 3 := by native_decide

/-- g₂(3) = 4 -/
theorem g₂_action_3 : (g₂ 0 0 0 : Perm (Fin 6)) 3 = 4 := by native_decide

-- ============================================
-- REACHING EACH ELEMENT FROM 0
-- ============================================

/-- From 0, we can reach 1 using g₂ -/
theorem reach_1_from_0 : ∃ h : H₆, h.val 0 = 1 :=
  ⟨⟨g₂ 0 0 0, g₂_mem_H 0 0 0⟩, g₂_action_0⟩

/-- From 0, we can reach 5 using g₁ -/
theorem reach_5_from_0 : ∃ h : H₆, h.val 0 = 5 :=
  ⟨⟨g₁ 0 0 0, g₁_mem_H 0 0 0⟩, g₁_action_0⟩

/-- From 0, we can reach 3 using g₁² -/
theorem reach_3_from_0 : ∃ h : H₆, h.val 0 = 3 := by
  use ⟨(g₁ 0 0 0) ^ 2, Subgroup.pow_mem _ (g₁_mem_H 0 0 0) 2⟩
  native_decide

/-- From 0, we can reach 2 using g₁³ -/
theorem reach_2_from_0 : ∃ h : H₆, h.val 0 = 2 := by
  use ⟨(g₁ 0 0 0) ^ 3, Subgroup.pow_mem _ (g₁_mem_H 0 0 0) 3⟩
  native_decide

/-- From 0, we can reach 4 using g₂³ -/
theorem reach_4_from_0 : ∃ h : H₆, h.val 0 = 4 := by
  use ⟨(g₂ 0 0 0) ^ 3, Subgroup.pow_mem _ (g₂_mem_H 0 0 0) 3⟩
  native_decide

-- ============================================
-- BASE CASE TRANSITIVITY
-- ============================================

/-- In the base case, every element of Fin 6 is reachable from 0 under H₆. -/
theorem H₆_orbit_of_zero : ∀ x : Fin 6, ∃ h : H₆, h.val 0 = x := by
  intro x
  fin_cases x
  · exact ⟨1, rfl⟩  -- 0: identity
  · exact reach_1_from_0
  · exact reach_2_from_0
  · exact reach_3_from_0
  · exact reach_4_from_0
  · exact reach_5_from_0

/-- For any two elements x, y in Fin 6, there exists h ∈ H₆ with h(x) = y -/
theorem H₆_orbit_exists (x y : Fin 6) : ∃ h : H₆, h.val x = y := by
  -- First get h₁ with h₁(0) = x, and h₂ with h₂(0) = y
  obtain ⟨h₁, hh₁⟩ := H₆_orbit_of_zero x
  obtain ⟨h₂, hh₂⟩ := H₆_orbit_of_zero y
  -- Then h₂ * h₁⁻¹ takes x to y
  use h₂ * h₁⁻¹
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.coe_mul]
  -- h₁⁻¹(x) = 0 since h₁(0) = x
  have hinv : h₁.val⁻¹ x = 0 := by
    rw [← hh₁]
    simp only [Perm.inv_apply_self]
  simp only [Function.comp_apply, hinv, hh₂]

/-- The base case group H₆ acts transitively on Fin 6 -/
theorem H₆_isPretransitive : MulAction.IsPretransitive H₆ (Fin 6) := by
  constructor
  intro x y
  obtain ⟨h, hh⟩ := H₆_orbit_exists x y
  exact ⟨h, hh⟩

/-! ### General Case

For the general case with arbitrary n, k, m, we use the support graph argument.
The support graph has vertices = Omega and edges = {(x, g(x)) : g generator, x moved}.
-/

/-- The Core vertices {0,1,2,3,4,5} are connected in the support graph.
    This follows from the base case transitivity. -/
theorem core_connected (n k m : ℕ) :
    ∀ x y : Fin 6, ∃ h : H n k m, (h.val (Fin.castLE (by omega : 6 ≤ 6 + n + k + m) x) =
      Fin.castLE (by omega : 6 ≤ 6 + n + k + m) y) := by
  sorry -- Requires showing generators act the same on Core

/-- Each tail vertex in the a-tail (from g₁) connects to the Core.
    The a-tail elements are at indices 6, 7, ..., 5+n.
    g₁ cycles through [0, 5, 3, 2, 6, 7, ..., 5+n], so
    g₁⁻¹ maps 6 to 2 (in the Core). -/
theorem a_tail_connected_to_core (n k m : ℕ) (i : Fin n) :
    ∃ h : H n k m, (h.val ⟨6 + i.val, by omega⟩ : Omega n k m).val < 6 := by
  sorry -- Requires showing g₁⁻^(i+1) maps 6+i to Core

/-- Each tail vertex in the b-tail (from g₂) connects to the Core.
    The b-tail elements are at indices 6+n, 6+n+1, ..., 5+n+k.
    g₂ cycles through [1, 3, 4, 0, 6+n, ...], so
    g₂⁻¹ maps 6+n to 0 (in the Core). -/
theorem b_tail_connected_to_core (n k m : ℕ) (j : Fin k) :
    ∃ h : H n k m, (h.val ⟨6 + n + j.val, by omega⟩ : Omega n k m).val < 6 := by
  sorry -- Requires showing g₂⁻^(j+1) maps 6+n+j to Core

/-- Each tail vertex in the c-tail (from g₃) connects to the Core.
    The c-tail elements are at indices 6+n+k, ..., 5+n+k+m.
    g₃ cycles through [2, 4, 5, 1, 6+n+k, ...], so
    g₃⁻¹ maps 6+n+k to 1 (in the Core). -/
theorem c_tail_connected_to_core (n k m : ℕ) (l : Fin m) :
    ∃ h : H n k m, (h.val ⟨6 + n + k + l.val, by omega⟩ : Omega n k m).val < 6 := by
  sorry -- Requires showing g₃⁻^(l+1) maps 6+n+k+l to Core

/-- The group H acts transitively on Omega.
    Proof: The support graph is connected (Core is connected and all tails
    connect to Core), hence H acts transitively. -/
theorem H_isPretransitive (n k m : ℕ) : MulAction.IsPretransitive (H n k m) (Omega n k m) := by
  sorry -- Combines core_connected with tail connections

/-! ### Orbit Equivalence

Alternative formulation using orbits.
-/

/-- There is only one orbit under the action of H -/
theorem H_single_orbit (n k m : ℕ) :
    ∀ x y : Omega n k m, ∃ h : H n k m, h.val x = y := by
  sorry -- Equivalent to H_isPretransitive

end AfTests.Transitivity
