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

-- ============================================
-- GENERAL CASE GENERATOR ACTIONS ON CORE
-- ============================================

/-- The g₁ list has length at least 4 -/
theorem g₁_list_length_ge_4 (n k m : ℕ) :
    4 ≤ (g₁CoreList n k m ++ tailAList n k m).length := by
  simp [g₁CoreList, tailAList, List.finRange]

/-- The g₂ list has length at least 4 -/
theorem g₂_list_length_ge_4 (n k m : ℕ) :
    4 ≤ (g₂CoreList n k m ++ tailBList n k m).length := by
  simp [g₂CoreList, tailBList, List.finRange]

/-- The g₁ list at index 0 is ⟨0, _⟩ -/
theorem g₁_list_getElem_0 (n k m : ℕ) (h : 0 < (g₁CoreList n k m ++ tailAList n k m).length) :
    (g₁CoreList n k m ++ tailAList n k m)[0] = Fin.mk 0 (by omega) := by
  simp [g₁CoreList, tailAList]

/-- The g₁ list at index 1 is ⟨5, _⟩ -/
theorem g₁_list_getElem_1 (n k m : ℕ) (h : 1 < (g₁CoreList n k m ++ tailAList n k m).length) :
    (g₁CoreList n k m ++ tailAList n k m)[1] = Fin.mk 5 (by omega) := by
  simp [g₁CoreList, tailAList]

/-- The g₁ list at index 2 is ⟨3, _⟩ -/
theorem g₁_list_getElem_2 (n k m : ℕ) (h : 2 < (g₁CoreList n k m ++ tailAList n k m).length) :
    (g₁CoreList n k m ++ tailAList n k m)[2] = Fin.mk 3 (by omega) := by
  simp [g₁CoreList, tailAList]

/-- The g₁ list at index 3 is ⟨2, _⟩ -/
theorem g₁_list_getElem_3 (n k m : ℕ) (h : 3 < (g₁CoreList n k m ++ tailAList n k m).length) :
    (g₁CoreList n k m ++ tailAList n k m)[3] = Fin.mk 2 (by omega) := by
  simp [g₁CoreList, tailAList]

/-- The g₂ list at index 0 is ⟨1, _⟩ -/
theorem g₂_list_getElem_0 (n k m : ℕ) (h : 0 < (g₂CoreList n k m ++ tailBList n k m).length) :
    (g₂CoreList n k m ++ tailBList n k m)[0] = Fin.mk 1 (by omega) := by
  simp [g₂CoreList, tailBList]

/-- The g₂ list at index 1 is ⟨3, _⟩ -/
theorem g₂_list_getElem_1 (n k m : ℕ) (h : 1 < (g₂CoreList n k m ++ tailBList n k m).length) :
    (g₂CoreList n k m ++ tailBList n k m)[1] = Fin.mk 3 (by omega) := by
  simp [g₂CoreList, tailBList]

/-- The g₂ list at index 2 is ⟨4, _⟩ -/
theorem g₂_list_getElem_2 (n k m : ℕ) (h : 2 < (g₂CoreList n k m ++ tailBList n k m).length) :
    (g₂CoreList n k m ++ tailBList n k m)[2] = Fin.mk 4 (by omega) := by
  simp [g₂CoreList, tailBList]

/-- The g₂ list at index 3 is ⟨0, _⟩ -/
theorem g₂_list_getElem_3 (n k m : ℕ) (h : 3 < (g₂CoreList n k m ++ tailBList n k m).length) :
    (g₂CoreList n k m ++ tailBList n k m)[3] = Fin.mk 0 (by omega) := by
  simp [g₂CoreList, tailBList]

/-- g₁ maps 0 to 5 for any n, k, m -/
theorem g₁_general_action_0 (n k m : ℕ) :
    (g₁ n k m) (Fin.mk 0 (by omega)) = Fin.mk 5 (by omega) := by
  unfold g₁
  have hnd := g₁_list_nodup n k m
  have h0 : 0 < (g₁CoreList n k m ++ tailAList n k m).length := by simp [g₁CoreList, tailAList]
  have hlt : 0 + 1 < (g₁CoreList n k m ++ tailAList n k m).length := by simp [g₁CoreList, tailAList]
  conv_lhs => rw [← g₁_list_getElem_0 n k m h0]
  rw [List.formPerm_apply_lt_getElem _ hnd 0 hlt]
  exact g₁_list_getElem_1 n k m hlt

/-- g₁ maps 5 to 3 for any n, k, m -/
theorem g₁_general_action_5 (n k m : ℕ) :
    (g₁ n k m) (Fin.mk 5 (by omega)) = Fin.mk 3 (by omega) := by
  unfold g₁
  have hnd := g₁_list_nodup n k m
  have h1 : 1 < (g₁CoreList n k m ++ tailAList n k m).length := by simp [g₁CoreList, tailAList]
  have hlt : 1 + 1 < (g₁CoreList n k m ++ tailAList n k m).length := by simp [g₁CoreList, tailAList]
  conv_lhs => rw [← g₁_list_getElem_1 n k m h1]
  rw [List.formPerm_apply_lt_getElem _ hnd 1 hlt]
  exact g₁_list_getElem_2 n k m hlt

/-- g₁ maps 3 to 2 for any n, k, m -/
theorem g₁_general_action_3 (n k m : ℕ) :
    (g₁ n k m) (Fin.mk 3 (by omega)) = Fin.mk 2 (by omega) := by
  unfold g₁
  have hnd := g₁_list_nodup n k m
  have h2 : 2 < (g₁CoreList n k m ++ tailAList n k m).length := by simp [g₁CoreList, tailAList]
  have hlt : 2 + 1 < (g₁CoreList n k m ++ tailAList n k m).length := by simp [g₁CoreList, tailAList]
  conv_lhs => rw [← g₁_list_getElem_2 n k m h2]
  rw [List.formPerm_apply_lt_getElem _ hnd 2 hlt]
  exact g₁_list_getElem_3 n k m hlt

/-- g₂⁻¹ maps 0 to 4 for any n, k, m (since g₂ maps 4 to 0) -/
theorem g₂_inv_general_action_0 (n k m : ℕ) :
    (g₂ n k m)⁻¹ (Fin.mk 0 (by omega)) = Fin.mk 4 (by omega) := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  unfold g₂
  have hnd := g₂_list_nodup n k m
  have h2 : 2 < (g₂CoreList n k m ++ tailBList n k m).length := by simp [g₂CoreList, tailBList]
  have hlt : 2 + 1 < (g₂CoreList n k m ++ tailBList n k m).length := by simp [g₂CoreList, tailBList]
  conv_rhs => rw [← g₂_list_getElem_2 n k m h2]
  rw [List.formPerm_apply_lt_getElem _ hnd 2 hlt]
  exact g₂_list_getElem_3 n k m hlt

/-- g₂⁻¹ maps 4 to 3 for any n, k, m (since g₂ maps 3 to 4) -/
theorem g₂_inv_general_action_4 (n k m : ℕ) :
    (g₂ n k m)⁻¹ (Fin.mk 4 (by omega)) = Fin.mk 3 (by omega) := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  unfold g₂
  have hnd := g₂_list_nodup n k m
  have h1 : 1 < (g₂CoreList n k m ++ tailBList n k m).length := by simp [g₂CoreList, tailBList]
  have hlt : 1 + 1 < (g₂CoreList n k m ++ tailBList n k m).length := by simp [g₂CoreList, tailBList]
  conv_rhs => rw [← g₂_list_getElem_1 n k m h1]
  rw [List.formPerm_apply_lt_getElem _ hnd 1 hlt]
  exact g₂_list_getElem_2 n k m hlt

/-- g₂⁻¹ maps 3 to 1 for any n, k, m (since g₂ maps 1 to 3) -/
theorem g₂_inv_general_action_3 (n k m : ℕ) :
    (g₂ n k m)⁻¹ (Fin.mk 3 (by omega)) = Fin.mk 1 (by omega) := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  unfold g₂
  have hnd := g₂_list_nodup n k m
  have h0 : 0 < (g₂CoreList n k m ++ tailBList n k m).length := by simp [g₂CoreList, tailBList]
  have hlt : 0 + 1 < (g₂CoreList n k m ++ tailBList n k m).length := by simp [g₂CoreList, tailBList]
  conv_rhs => rw [← g₂_list_getElem_0 n k m h0]
  rw [List.formPerm_apply_lt_getElem _ hnd 0 hlt]
  exact g₂_list_getElem_1 n k m hlt

-- ============================================
-- REACHING CORE ELEMENTS FROM 0 (GENERAL CASE)
-- ============================================

/-- From 0, reach any core element using g₁, g₂, g₂⁻¹ -/
theorem reach_from_0_general (n k m : ℕ) (x : Fin 6) :
    ∃ h : H n k m, h.val (Fin.mk 0 (by omega)) = Fin.mk x.val (by omega) := by
  fin_cases x
  · -- x = 0: identity
    exact ⟨1, rfl⟩
  · -- x = 1: g₂⁻³(0)
    use ⟨(g₂ n k m)⁻¹ ^ 3, Subgroup.pow_mem _ (Subgroup.inv_mem _ (g₂_mem_H n k m)) 3⟩
    simp only [Equiv.Perm.coe_pow, Function.iterate_succ,
      Function.comp_apply, Function.iterate_zero, id_eq]
    rw [g₂_inv_general_action_0, g₂_inv_general_action_4, g₂_inv_general_action_3]
  · -- x = 2: g₁³(0)
    use ⟨(g₁ n k m) ^ 3, Subgroup.pow_mem _ (g₁_mem_H n k m) 3⟩
    simp only [Equiv.Perm.coe_pow, Function.iterate_succ,
      Function.comp_apply, Function.iterate_zero, id_eq]
    rw [g₁_general_action_0, g₁_general_action_5, g₁_general_action_3]
  · -- x = 3: g₁²(0)
    use ⟨(g₁ n k m) ^ 2, Subgroup.pow_mem _ (g₁_mem_H n k m) 2⟩
    simp only [Equiv.Perm.coe_pow, Function.iterate_succ,
      Function.comp_apply, Function.iterate_zero, id_eq]
    rw [g₁_general_action_0, g₁_general_action_5]
  · -- x = 4: g₂⁻¹(0)
    use ⟨(g₂ n k m)⁻¹, Subgroup.inv_mem _ (g₂_mem_H n k m)⟩
    exact g₂_inv_general_action_0 n k m
  · -- x = 5: g₁(0)
    use ⟨g₁ n k m, g₁_mem_H n k m⟩
    exact g₁_general_action_0 n k m

/-- The Core vertices {0,1,2,3,4,5} are connected in the support graph.
    This follows from the base case transitivity. -/
theorem core_connected (n k m : ℕ) :
    ∀ x y : Fin 6, ∃ h : H n k m, (h.val (Fin.castLE (by omega : 6 ≤ 6 + n + k + m) x) =
      Fin.castLE (by omega : 6 ≤ 6 + n + k + m) y) := by
  intro x y
  -- Get h₁ with h₁(0) = x and h₂ with h₂(0) = y
  obtain ⟨h₁, hh₁⟩ := reach_from_0_general n k m x
  obtain ⟨h₂, hh₂⟩ := reach_from_0_general n k m y
  -- Then h₂ * h₁⁻¹ maps x to y
  use h₂ * h₁⁻¹
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.coe_mul, Function.comp_apply]
  -- h₁⁻¹(x) = 0 since h₁(0) = x
  have hinv : h₁.val⁻¹ (Fin.mk x.val (by omega)) = Fin.mk 0 (by omega) := by
    rw [← hh₁]
    simp only [Equiv.Perm.inv_apply_self]
  -- castLE x has val = x.val, so Fin.mk x.val _ = castLE x
  have hcast_x : Fin.castLE (by omega : 6 ≤ 6 + n + k + m) x = Fin.mk x.val (by omega) := rfl
  have hcast_y : Fin.castLE (by omega : 6 ≤ 6 + n + k + m) y = Fin.mk y.val (by omega) := rfl
  rw [hcast_x, hcast_y]
  rw [hinv, hh₂]

/-- Element 6+i is at index 4+i in the g₁ list -/
theorem g₁_list_getElem_tail (n k m : ℕ) (i : Fin n) :
    (g₁CoreList n k m ++ tailAList n k m)[4 + i.val]'(by simp [g₁CoreList, tailAList]; omega) =
    ⟨6 + i.val, by omega⟩ := by
  have h1 : (g₁CoreList n k m).length = 4 := by simp [g₁CoreList]
  have h2 : (g₁CoreList n k m).length ≤ 4 + i.val := by omega
  rw [List.getElem_append_right h2]
  simp only [tailAList, h1, Nat.add_sub_cancel_left]
  rw [List.getElem_map]
  simp only [List.getElem_finRange, Fin.cast_val_eq_self]
  rfl

/-- Each tail vertex in the a-tail (from g₁) connects to the Core.
    The a-tail elements are at indices 6, 7, ..., 5+n.
    g₁ cycles through [0, 5, 3, 2, 6, 7, ..., 5+n], so
    g₁^(n-i) maps 6+i to 0 (in the Core). -/
theorem a_tail_connected_to_core (n k m : ℕ) (i : Fin n) :
    ∃ h : H n k m, (h.val ⟨6 + i.val, by omega⟩ : Omega n k m).val < 6 := by
  -- Witness: g₁^(n - i.val) maps 6+i to 0
  use ⟨(g₁ n k m) ^ (n - i.val), Subgroup.pow_mem _ (g₁_mem_H n k m) _⟩
  -- The g₁ list and its properties
  let L := g₁CoreList n k m ++ tailAList n k m
  have hnd : L.Nodup := g₁_list_nodup n k m
  have hlen : L.length = 4 + n := g₁_cycle_length n k m
  -- Element 6+i is at index 4+i
  have hidx : 4 + i.val < L.length := by simp [L, g₁CoreList, tailAList]; omega
  have helem : L[4 + i.val] = ⟨6 + i.val, by omega⟩ := g₁_list_getElem_tail n k m i
  -- Element 0 is at index 0
  have hidx0 : 0 < L.length := by simp [L, g₁CoreList, tailAList]
  have helem0 : L[0] = ⟨0, by omega⟩ := by simp [L, g₁CoreList]
  -- Compute: g₁^(n-i.val) applied to element at index 4+i gives element at index 0
  have hmod : (4 + i.val + (n - i.val)) % (4 + n) = 0 := by
    have hi : i.val < n := i.isLt
    have heq : 4 + i.val + (n - i.val) = 4 + n := by omega
    rw [heq, Nat.mod_self]
  -- Apply formPerm_pow_apply_getElem
  unfold g₁
  conv_lhs => rw [← helem]
  rw [List.formPerm_pow_apply_getElem L hnd (n - i.val) (4 + i.val) hidx]
  simp only [hlen, hmod, helem0]
  omega

/-- Element 6+n+j is at index 4+j in the g₂ list -/
theorem g₂_list_getElem_tail (n k m : ℕ) (j : Fin k) :
    (g₂CoreList n k m ++ tailBList n k m)[4 + j.val]'(by simp [g₂CoreList, tailBList]; omega) =
    ⟨6 + n + j.val, by omega⟩ := by
  have h1 : (g₂CoreList n k m).length = 4 := by simp [g₂CoreList]
  have h2 : (g₂CoreList n k m).length ≤ 4 + j.val := by omega
  rw [List.getElem_append_right h2]
  simp only [tailBList, h1, Nat.add_sub_cancel_left]
  rw [List.getElem_map]
  simp only [List.getElem_finRange, Fin.cast_val_eq_self]
  rfl

/-- Each tail vertex in the b-tail (from g₂) connects to the Core.
    The b-tail elements are at indices 6+n, 6+n+1, ..., 5+n+k.
    g₂ cycles through [1, 3, 4, 0, 6+n, ...], so
    g₂^(k-j) maps 6+n+j to 1 (in the Core). -/
theorem b_tail_connected_to_core (n k m : ℕ) (j : Fin k) :
    ∃ h : H n k m, (h.val ⟨6 + n + j.val, by omega⟩ : Omega n k m).val < 6 := by
  -- Witness: g₂^(k - j.val) maps 6+n+j to 1
  use ⟨(g₂ n k m) ^ (k - j.val), Subgroup.pow_mem _ (g₂_mem_H n k m) _⟩
  -- The g₂ list and its properties
  let L := g₂CoreList n k m ++ tailBList n k m
  have hnd : L.Nodup := g₂_list_nodup n k m
  have hlen : L.length = 4 + k := g₂_cycle_length n k m
  -- Element 6+n+j is at index 4+j
  have hidx : 4 + j.val < L.length := by simp [L, g₂CoreList, tailBList]; omega
  have helem : L[4 + j.val] = ⟨6 + n + j.val, by omega⟩ := g₂_list_getElem_tail n k m j
  -- Element 1 is at index 0
  have hidx0 : 0 < L.length := by simp [L, g₂CoreList, tailBList]
  have helem0 : L[0] = ⟨1, by omega⟩ := by simp [L, g₂CoreList]
  -- Compute: g₂^(k-j.val) applied to element at index 4+j gives element at index 0
  have hmod : (4 + j.val + (k - j.val)) % (4 + k) = 0 := by
    have hj : j.val < k := j.isLt
    have heq : 4 + j.val + (k - j.val) = 4 + k := by omega
    rw [heq, Nat.mod_self]
  -- Apply formPerm_pow_apply_getElem
  unfold g₂
  conv_lhs => rw [← helem]
  rw [List.formPerm_pow_apply_getElem L hnd (k - j.val) (4 + j.val) hidx]
  simp only [hlen, hmod, helem0]
  omega

/-- Element 6+n+k+l is at index 4+l in the g₃ list -/
theorem g₃_list_getElem_tail (n k m : ℕ) (l : Fin m) :
    (g₃CoreList n k m ++ tailCList n k m)[4 + l.val]'(by simp [g₃CoreList, tailCList]; omega) =
    ⟨6 + n + k + l.val, by omega⟩ := by
  have h1 : (g₃CoreList n k m).length = 4 := by simp [g₃CoreList]
  have h2 : (g₃CoreList n k m).length ≤ 4 + l.val := by omega
  rw [List.getElem_append_right h2]
  simp only [tailCList, h1, Nat.add_sub_cancel_left]
  rw [List.getElem_map]
  simp only [List.getElem_finRange, Fin.cast_val_eq_self]
  rfl

/-- Each tail vertex in the c-tail (from g₃) connects to the Core.
    The c-tail elements are at indices 6+n+k, ..., 5+n+k+m.
    g₃ cycles through [2, 4, 5, 1, 6+n+k, ...], so
    g₃^(m-l) maps 6+n+k+l to 2 (in the Core). -/
theorem c_tail_connected_to_core (n k m : ℕ) (l : Fin m) :
    ∃ h : H n k m, (h.val ⟨6 + n + k + l.val, by omega⟩ : Omega n k m).val < 6 := by
  -- Witness: g₃^(m - l.val) maps 6+n+k+l to 2
  use ⟨(g₃ n k m) ^ (m - l.val), Subgroup.pow_mem _ (g₃_mem_H n k m) _⟩
  -- The g₃ list and its properties
  let L := g₃CoreList n k m ++ tailCList n k m
  have hnd : L.Nodup := g₃_list_nodup n k m
  have hlen : L.length = 4 + m := g₃_cycle_length n k m
  -- Element 6+n+k+l is at index 4+l
  have hidx : 4 + l.val < L.length := by simp [L, g₃CoreList, tailCList]; omega
  have helem : L[4 + l.val] = ⟨6 + n + k + l.val, by omega⟩ := g₃_list_getElem_tail n k m l
  -- Element 2 is at index 0
  have hidx0 : 0 < L.length := by simp [L, g₃CoreList, tailCList]
  have helem0 : L[0] = ⟨2, by omega⟩ := by simp [L, g₃CoreList]
  -- Compute: g₃^(m-l.val) applied to element at index 4+l gives element at index 0
  have hmod : (4 + l.val + (m - l.val)) % (4 + m) = 0 := by
    have hl : l.val < m := l.isLt
    have heq : 4 + l.val + (m - l.val) = 4 + m := by omega
    rw [heq, Nat.mod_self]
  -- Apply formPerm_pow_apply_getElem
  unfold g₃
  conv_lhs => rw [← helem]
  rw [List.formPerm_pow_apply_getElem L hnd (m - l.val) (4 + l.val) hidx]
  simp only [hlen, hmod, helem0]
  omega

/-- Any element of Omega can be mapped to a core element -/
theorem H_reaches_core (n k m : ℕ) (x : Omega n k m) :
    ∃ h : H n k m, (h.val x).val < 6 := by
  by_cases hx : x.val < 6
  · -- x is already in core, use identity
    exact ⟨1, by simp [hx]⟩
  · push_neg at hx
    -- x is in some tail
    by_cases hn : x.val < 6 + n
    · -- x is in a-tail: x.val = 6 + i for some i < n
      have hi : x.val - 6 < n := by omega
      obtain ⟨h, hh⟩ := a_tail_connected_to_core n k m ⟨x.val - 6, hi⟩
      refine ⟨h, ?_⟩
      have hval : 6 + (x.val - 6) = x.val := Nat.add_sub_cancel' hx
      have heq : (⟨6 + (x.val - 6), by have := x.isLt; omega⟩ : Omega n k m) = x := by
        ext; exact hval
      rw [← heq]; exact hh
    · push_neg at hn
      by_cases hk : x.val < 6 + n + k
      · -- x is in b-tail: x.val = 6 + n + j for some j < k
        have hj : x.val - 6 - n < k := by omega
        obtain ⟨h, hh⟩ := b_tail_connected_to_core n k m ⟨x.val - 6 - n, hj⟩
        refine ⟨h, ?_⟩
        have hval : 6 + n + (x.val - 6 - n) = x.val := by omega
        have heq : (⟨6 + n + (x.val - 6 - n), by have := x.isLt; omega⟩ : Omega n k m) = x := by
          ext; exact hval
        rw [← heq]; exact hh
      · push_neg at hk
        -- x is in c-tail: x.val = 6 + n + k + l for some l < m
        have hl : x.val - 6 - n - k < m := by have := x.isLt; omega
        obtain ⟨h, hh⟩ := c_tail_connected_to_core n k m ⟨x.val - 6 - n - k, hl⟩
        refine ⟨h, ?_⟩
        have hval : 6 + n + k + (x.val - 6 - n - k) = x.val := by omega
        have heq : (⟨6 + n + k + (x.val - 6 - n - k), by have := x.isLt; omega⟩ : Omega n k m) = x := by
          ext; exact hval
        rw [← heq]; exact hh

/-- There is only one orbit under the action of H -/
theorem H_single_orbit (n k m : ℕ) :
    ∀ x y : Omega n k m, ∃ h : H n k m, h.val x = y := by
  intro x y
  -- Get h₁ mapping x to some core element c₁
  obtain ⟨h₁, hh₁⟩ := H_reaches_core n k m x
  -- Get h₂ mapping y to some core element c₂
  obtain ⟨h₂, hh₂⟩ := H_reaches_core n k m y
  -- Get elements as Fin 6
  let c₁ : Fin 6 := ⟨(h₁.val x).val, hh₁⟩
  let c₂ : Fin 6 := ⟨(h₂.val y).val, hh₂⟩
  -- Use core_connected to get h₃ mapping c₁ to c₂
  obtain ⟨h₃, hh₃⟩ := core_connected n k m c₁ c₂
  -- Compose: h₂⁻¹ * h₃ * h₁ maps x to y
  use h₂⁻¹ * h₃ * h₁
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.coe_mul, Function.comp_apply]
  -- h₃(h₁(x)) = h₂(y) since h₃(c₁) = c₂
  have heq : h₃.val (h₁.val x) = h₂.val y := by
    have hh₃' := hh₃
    -- Both sides have val < 6+n+k+m and we need to show they're equal
    ext
    have lhs_val : (h₃.val (h₁.val x)).val = (Fin.castLE (by omega : 6 ≤ 6 + n + k + m) c₂).val := by
      have : h₃.val (Fin.castLE (by omega : 6 ≤ 6 + n + k + m) c₁) =
             Fin.castLE (by omega : 6 ≤ 6 + n + k + m) c₂ := hh₃'
      have heq1 : (Fin.castLE (by omega : 6 ≤ 6 + n + k + m) c₁ : Omega n k m) = h₁.val x := by
        ext; simp [c₁]
      rw [← heq1, this]
    have rhs_val : (h₂.val y).val = (Fin.castLE (by omega : 6 ≤ 6 + n + k + m) c₂).val := by
      simp [c₂]
    rw [lhs_val, rhs_val]
  rw [heq]
  exact Equiv.Perm.inv_apply_self (h₂.val) y

/-- The group H acts transitively on Omega.
    Proof: The support graph is connected (Core is connected and all tails
    connect to Core), hence H acts transitively. -/
theorem H_isPretransitive (n k m : ℕ) : MulAction.IsPretransitive (H n k m) (Omega n k m) := by
  constructor
  intro x y
  exact H_single_orbit n k m x y

end AfTests.Transitivity
