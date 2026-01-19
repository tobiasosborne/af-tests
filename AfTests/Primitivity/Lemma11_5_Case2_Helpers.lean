/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Core
import AfTests.Primitivity.Lemma11_5_CycleSupport
import AfTests.Primitivity.Lemma11_5_SupportCover
import AfTests.Primitivity.Lemma11_5_FixedPoints
import AfTests.Primitivity.Lemma11_3
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# Lemma 11.5 Case 2: Helper Lemmas

Helper lemmas showing B subset tailA and g1(a1) computation for Case 2 analysis.
-/

open Equiv Equiv.Perm Set
variable {n k m : ℕ}

theorem elem5_in_support_g₃ : (⟨5, by omega⟩ : Omega n k m) ∈ (g₃ n k m).support := by
  have hNodup := g₃_list_nodup n k m
  have hNotSingleton : ∀ x, g₃CoreList n k m ++ tailCList n k m ≠ [x] := by
    intro x h
    have : (g₃CoreList n k m ++ tailCList n k m).length = 1 := by rw [h]; simp
    have := g₃_cycle_length n k m; omega
  rw [g₃, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₃CoreList, List.mem_cons]; tauto

theorem elem3_in_support_g₂' : (⟨3, by omega⟩ : Omega n k m) ∈ (g₂ n k m).support := by
  have hNodup := g₂_list_nodup n k m
  have hNotSingleton : ∀ x, g₂CoreList n k m ++ tailBList n k m ≠ [x] := by
    intro x h
    have : (g₂CoreList n k m ++ tailBList n k m).length = 1 := by rw [h]; simp
    have := g₂_cycle_length n k m; omega
  rw [g₂, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₂CoreList, List.mem_cons]; tauto

theorem core_in_support_g₂_or_g₃ (x : Omega n k m) (hCore : isCore x) :
    x ∈ (g₂ n k m).support ∨ x ∈ (g₃ n k m).support := by
  obtain ⟨v, hv⟩ := x
  simp only [isCore] at hCore
  have : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
  · left; convert elem0_in_support_g₂ (n := n) (k := k) (m := m)
  · left; convert elem1_in_support_g₂ (n := n) (k := k) (m := m)
  · right; convert elem2_in_support_g₃ (n := n) (k := k) (m := m)
  · left; convert elem3_in_support_g₂' (n := n) (k := k) (m := m)
  · left; convert elem4_in_support_g₂ (n := n) (k := k) (m := m)
  · right; convert elem5_in_support_g₃ (n := n) (k := k) (m := m)

theorem case2_B_subset_tailA (B : Set (Omega n k m))
    (hDisj₂ : Disjoint (↑(g₂ n k m).support) B)
    (hDisj₃ : Disjoint (↑(g₃ n k m).support) B) :
    ∀ x ∈ B, isTailA x := by
  intro x hx
  rcases Omega.partition x with hCore | hA | hB | hC
  · rcases core_in_support_g₂_or_g₃ x hCore with h2 | h3
    · exact (Set.disjoint_iff.mp hDisj₂ ⟨h2, hx⟩).elim
    · exact (Set.disjoint_iff.mp hDisj₃ ⟨h3, hx⟩).elim
  · exact hA
  · have h_in_supp : x ∈ (g₂ n k m).support := by
      simp only [isTailB] at hB; obtain ⟨hLo, hHi⟩ := hB
      have hi : x.val - 6 - n < k := by have := x.isLt; omega
      convert tailB_in_support_g₂ (⟨x.val - 6 - n, hi⟩ : Fin k) using 1
      simp only [Fin.ext_iff]; omega
    exact (Set.disjoint_iff.mp hDisj₂ ⟨h_in_supp, hx⟩).elim
  · have h_in_supp : x ∈ (g₃ n k m).support := by
      simp only [isTailC] at hC; obtain ⟨hLo, hHi⟩ := hC
      have hi : x.val - 6 - n - k < m := by have := x.isLt; omega
      convert tailC_in_support_g₃ (⟨x.val - 6 - n - k, hi⟩ : Fin m) using 1
      simp only [Fin.ext_iff]; omega
    exact (Set.disjoint_iff.mp hDisj₃ ⟨h_in_supp, hx⟩).elim

lemma g₁_list_length' (n k m : ℕ) :
    (g₁CoreList n k m ++ tailAList n k m).length = 4 + n := by
  simp only [g₁CoreList, tailAList, List.length_append, List.length_cons, List.length_nil,
    List.length_map, List.length_finRange]

lemma g₁_list_idx_4 (n k m : ℕ) (hn : n ≥ 1) :
    (g₁CoreList n k m ++ tailAList n k m)[4]'(by rw [g₁_list_length']; omega) =
    (⟨6, by omega⟩ : Omega n k m) := by
  have h2 : (g₁CoreList n k m).length ≤ 4 := by simp [g₁CoreList]
  rw [List.getElem_append_right h2]
  simp only [g₁CoreList, List.length_cons, List.length_nil, Nat.sub_self]
  simp only [tailAList, List.getElem_map, List.getElem_finRange]; rfl

lemma g₁_list_idx_5 (n k m : ℕ) (hn : n ≥ 2) :
    (g₁CoreList n k m ++ tailAList n k m)[5]'(by rw [g₁_list_length']; omega) =
    (⟨7, by omega⟩ : Omega n k m) := by
  have h2 : (g₁CoreList n k m).length ≤ 5 := by simp [g₁CoreList]
  rw [List.getElem_append_right h2]
  simp only [g₁CoreList, List.length_cons, List.length_nil]
  simp only [tailAList, List.getElem_map, List.getElem_finRange]; rfl

/-- For n >= 2, g₁(a₁) = element 7 -/
theorem g₁_a₁_eq_7 (hn2 : n ≥ 2) :
    g₁ n k m (⟨6, by omega⟩ : Omega n k m) = ⟨7, by omega⟩ := by
  unfold g₁
  have hNodup := g₁_list_nodup n k m
  have h_len := g₁_list_length' n k m
  have h_4_lt : 4 < (g₁CoreList n k m ++ tailAList n k m).length := by omega
  have h_idx4 := g₁_list_idx_4 n k m (by omega : n ≥ 1)
  rw [← h_idx4, List.formPerm_apply_getElem _ hNodup 4 h_4_lt]
  have h_5_lt' : 5 < 4 + n := by omega
  have h_mod_eq : (4 + 1) % (4 + n) = 5 := Nat.mod_eq_of_lt h_5_lt'
  simp only [h_len, h_mod_eq]; exact g₁_list_idx_5 n k m hn2

lemma g₁_a₁_eq_elem7 (hn : n ≥ 1) (hn2 : n ≥ 2) :
    g₁ n k m (a₁ n k m hn) = (⟨7, by omega⟩ : Omega n k m) := by
  unfold a₁; exact g₁_a₁_eq_7 hn2

set_option maxHeartbeats 400000 in
-- Suppressing style warning - proof needs computational effort for case analysis
set_option linter.style.maxHeartbeats false in
/-- In Case 2, |B| ≤ 1. Uses full g₁(B) ∩ B = ∅ disjointness.

**BUG**: This theorem as stated is FALSE for n ≥ 3. Counterexample: B = {6, 8} for n = 3.
The hypotheses are satisfied but |B| = 2. The issue is that g₁(B) ∩ B = ∅ does not imply
g₁²(B) ∩ B = ∅. For B = {6, 8}: g₁²(B) = {8, 5}, and {8, 5} ∩ {6, 8} = {8} ≠ ∅.

The correct approach (per AF Node 1.9.5) requires B to be a proper block in an H-invariant
block system, which enforces that the full orbit of B under g₁ consists of pairwise disjoint
sets. This additional constraint rules out the counterexample.

See issue af-tests-5jc for tracking this redesign. -/
theorem case2_B_ncard_le_one (hn : n ≥ 1) (B : Set (Omega n k m))
    (hDisj₂ : Disjoint (↑(g₂ n k m).support) B)
    (hDisj₃ : Disjoint (↑(g₃ n k m).support) B)
    (hg₁Disj : Disjoint (g₁ n k m '' B) B)
    (ha₁_in_B : a₁ n k m hn ∈ B) : B.ncard ≤ 1 := by
  have hSubset := case2_B_subset_tailA B hDisj₂ hDisj₃
  rw [Set.ncard_le_one (Set.toFinite B)]
  intro a ha b hb
  have haTail := hSubset a ha; have hbTail := hSubset b hb
  simp only [isTailA] at haTail hbTail
  have hg₁_not : ∀ x ∈ B, g₁ n k m x ∉ B := fun x hx hg₁x =>
    Set.disjoint_iff.mp hg₁Disj ⟨⟨x, hx, rfl⟩, hg₁x⟩
  by_cases hn1 : n = 1; · ext1; omega
  have hn2 : n ≥ 2 := by omega
  have h7_not_in_B : (⟨7, by omega⟩ : Omega n k m) ∉ B := by
    have heq := g₁_a₁_eq_elem7 (k := k) (m := m) hn hn2
    have := hg₁_not (a₁ n k m hn) ha₁_in_B; rwa [heq] at this
  suffices h_all_6 : ∀ x ∈ B, x.val = 6 by
    have ha6 := h_all_6 a ha; have hb6 := h_all_6 b hb; ext1; omega
  intro x hx
  have hxTail := hSubset x hx; simp only [isTailA] at hxTail
  by_contra hne; have hxgt6 : x.val > 6 := by omega
  have hx_ne_7 : x.val ≠ 7 := by
    intro heq; apply h7_not_in_B; have : x = ⟨7, by omega⟩ := Fin.ext heq; rwa [← this]
  have hxge8 : x.val ≥ 8 := by omega
  -- BUG: The theorem is false for n ≥ 3 (see docstring). This sorry cannot be eliminated
  -- without adding hypotheses about B being a proper block in a block system.
  sorry
