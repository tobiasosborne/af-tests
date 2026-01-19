/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Core
import AfTests.Primitivity.Lemma11_2
import AfTests.Primitivity.Lemma11_3
import AfTests.Primitivity.Lemma11_5_FixedPoints

/-!
# Lemma 11.5: Case Analysis Helpers

Helper lemmas for the case analysis in Lemma 11.5, proving that H admits
no non-trivial block system.

## Main Results

* `perm_image_preserves_or_disjoint`: In a pairwise disjoint block system,
  σ '' B either equals B or is disjoint from B
* `case1a_ii_impossible`: Case 1a-ii leads to contradiction

## Reference

See `examples/lemmas/lemma11_5_no_nontrivial_blocks.md` for the full proof.
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

-- ============================================
-- SECTION 1: BLOCK SYSTEM BRIDGE LEMMAS
-- ============================================

/-- In a pairwise disjoint block system, if B and σ '' B are both blocks,
    then either σ '' B = B or they are disjoint -/
theorem perm_image_preserves_or_disjoint {α : Type*}
    (σ : Perm α) (B : Set α) (Blocks : Set (Set α))
    (hDisj : Blocks.PairwiseDisjoint id) (hB : B ∈ Blocks) (hσB : σ '' B ∈ Blocks) :
    σ '' B = B ∨ Disjoint (σ '' B) B := by
  by_cases h : σ '' B = B
  · left; exact h
  · right
    apply hDisj hσB hB h

/-- Contrapositive: if σ '' B ∩ B is nonempty, then σ '' B = B -/
theorem perm_image_eq_of_meet_nonempty {α : Type*}
    (σ : Perm α) (B : Set α) (Blocks : Set (Set α))
    (hDisj : Blocks.PairwiseDisjoint id) (hB : B ∈ Blocks) (hσB : σ '' B ∈ Blocks)
    (hMeet : (σ '' B ∩ B).Nonempty) : σ '' B = B := by
  rcases perm_image_preserves_or_disjoint σ B Blocks hDisj hB hσB with h | h
  · exact h
  · exfalso
    obtain ⟨x, hx⟩ := hMeet
    exact Set.disjoint_iff.mp h hx

/-- Convert between PreservesSet and set equality -/
theorem preservesSet_iff_image_eq {α : Type*} [Fintype α]
    (σ : Perm α) (B : Set α) : PreservesSet σ B ↔ σ '' B = B := Iff.rfl

/-- If σ fixes x ∈ B, then x ∈ σ '' B ∩ B -/
theorem fixed_point_in_image_inter {α : Type*}
    (σ : Perm α) (B : Set α) (x : α) (hx : x ∈ B) (hFix : σ x = x) :
    x ∈ σ '' B ∩ B := by
  refine ⟨?_, hx⟩
  rw [Set.mem_image]
  exact ⟨x, hx, hFix⟩

-- ============================================
-- SECTION 2: FIXED POINT HELPERS
-- ============================================

/-- g₂ is a cycle -/
theorem g₂_isCycle (n k m : ℕ) : (g₂ n k m).IsCycle := by
  unfold g₂
  apply List.isCycle_formPerm
  · exact g₂_list_nodup n k m
  · have := g₂_cycle_length n k m; simp only [List.length_append] at this ⊢; omega

/-- g₃ is a cycle -/
theorem g₃_isCycle (n k m : ℕ) : (g₃ n k m).IsCycle := by
  unfold g₃
  apply List.isCycle_formPerm
  · exact g₃_list_nodup n k m
  · have := g₃_cycle_length n k m; simp only [List.length_append] at this ⊢; omega

/-- Element 0 is in supp(g₂) (it's the first element of the g₂ cycle) -/
theorem elem0_in_support_g₂ :
    (⟨0, by omega⟩ : Omega n k m) ∈ (g₂ n k m).support := by
  have hNodup := g₂_list_nodup n k m
  have hNotSingleton : ∀ x, g₂CoreList n k m ++ tailBList n k m ≠ [x] := by
    intro x h
    have : (g₂CoreList n k m ++ tailBList n k m).length = 1 := by rw [h]; simp
    have := g₂_cycle_length n k m
    omega
  rw [g₂, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₂CoreList, List.mem_cons]
  tauto

/-- Element 1 is in supp(g₂) -/
theorem elem1_in_support_g₂ :
    (⟨1, by omega⟩ : Omega n k m) ∈ (g₂ n k m).support := by
  have hNodup := g₂_list_nodup n k m
  have hNotSingleton : ∀ x, g₂CoreList n k m ++ tailBList n k m ≠ [x] := by
    intro x h
    have : (g₂CoreList n k m ++ tailBList n k m).length = 1 := by rw [h]; simp
    have := g₂_cycle_length n k m
    omega
  rw [g₂, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₂CoreList, List.mem_cons]
  tauto

/-- Element 1 is in supp(g₃) -/
theorem elem1_in_support_g₃ :
    (⟨1, by omega⟩ : Omega n k m) ∈ (g₃ n k m).support := by
  have hNodup := g₃_list_nodup n k m
  have hNotSingleton : ∀ x, g₃CoreList n k m ++ tailCList n k m ≠ [x] := by
    intro x h
    have : (g₃CoreList n k m ++ tailCList n k m).length = 1 := by rw [h]; simp
    have := g₃_cycle_length n k m
    omega
  rw [g₃, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₃CoreList, List.mem_cons]
  tauto

/-- Element 0 is in supp(g₁) -/
theorem elem0_in_support_g₁ :
    (⟨0, by omega⟩ : Omega n k m) ∈ (g₁ n k m).support := by
  have hNodup := g₁_list_nodup n k m
  have hNotSingleton : ∀ x, g₁CoreList n k m ++ tailAList n k m ≠ [x] := by
    intro x h
    have : (g₁CoreList n k m ++ tailAList n k m).length = 1 := by rw [h]; simp
    have := g₁_cycle_length n k m
    omega
  rw [g₁, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₁CoreList, List.mem_cons]
  tauto

/-- Element 3 is in supp(g₁) -/
theorem elem3_in_support_g₁ :
    (⟨3, by omega⟩ : Omega n k m) ∈ (g₁ n k m).support := by
  have hNodup := g₁_list_nodup n k m
  have hNotSingleton : ∀ x, g₁CoreList n k m ++ tailAList n k m ≠ [x] := by
    intro x h
    have : (g₁CoreList n k m ++ tailAList n k m).length = 1 := by rw [h]; simp
    have := g₁_cycle_length n k m
    omega
  rw [g₁, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₁CoreList, List.mem_cons]
  tauto

/-- Element 0 is NOT in supp(g₃) -/
theorem elem0_not_in_support_g₃ :
    (⟨0, by omega⟩ : Omega n k m) ∉ (g₃ n k m).support := by
  simp only [g₃, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_notMem
  intro h
  simp only [List.mem_append, g₃CoreList, tailCList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h
    all_goals simp only [Fin.ext_iff] at h; omega
  · obtain ⟨j, _, hj⟩ := h
    simp only [Fin.ext_iff] at hj
    omega

/-- g₃ fixes element 0 -/
theorem g₃_fixes_elem0 :
    g₃ n k m (⟨0, by omega⟩ : Omega n k m) = ⟨0, by omega⟩ := by
  exact fixed_outside_support _ _ elem0_not_in_support_g₃

/-- Element 3 is NOT in supp(g₃) -/
theorem elem3_not_in_support_g₃ :
    (⟨3, by omega⟩ : Omega n k m) ∉ (g₃ n k m).support := by
  simp only [g₃, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_notMem
  intro h
  simp only [List.mem_append, g₃CoreList, tailCList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h
    all_goals simp only [Fin.ext_iff] at h; omega
  · obtain ⟨j, _, hj⟩ := h
    simp only [Fin.ext_iff] at hj
    omega

/-- g₃ fixes element 3 -/
theorem g₃_fixes_elem3 :
    g₃ n k m (⟨3, by omega⟩ : Omega n k m) = ⟨3, by omega⟩ := by
  exact fixed_outside_support _ _ elem3_not_in_support_g₃

-- ============================================
-- SECTION 3: CASE 1a-ii IMPOSSIBILITY
-- ============================================

/-- Case 1a-ii impossibility: g₃(B) ≠ B is impossible when element 0 ∈ B
    because g₃ fixes element 0 (not in supp(g₃)), creating intersection -/
theorem case1a_ii_impossible (B : Set (Omega n k m))
    (h0_in_B : (⟨0, by omega⟩ : Omega n k m) ∈ B)
    (hDisj : Disjoint (g₃ n k m '' B) B) : False := by
  -- Element 0 is fixed by g₃ (not in supp(g₃))
  have hFix : g₃ n k m (⟨0, by omega⟩ : Omega n k m) = ⟨0, by omega⟩ := g₃_fixes_elem0
  -- Therefore 0 ∈ g₃(B) ∩ B
  have h0_in_both := fixed_point_in_image_inter (g₃ n k m) B _ h0_in_B hFix
  -- This contradicts disjointness
  exact Set.disjoint_iff.mp hDisj h0_in_both

-- Note: case1a_i proof moved to Lemma11_5_SupportCover.lean as `case1a_i_supports_cover_univ`
