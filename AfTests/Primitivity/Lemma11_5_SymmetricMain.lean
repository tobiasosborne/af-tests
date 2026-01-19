/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Primitivity.Lemma11_5_SymmetricCases
import AfTests.Primitivity.Lemma11_5_Cases
import AfTests.Primitivity.Lemma11_5_SupportCover
import AfTests.Primitivity.Lemma11_5_Defs
import AfTests.Primitivity.Lemma11_5_SymmetricCase2B
import AfTests.Primitivity.Lemma11_5_SymmetricCase2C

/-!
# Lemma 11.5: Symmetric Main Contradiction Lemmas

Main contradiction lemmas for k >= 1 and m >= 1 cases.
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

-- ============================================
-- SECTION 1: CASE 1B IMPOSSIBILITY FOR G3/G1
-- ============================================

/-- Element 3 is in supp(g₂) -/
theorem elem3_in_support_g₂ : (⟨3, by omega⟩ : Omega n k m) ∈ (g₂ n k m).support := by
  have hNodup := g₂_list_nodup n k m
  have hNotSingleton : ∀ x, g₂CoreList n k m ++ tailBList n k m ≠ [x] := by
    intro x h; have : (g₂CoreList n k m ++ tailBList n k m).length = 1 := by rw [h]; simp
    have := g₂_cycle_length n k m; omega
  rw [g₂, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₂CoreList, List.mem_cons]; tauto

/-- Case 1b: g₃(B) ≠ B is impossible when supp(g₂) ⊆ B -/
theorem case1b_impossible_g₃ (B : Set (Omega n k m))
    (hSupp : ((g₂ n k m).support : Set _) ⊆ B)
    (hDisj : Disjoint (g₃ n k m '' B) B) : False := by
  have h3_in_B : (⟨3, by omega⟩ : Omega n k m) ∈ B := hSupp elem3_in_support_g₂
  have hFix : g₃ n k m (⟨3, by omega⟩ : Omega n k m) = ⟨3, by omega⟩ := g₃_fixes_elem3
  have h3_in_both := fixed_point_in_image_inter (g₃ n k m) B _ h3_in_B hFix
  exact Set.disjoint_iff.mp hDisj h3_in_both

/-- Case 1b: g₁(B) ≠ B is impossible when supp(g₃) ⊆ B -/
theorem case1b_impossible_g₁ (B : Set (Omega n k m))
    (hSupp : ((g₃ n k m).support : Set _) ⊆ B)
    (hDisj : Disjoint (g₁ n k m '' B) B) : False := by
  have h1_in_B : (⟨1, by omega⟩ : Omega n k m) ∈ B := hSupp elem1_in_support_g₃
  have h1_not_in_supp : (⟨1, by omega⟩ : Omega n k m) ∉ (g₁ n k m).support :=
    elem1_not_in_support_g₁'
  have hFix := fixed_outside_support _ _ h1_not_in_supp
  have h1_in_both := fixed_point_in_image_inter (g₁ n k m) B _ h1_in_B hFix
  exact Set.disjoint_iff.mp hDisj h1_in_both

/-- Case 1b: g₁(B) ≠ B is impossible when supp(g₂) ⊆ B (element 4 fixed by g₁) -/
theorem case1b_impossible_g₁_from_g₂ (B : Set (Omega n k m))
    (hSupp : ((g₂ n k m).support : Set _) ⊆ B)
    (hDisj : Disjoint (g₁ n k m '' B) B) : False := by
  have h4_in_B : (⟨4, by omega⟩ : Omega n k m) ∈ B := hSupp elem4_in_support_g₂
  have hFix : g₁ n k m ⟨4, by omega⟩ = ⟨4, by omega⟩ := g₁_fixes_elem4'
  have h4_in_both := fixed_point_in_image_inter (g₁ n k m) B _ h4_in_B hFix
  exact Set.disjoint_iff.mp hDisj h4_in_both

/-- Case 1b: g₂(B) ≠ B is impossible when supp(g₃) ⊆ B (element 4 fixed by g₂) -/
theorem case1b_impossible_g₂_from_g₃ (B : Set (Omega n k m))
    (hSupp : ((g₃ n k m).support : Set _) ⊆ B)
    (hDisj : Disjoint (g₂ n k m '' B) B) : False := by
  have h5_in_B : (⟨5, by omega⟩ : Omega n k m) ∈ B := by
    have h5_in_supp : (⟨5, by omega⟩ : Omega n k m) ∈ (g₃ n k m).support := by
      have hNodup := g₃_list_nodup n k m
      have hNotSingleton : ∀ x, g₃CoreList n k m ++ tailCList n k m ≠ [x] := by
        intro x h; have : (g₃CoreList n k m ++ tailCList n k m).length = 1 := by rw [h]; simp
        have := g₃_cycle_length n k m; omega
      rw [g₃, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
      simp only [List.mem_toFinset, List.mem_append, g₃CoreList, List.mem_cons]; tauto
    exact hSupp h5_in_supp
  have h5_not_in_supp_g₂ : (⟨5, by omega⟩ : Omega n k m) ∉ (g₂ n k m).support := by
    simp only [g₂, Equiv.Perm.mem_support, ne_eq, not_not]
    apply List.formPerm_apply_of_notMem
    intro h; simp only [List.mem_append, g₂CoreList, tailBList, List.mem_cons,
      List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
    rcases h with h | h
    · rcases h with h | h | h | h <;> simp only [Fin.ext_iff] at h <;> omega
    · obtain ⟨j, _, hj⟩ := h; simp only [Fin.ext_iff] at hj; have := j.isLt; omega
  have hFix := fixed_outside_support _ _ h5_not_in_supp_g₂
  have h5_in_both := fixed_point_in_image_inter (g₂ n k m) B _ h5_in_B hFix
  exact Set.disjoint_iff.mp hDisj h5_in_both

-- ============================================
-- SECTION 2: CASE 2 STABILIZATION FOR B/C
-- ============================================

/-- Case 2: g₂(B) ≠ B forces g₁(B) = B and g₃(B) = B when b₁ ∈ B -/
theorem case2_forces_stabilization_B (hk : k ≥ 1) (B : Set (Omega n k m))
    (hB : b₁ n k m hk ∈ B)
    (h₁Disj : ¬PreservesSet (g₁ n k m) B → Disjoint (g₁ n k m '' B) B)
    (h₃Disj : ¬PreservesSet (g₃ n k m) B → Disjoint (g₃ n k m '' B) B) :
    PreservesSet (g₁ n k m) B ∧ PreservesSet (g₃ n k m) B := by
  constructor
  · by_contra hNotPres
    have hDisj := h₁Disj hNotPres
    have hFix : g₁ n k m (b₁ n k m hk) = b₁ n k m hk := g₁_fixes_b₁ hk
    have h_in_both := fixed_point_in_image_inter (g₁ n k m) B (b₁ n k m hk) hB hFix
    exact Set.disjoint_iff.mp hDisj h_in_both
  · by_contra hNotPres
    have hDisj := h₃Disj hNotPres
    have hFix : g₃ n k m (b₁ n k m hk) = b₁ n k m hk := g₃_fixes_b₁ hk
    have h_in_both := fixed_point_in_image_inter (g₃ n k m) B (b₁ n k m hk) hB hFix
    exact Set.disjoint_iff.mp hDisj h_in_both

/-- Case 2: g₃(B) ≠ B forces g₁(B) = B and g₂(B) = B when c₁ ∈ B -/
theorem case2_forces_stabilization_C (hm : m ≥ 1) (B : Set (Omega n k m))
    (hC : c₁ n k m hm ∈ B)
    (h₁Disj : ¬PreservesSet (g₁ n k m) B → Disjoint (g₁ n k m '' B) B)
    (h₂Disj : ¬PreservesSet (g₂ n k m) B → Disjoint (g₂ n k m '' B) B) :
    PreservesSet (g₁ n k m) B ∧ PreservesSet (g₂ n k m) B := by
  constructor
  · by_contra hNotPres
    have hDisj := h₁Disj hNotPres
    have hFix : g₁ n k m (c₁ n k m hm) = c₁ n k m hm := g₁_fixes_c₁ hm
    have h_in_both := fixed_point_in_image_inter (g₁ n k m) B (c₁ n k m hm) hC hFix
    exact Set.disjoint_iff.mp hDisj h_in_both
  · by_contra hNotPres
    have hDisj := h₂Disj hNotPres
    have hFix : g₂ n k m (c₁ n k m hm) = c₁ n k m hm := g₂_fixes_c₁ hm
    have h_in_both := fixed_point_in_image_inter (g₂ n k m) B (c₁ n k m hm) hC hFix
    exact Set.disjoint_iff.mp hDisj h_in_both

-- ============================================
-- SECTION 3: CASE 2 IMPOSSIBILITY FOR B/C
-- ============================================

/-- Case 2 impossible for k >= 1 case -/
theorem case2_impossible_B (hk : k ≥ 1) (hn : n ≥ 1) (B : Set (Omega n k m))
    (hg₂_disj : Disjoint (g₂ n k m '' B) B) (hb₁_in_B : b₁ n k m hk ∈ B)
    (hg₁_pres : PreservesSet (g₁ n k m) B) (hg₃_pres : PreservesSet (g₃ n k m) B)
    (hSize : 1 < B.ncard) : False := by
  -- B is disjoint from supp(g₁) and supp(g₃)
  have hDisj₁ := case2B_B_disjoint_supp_g₁ hn B hg₂_disj hg₁_pres
  have hDisj₃ := case2B_B_disjoint_supp_g₃ B hg₂_disj hg₃_pres
  -- For k = 1, B ⊆ tailB = {single element}, so |B| ≤ 1
  by_cases hk1 : k = 1
  · have hB_small := case2B_B_ncard_le_one_k1 hk1 B hDisj₁ hDisj₃; omega
  · -- For k >= 2, the orbit structure argument (analogous to case2_B_ncard_le_one for n>=3)
    -- shows B ⊆ tailB with |B| ≤ 1 via consecutive element exclusion
    have hB_small : B.ncard ≤ 1 := by
      have hSubset := case2B_B_subset_tailB B hDisj₁ hDisj₃
      rw [Set.ncard_le_one (Set.toFinite B)]
      intro a ha b hb
      simp only [isTailB] at hSubset
      have haTail := hSubset a ha; have hbTail := hSubset b hb
      -- Orbit structure: g₂ cycles through tailB, g₂(B) ∩ B = ∅ forces gaps
      -- For k=2: only 2 elements in tailB, can't have both with disjoint orbit
      -- For k >= 2: all elements in tailB and g₂ cycles through them
      -- Since g₂(B) ∩ B = ∅ and B ⊆ tailB, we can't have two distinct elements
      -- (g₂ would map one to the other or nearby, creating overlap)
      -- The argument uses: b₁ ∈ B, g₂(b₁) ∉ B, so the orbit gaps force |B| = 1
      sorry
    omega

/-- Case 2 impossible for m >= 1 case -/
theorem case2_impossible_C (hm : m ≥ 1) (hn : n ≥ 1) (B : Set (Omega n k m))
    (hg₃_disj : Disjoint (g₃ n k m '' B) B) (hc₁_in_B : c₁ n k m hm ∈ B)
    (hg₁_pres : PreservesSet (g₁ n k m) B) (hg₂_pres : PreservesSet (g₂ n k m) B)
    (hSize : 1 < B.ncard) : False := by
  -- B is disjoint from supp(g₁) and supp(g₂)
  have hDisj₁ := case2C_B_disjoint_supp_g₁ hn B hg₃_disj hg₁_pres
  have hDisj₂ := case2C_B_disjoint_supp_g₂ B hg₃_disj hg₂_pres
  -- For m = 1, B ⊆ tailC = {single element}, so |B| ≤ 1
  by_cases hm1 : m = 1
  · have hB_small := case2C_B_ncard_le_one_m1 hm1 B hDisj₁ hDisj₂; omega
  · -- For m >= 2, orbit structure argument (analogous to k>=2 and n>=3 cases)
    have hB_small : B.ncard ≤ 1 := by
      have hSubset := case2C_B_subset_tailC B hDisj₁ hDisj₂
      rw [Set.ncard_le_one (Set.toFinite B)]
      intro a ha b hb
      simp only [isTailC] at hSubset
      have haTail := hSubset a ha; have hbTail := hSubset b hb
      -- For m >= 2: Same orbit structure argument as k >= 2 case
      sorry
    omega
