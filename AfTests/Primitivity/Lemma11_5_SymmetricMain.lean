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
import AfTests.Primitivity.Lemma11_5_OrbitHelpers

/-!
# Lemma 11.5: Symmetric Main Contradiction Lemmas

Main contradiction lemmas for k >= 1 and m >= 1 cases.
-/

open Equiv Equiv.Perm Set OrbitTailB OrbitTailC

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
theorem case2_impossible_B (hk : k ≥ 1) (B : Set (Omega n k m))
    (hg₂_disj : Disjoint (g₂ n k m '' B) B) (hb₁_in_B : b₁ n k m hk ∈ B)
    (hg₁_pres : PreservesSet (g₁ n k m) B) (hg₃_pres : PreservesSet (g₃ n k m) B)
    (hBlock : ∀ j : ℕ, (g₂ n k m ^ j) '' B = B ∨ Disjoint ((g₂ n k m ^ j) '' B) B)
    (hSize : 1 < B.ncard) : False := by
  -- B is disjoint from supp(g₁) and supp(g₃)
  have hDisj₁ := case2B_B_disjoint_supp_g₁ B hg₂_disj hg₁_pres
  have hDisj₃ := case2B_B_disjoint_supp_g₃ B hg₂_disj hg₃_pres
  have hSubset := case2B_B_subset_tailB B hDisj₁ hDisj₃
  -- For k = 1, B ⊆ tailB = {single element}, so |B| ≤ 1
  by_cases hk1 : k = 1
  · have hB_small := case2B_B_ncard_le_one_k1 hk1 B hDisj₁ hDisj₃; omega
  · -- For k >= 2: use orbit argument with block property
    have hk2 : k ≥ 2 := by omega
    -- Since |B| ≥ 2 and 6+n+1 ∉ B, find second element 6+n+j with j ≥ 2
    obtain ⟨x, hx_in_B, hx_ne_b₁⟩ := Set.exists_ne_of_one_lt_ncard hSize (b₁ n k m hk)
    have hxTail := hSubset x hx_in_B
    simp only [isTailB] at hxTail
    have hx_ne_6n : x.val ≠ 6 + n := by
      intro h; apply hx_ne_b₁; ext1; simp only [b₁, Fin.ext_iff]; exact h
    -- g₂(b₁) = 6+n+1 ∉ B (from disjointness)
    have hg₂b₁_eq : g₂ n k m (b₁ n k m hk) = ⟨6 + n + 1, by omega⟩ := g₂_b₁_eq_b₁_succ hk hk2
    have h6n1_not_in_B : (⟨6 + n + 1, by omega⟩ : Omega n k m) ∉ B := by
      intro h6n1; have h_in_img : (⟨6+n+1, by omega⟩ : Omega n k m) ∈ g₂ n k m '' B :=
        ⟨b₁ n k m hk, hb₁_in_B, hg₂b₁_eq⟩
      exact Set.disjoint_iff.mp hg₂_disj ⟨h_in_img, h6n1⟩
    have hx_ne_6n1 : x.val ≠ 6 + n + 1 := by
      intro h; apply h6n1_not_in_B
      have : x = ⟨6 + n + 1, by omega⟩ := by ext1; exact h
      rwa [← this]
    have hx_ge : x.val ≥ 6 + n + 2 := by omega
    let j := x.val - 6 - n
    have hj_ge_2 : j ≥ 2 := by simp only [j]; omega
    have hj_lt_k : j < k := by simp only [j]; omega
    -- g₂^j(b₁) = x ∈ B, so g₂^j(B) ∩ B ≠ ∅, hence g₂^j(B) = B
    have hg₂j_b₁ : (g₂ n k m ^ j) (b₁ n k m hk) = x := by
      have h := g₂_pow_b₁_eq_tailB_elem (n := n) (m := m) hk hk2 ⟨j, hj_lt_k⟩ (by omega : j > 0)
      simp only [b₁] at h ⊢
      rw [h]
      ext1; simp only [j]; omega
    have hg₂j_meets : ((g₂ n k m ^ j) '' B ∩ B).Nonempty :=
      ⟨(g₂ n k m ^ j) (b₁ n k m hk), ⟨b₁ n k m hk, hb₁_in_B, rfl⟩, hg₂j_b₁ ▸ hx_in_B⟩
    have hg₂j_pres : (g₂ n k m ^ j) '' B = B :=
      (hBlock j).resolve_right (fun h => Set.not_nonempty_iff_eq_empty.mpr
        (Set.disjoint_iff_inter_eq_empty.mp h) hg₂j_meets)
    -- Iterate: g₂^{rj}(B) = B for all r, so g₂^{rj}(b₁) ∈ B for all r
    have hiter : ∀ r : ℕ, (g₂ n k m ^ (r * j)) '' B = B := by
      intro r; induction r with
      | zero => simp
      | succ r' ih =>
        have h1 : (r' + 1) * j = r' * j + j := by ring
        rw [h1, pow_add, Equiv.Perm.coe_mul, Set.image_comp, hg₂j_pres, ih]
    -- Eventually g₂^{rj}(b₁) exits tailB, contradicting B ⊆ tailB
    obtain ⟨r, hr_pos, hr_exit⟩ := g₂_pow_orbit_hits_core hk hk2 j hj_ge_2 hj_lt_k
    have h_in_B : (g₂ n k m ^ (r * j)) (b₁ n k m hk) ∈ B := by
      rw [← hiter r]; exact ⟨b₁ n k m hk, hb₁_in_B, rfl⟩
    have h_in_tailB := hSubset _ h_in_B
    exact hr_exit h_in_tailB

/-- Case 2 impossible for m >= 1 case -/
theorem case2_impossible_C (hm : m ≥ 1) (B : Set (Omega n k m))
    (hg₃_disj : Disjoint (g₃ n k m '' B) B) (hc₁_in_B : c₁ n k m hm ∈ B)
    (hg₁_pres : PreservesSet (g₁ n k m) B) (hg₂_pres : PreservesSet (g₂ n k m) B)
    (hBlock : ∀ j : ℕ, (g₃ n k m ^ j) '' B = B ∨ Disjoint ((g₃ n k m ^ j) '' B) B)
    (hSize : 1 < B.ncard) : False := by
  -- B is disjoint from supp(g₁) and supp(g₂)
  have hDisj₁ := case2C_B_disjoint_supp_g₁ B hg₃_disj hg₁_pres
  have hDisj₂ := case2C_B_disjoint_supp_g₂ B hg₃_disj hg₂_pres
  have hSubset := case2C_B_subset_tailC B hDisj₁ hDisj₂
  -- For m = 1, B ⊆ tailC = {single element}, so |B| ≤ 1
  by_cases hm1 : m = 1
  · have hB_small := case2C_B_ncard_le_one_m1 hm1 B hDisj₁ hDisj₂; omega
  · -- For m >= 2: use orbit argument with block property
    have hm2 : m ≥ 2 := by omega
    -- Since |B| ≥ 2 and 6+n+k+1 ∉ B, find second element 6+n+k+j with j ≥ 2
    obtain ⟨x, hx_in_B, hx_ne_c₁⟩ := Set.exists_ne_of_one_lt_ncard hSize (c₁ n k m hm)
    have hxTail := hSubset x hx_in_B
    simp only [isTailC] at hxTail
    have hx_ne_6nk : x.val ≠ 6 + n + k := by
      intro h; apply hx_ne_c₁; ext1; simp only [c₁, Fin.ext_iff]; exact h
    -- g₃(c₁) = 6+n+k+1 ∉ B (from disjointness)
    have hg₃c₁_eq : g₃ n k m (c₁ n k m hm) = ⟨6 + n + k + 1, by omega⟩ :=
      g₃_c₁_eq_c₁_succ hm hm2
    have h6nk1_not_in_B : (⟨6 + n + k + 1, by omega⟩ : Omega n k m) ∉ B := by
      intro h6nk1
      have h_in_img : (⟨6+n+k+1, by omega⟩ : Omega n k m) ∈ g₃ n k m '' B :=
        ⟨c₁ n k m hm, hc₁_in_B, hg₃c₁_eq⟩
      exact Set.disjoint_iff.mp hg₃_disj ⟨h_in_img, h6nk1⟩
    have hx_ne_6nk1 : x.val ≠ 6 + n + k + 1 := by
      intro h; apply h6nk1_not_in_B
      have : x = ⟨6 + n + k + 1, by omega⟩ := by ext1; exact h
      rwa [← this]
    have hx_ge : x.val ≥ 6 + n + k + 2 := by omega
    let j := x.val - 6 - n - k
    have hj_ge_2 : j ≥ 2 := by simp only [j]; omega
    have hj_lt_m : j < m := by simp only [j]; omega
    -- g₃^j(c₁) = x ∈ B, so g₃^j(B) ∩ B ≠ ∅, hence g₃^j(B) = B
    have hg₃j_c₁ : (g₃ n k m ^ j) (c₁ n k m hm) = x := by
      have h := g₃_pow_c₁_eq_tailC_elem (n := n) (k := k) hm hm2 ⟨j, hj_lt_m⟩ (by omega : j > 0)
      simp only [c₁] at h ⊢
      rw [h]
      ext1; simp only [j]; omega
    have hg₃j_meets : ((g₃ n k m ^ j) '' B ∩ B).Nonempty :=
      ⟨(g₃ n k m ^ j) (c₁ n k m hm), ⟨c₁ n k m hm, hc₁_in_B, rfl⟩, hg₃j_c₁ ▸ hx_in_B⟩
    have hg₃j_pres : (g₃ n k m ^ j) '' B = B :=
      (hBlock j).resolve_right (fun h => Set.not_nonempty_iff_eq_empty.mpr
        (Set.disjoint_iff_inter_eq_empty.mp h) hg₃j_meets)
    -- Iterate: g₃^{rj}(B) = B for all r, so g₃^{rj}(c₁) ∈ B for all r
    have hiter : ∀ r : ℕ, (g₃ n k m ^ (r * j)) '' B = B := by
      intro r; induction r with
      | zero => simp
      | succ r' ih =>
        have h1 : (r' + 1) * j = r' * j + j := by ring
        rw [h1, pow_add, Equiv.Perm.coe_mul, Set.image_comp, hg₃j_pres, ih]
    -- Eventually g₃^{rj}(c₁) exits tailC, contradicting B ⊆ tailC
    obtain ⟨r, hr_pos, hr_exit⟩ := g₃_pow_orbit_hits_core hm hm2 j hj_ge_2 hj_lt_m
    have h_in_B : (g₃ n k m ^ (r * j)) (c₁ n k m hm) ∈ B := by
      rw [← hiter r]; exact ⟨c₁ n k m hm, hc₁_in_B, rfl⟩
    have h_in_tailC := hSubset _ h_in_B
    exact hr_exit h_in_tailC
