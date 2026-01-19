/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Primitivity.Lemma11_5_SymmetricCase2B

/-!
# Lemma 11.5 Symmetric Case 2C: C-Tail Helper Lemmas
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

/-- Every core element is in supp(g₁) or supp(g₂) -/
theorem core_in_support_g₁_or_g₂ (x : Omega n k m) (hCore : isCore x) :
    x ∈ (g₁ n k m).support ∨ x ∈ (g₂ n k m).support := by
  obtain ⟨v, hv⟩ := x
  simp only [isCore] at hCore
  have : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
  · left; convert elem0_in_support_g₁ (n := n) (k := k) (m := m)
  · right; convert elem1_in_support_g₂ (n := n) (k := k) (m := m)
  · left; have h : (⟨2, by omega⟩ : Omega n k m) ∈ (g₁ n k m).support := by
      have hNodup := g₁_list_nodup n k m
      have hNotSingleton : ∀ x, g₁CoreList n k m ++ tailAList n k m ≠ [x] := by
        intro x h; have : (g₁CoreList n k m ++ tailAList n k m).length = 1 := by rw [h]; simp
        have := g₁_cycle_length n k m; omega
      rw [g₁, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
      simp only [List.mem_toFinset, List.mem_append, g₁CoreList, List.mem_cons]; tauto
    convert h
  · right; have h : (⟨3, by omega⟩ : Omega n k m) ∈ (g₂ n k m).support := by
      have hNodup := g₂_list_nodup n k m
      have hNotSingleton : ∀ x, g₂CoreList n k m ++ tailBList n k m ≠ [x] := by
        intro x h; have : (g₂CoreList n k m ++ tailBList n k m).length = 1 := by rw [h]; simp
        have := g₂_cycle_length n k m; omega
      rw [g₂, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
      simp only [List.mem_toFinset, List.mem_append, g₂CoreList, List.mem_cons]; tauto
    convert h
  · right; convert elem4_in_support_g₂ (n := n) (k := k) (m := m)
  · left; convert elem5_in_support_g₁ (n := n) (k := k) (m := m)

/-- In Case 2C, B is disjoint from supp(g₁).
    Uses element 0 which is in supp(g₁) (no n≥1 required) and fixed by g₃. -/
theorem case2C_B_disjoint_supp_g₁ (B : Set (Omega n k m))
    (hg₃_disj : Disjoint (g₃ n k m '' B) B)
    (hg₁_pres : PreservesSet (g₁ n k m) B) :
    Disjoint (↑(g₁ n k m).support) B := by
  by_contra hMeet
  rw [Set.not_disjoint_iff] at hMeet
  obtain ⟨x, hx_supp, hx_B⟩ := hMeet
  have hSupp := g₁_support_subset_if_meets B hg₁_pres ⟨x, hx_supp, hx_B⟩
  have h0_in_supp := elem0_in_support_g₁ (n := n) (k := k) (m := m)
  have h0_in_B := hSupp h0_in_supp
  have hFix := g₃_fixes_elem0 (n := n) (k := k) (m := m)
  have h0_in_img : (⟨0, by omega⟩ : Omega n k m) ∈ g₃ n k m '' B := ⟨_, h0_in_B, hFix⟩
  exact Set.disjoint_iff.mp hg₃_disj ⟨h0_in_img, h0_in_B⟩

/-- In Case 2C, B is disjoint from supp(g₂) -/
theorem case2C_B_disjoint_supp_g₂ (B : Set (Omega n k m))
    (hg₃_disj : Disjoint (g₃ n k m '' B) B)
    (hg₂_pres : PreservesSet (g₂ n k m) B) :
    Disjoint (↑(g₂ n k m).support) B := by
  by_contra hMeet
  rw [Set.not_disjoint_iff] at hMeet
  obtain ⟨x, hx_supp, hx_B⟩ := hMeet
  have hCyc := g₂_isCycle n k m
  have hSupp : (↑(g₂ n k m).support : Set _) ⊆ B :=
    (cycle_support_subset_or_disjoint hCyc hg₂_pres).resolve_right
      (fun h => Set.not_nonempty_iff_eq_empty.mpr
        (Set.disjoint_iff_inter_eq_empty.mp h) ⟨x, hx_supp, hx_B⟩)
  have h3_in_supp : (⟨3, by omega⟩ : Omega n k m) ∈ (g₂ n k m).support := by
    have hNodup := g₂_list_nodup n k m
    have hNotSingleton : ∀ x, g₂CoreList n k m ++ tailBList n k m ≠ [x] := by
      intro x h; have : (g₂CoreList n k m ++ tailBList n k m).length = 1 := by rw [h]; simp
      have := g₂_cycle_length n k m; omega
    rw [g₂, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
    simp only [List.mem_toFinset, List.mem_append, g₂CoreList, List.mem_cons]; tauto
  have h3_in_B := hSupp h3_in_supp
  have hFix := g₃_fixes_elem3 (n := n) (k := k) (m := m)
  have h3_in_img : (⟨3, by omega⟩ : Omega n k m) ∈ g₃ n k m '' B := ⟨_, h3_in_B, hFix⟩
  exact Set.disjoint_iff.mp hg₃_disj ⟨h3_in_img, h3_in_B⟩

/-- In Case 2C, B ⊆ tailC -/
theorem case2C_B_subset_tailC (B : Set (Omega n k m))
    (hDisj₁ : Disjoint (↑(g₁ n k m).support) B)
    (hDisj₂ : Disjoint (↑(g₂ n k m).support) B) :
    ∀ x ∈ B, isTailC x := by
  intro x hx
  rcases Omega.partition x with hCore | hA | hB | hC
  · rcases core_in_support_g₁_or_g₂ x hCore with h1 | h2
    · exact (Set.disjoint_iff.mp hDisj₁ ⟨h1, hx⟩).elim
    · exact (Set.disjoint_iff.mp hDisj₂ ⟨h2, hx⟩).elim
  · have h_in_supp : x ∈ (g₁ n k m).support := by
      simp only [isTailA] at hA; obtain ⟨hLo, hHi⟩ := hA
      have hi : x.val - 6 < n := by have := x.isLt; omega
      convert tailA_in_support_g₁ (⟨x.val - 6, hi⟩ : Fin n) using 1
      simp only [Fin.ext_iff]; omega
    exact (Set.disjoint_iff.mp hDisj₁ ⟨h_in_supp, hx⟩).elim
  · have h_in_supp : x ∈ (g₂ n k m).support := by
      simp only [isTailB] at hB; obtain ⟨hLo, hHi⟩ := hB
      have hi : x.val - 6 - n < k := by have := x.isLt; omega
      convert tailB_in_support_g₂ (⟨x.val - 6 - n, hi⟩ : Fin k) using 1
      simp only [Fin.ext_iff]; omega
    exact (Set.disjoint_iff.mp hDisj₂ ⟨h_in_supp, hx⟩).elim
  · exact hC

/-- In Case 2C with m=1, |B| ≤ 1 -/
theorem case2C_B_ncard_le_one_m1 (hm1 : m = 1) (B : Set (Omega n k m))
    (hDisj₁ : Disjoint (↑(g₁ n k m).support) B)
    (hDisj₂ : Disjoint (↑(g₂ n k m).support) B) : B.ncard ≤ 1 := by
  have hSubset := case2C_B_subset_tailC B hDisj₁ hDisj₂
  rw [Set.ncard_le_one (Set.toFinite B)]
  intro a ha b hb
  have haTail := hSubset a ha
  have hbTail := hSubset b hb
  simp only [isTailC] at haTail hbTail
  have ha_eq : a.val = 6 + n + k := by omega
  have hb_eq : b.val = 6 + n + k := by omega
  ext1; omega
