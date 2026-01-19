/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Core
import AfTests.Primitivity.Lemma11_5_CycleSupport
import AfTests.Primitivity.Lemma11_5_SupportCover
import AfTests.Primitivity.Lemma11_5_FixedPoints
import AfTests.Primitivity.Lemma11_5_SymmetricCases
import AfTests.Primitivity.Lemma11_3

/-!
# Lemma 11.5 Symmetric Case 2B: B-Tail Helper Lemmas
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

/-- Element 1 is NOT in supp(g₁) -/
theorem elem1_not_in_support_g₁' :
    (⟨1, by omega⟩ : Omega n k m) ∉ (g₁ n k m).support := by
  simp only [g₁, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_notMem
  intro h; simp only [List.mem_append, g₁CoreList, tailAList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h <;> simp only [Fin.ext_iff] at h <;> omega
  · obtain ⟨j, _, hj⟩ := h; simp only [Fin.ext_iff] at hj; omega

/-- Element 4 is NOT in supp(g₁) -/
theorem elem4_not_in_support_g₁' :
    (⟨4, by omega⟩ : Omega n k m) ∉ (g₁ n k m).support := by
  simp only [g₁, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_notMem
  intro h; simp only [List.mem_append, g₁CoreList, tailAList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h <;> simp only [Fin.ext_iff] at h <;> omega
  · obtain ⟨j, _, hj⟩ := h; simp only [Fin.ext_iff] at hj; omega

/-- g₁ fixes element 4 -/
theorem g₁_fixes_elem4' : g₁ n k m (⟨4, by omega⟩ : Omega n k m) = ⟨4, by omega⟩ :=
  fixed_outside_support _ _ elem4_not_in_support_g₁'

/-- If x ∈ supp(g₁) and g₁(B) = B, then supp(g₁) ⊆ B -/
theorem g₁_support_subset_if_meets (B : Set (Omega n k m))
    (hg₁_pres : PreservesSet (g₁ n k m) B)
    (hMeets : ∃ x, x ∈ (g₁ n k m).support ∧ x ∈ B) :
    (↑(g₁ n k m).support : Set _) ⊆ B := by
  have hCyc := g₁_isCycle n k m (by omega)
  rcases cycle_support_subset_or_disjoint hCyc hg₁_pres with hSub | hDisj
  · exact hSub
  · obtain ⟨x, hx_supp, hx_B⟩ := hMeets
    exfalso; exact Set.disjoint_iff.mp hDisj ⟨hx_supp, hx_B⟩

/-- If x ∈ supp(g₃) and g₃(B) = B, then supp(g₃) ⊆ B -/
theorem g₃_support_subset_if_meets (B : Set (Omega n k m))
    (hg₃_pres : PreservesSet (g₃ n k m) B)
    (hMeets : ∃ x, x ∈ (g₃ n k m).support ∧ x ∈ B) :
    (↑(g₃ n k m).support : Set _) ⊆ B := by
  have hCyc := g₃_isCycle n k m
  rcases cycle_support_subset_or_disjoint hCyc hg₃_pres with hSub | hDisj
  · exact hSub
  · obtain ⟨x, hx_supp, hx_B⟩ := hMeets
    exfalso; exact Set.disjoint_iff.mp hDisj ⟨hx_supp, hx_B⟩

/-- Element 5 is in supp(g₃) -/
theorem elem5_in_support_g₃' : (⟨5, by omega⟩ : Omega n k m) ∈ (g₃ n k m).support := by
  have hNodup := g₃_list_nodup n k m
  have hNotSingleton : ∀ x, g₃CoreList n k m ++ tailCList n k m ≠ [x] := by
    intro x h; have : (g₃CoreList n k m ++ tailCList n k m).length = 1 := by rw [h]; simp
    have := g₃_cycle_length n k m; omega
  rw [g₃, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₃CoreList, List.mem_cons]; tauto

/-- Element 5 is NOT in supp(g₂) -/
theorem elem5_not_in_support_g₂ : (⟨5, by omega⟩ : Omega n k m) ∉ (g₂ n k m).support := by
  simp only [g₂, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_notMem
  intro h; simp only [List.mem_append, g₂CoreList, tailBList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h <;> simp only [Fin.ext_iff] at h <;> omega
  · obtain ⟨j, _, hj⟩ := h; simp only [Fin.ext_iff] at hj; have := j.isLt; omega

/-- g₂ fixes element 5 -/
theorem g₂_fixes_elem5 : g₂ n k m (⟨5, by omega⟩ : Omega n k m) = ⟨5, by omega⟩ :=
  fixed_outside_support _ _ elem5_not_in_support_g₂

/-- In Case 2B, B is disjoint from supp(g₁).
    Uses element 5 which is in supp(g₁) (no n≥1 required) and fixed by g₂. -/
theorem case2B_B_disjoint_supp_g₁ (B : Set (Omega n k m))
    (hg₂_disj : Disjoint (g₂ n k m '' B) B)
    (hg₁_pres : PreservesSet (g₁ n k m) B) :
    Disjoint (↑(g₁ n k m).support) B := by
  by_contra hMeet
  rw [Set.not_disjoint_iff] at hMeet
  obtain ⟨x, hx_supp, hx_B⟩ := hMeet
  have hSupp := g₁_support_subset_if_meets B hg₁_pres ⟨x, hx_supp, hx_B⟩
  -- Use element 5 which is in supp(g₁) and fixed by g₂
  have h5_in_supp : (⟨5, by omega⟩ : Omega n k m) ∈ (g₁ n k m).support := elem5_in_support_g₁
  have h5_in_B := hSupp h5_in_supp
  have hFix := g₂_fixes_elem5 (n := n) (k := k) (m := m)
  have h5_in_img : (⟨5, by omega⟩ : Omega n k m) ∈ g₂ n k m '' B := ⟨_, h5_in_B, hFix⟩
  exact Set.disjoint_iff.mp hg₂_disj ⟨h5_in_img, h5_in_B⟩

/-- In Case 2B, B is disjoint from supp(g₃) -/
theorem case2B_B_disjoint_supp_g₃ (B : Set (Omega n k m))
    (hg₂_disj : Disjoint (g₂ n k m '' B) B)
    (hg₃_pres : PreservesSet (g₃ n k m) B) :
    Disjoint (↑(g₃ n k m).support) B := by
  by_contra hMeet
  rw [Set.not_disjoint_iff] at hMeet
  obtain ⟨x, hx_supp, hx_B⟩ := hMeet
  have hSupp := g₃_support_subset_if_meets B hg₃_pres ⟨x, hx_supp, hx_B⟩
  have h5_in_supp : (⟨5, by omega⟩ : Omega n k m) ∈ (g₃ n k m).support := elem5_in_support_g₃'
  have h5_in_B := hSupp h5_in_supp
  have hFix := g₂_fixes_elem5 (n := n) (k := k) (m := m)
  have h5_in_img : (⟨5, by omega⟩ : Omega n k m) ∈ g₂ n k m '' B := ⟨_, h5_in_B, hFix⟩
  exact Set.disjoint_iff.mp hg₂_disj ⟨h5_in_img, h5_in_B⟩

/-- Every core element is in supp(g₁) or supp(g₃) -/
theorem core_in_support_g₁_or_g₃ (x : Omega n k m) (hCore : isCore x) :
    x ∈ (g₁ n k m).support ∨ x ∈ (g₃ n k m).support := by
  obtain ⟨v, hv⟩ := x
  simp only [isCore] at hCore
  have : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
  · left; convert elem0_in_support_g₁ (n := n) (k := k) (m := m)
  · right; convert elem1_in_support_g₃ (n := n) (k := k) (m := m)
  · right; convert elem2_in_support_g₃ (n := n) (k := k) (m := m)
  · left; convert elem3_in_support_g₁ (n := n) (k := k) (m := m)
  · right; have h : (⟨4, by omega⟩ : Omega n k m) ∈ (g₃ n k m).support := by
      have hNodup := g₃_list_nodup n k m
      have hNotSingleton : ∀ x, g₃CoreList n k m ++ tailCList n k m ≠ [x] := by
        intro x h; have : (g₃CoreList n k m ++ tailCList n k m).length = 1 := by rw [h]; simp
        have := g₃_cycle_length n k m; omega
      rw [g₃, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
      simp only [List.mem_toFinset, List.mem_append, g₃CoreList, List.mem_cons]; tauto
    convert h
  · left; convert elem5_in_support_g₁ (n := n) (k := k) (m := m)

/-- In Case 2B, B ⊆ tailB -/
theorem case2B_B_subset_tailB (B : Set (Omega n k m))
    (hDisj₁ : Disjoint (↑(g₁ n k m).support) B)
    (hDisj₃ : Disjoint (↑(g₃ n k m).support) B) :
    ∀ x ∈ B, isTailB x := by
  intro x hx
  rcases Omega.partition x with hCore | hA | hB | hC
  · rcases core_in_support_g₁_or_g₃ x hCore with h1 | h3
    · exact (Set.disjoint_iff.mp hDisj₁ ⟨h1, hx⟩).elim
    · exact (Set.disjoint_iff.mp hDisj₃ ⟨h3, hx⟩).elim
  · have h_in_supp : x ∈ (g₁ n k m).support := by
      simp only [isTailA] at hA; obtain ⟨hLo, hHi⟩ := hA
      have hi : x.val - 6 < n := by have := x.isLt; omega
      convert tailA_in_support_g₁ (⟨x.val - 6, hi⟩ : Fin n) using 1
      simp only [Fin.ext_iff]; omega
    exact (Set.disjoint_iff.mp hDisj₁ ⟨h_in_supp, hx⟩).elim
  · exact hB
  · have h_in_supp : x ∈ (g₃ n k m).support := by
      simp only [isTailC] at hC; obtain ⟨hLo, hHi⟩ := hC
      have hi : x.val - 6 - n - k < m := by have := x.isLt; omega
      convert tailC_in_support_g₃ (⟨x.val - 6 - n - k, hi⟩ : Fin m) using 1
      simp only [Fin.ext_iff]; omega
    exact (Set.disjoint_iff.mp hDisj₃ ⟨h_in_supp, hx⟩).elim

/-- In Case 2B with k=1, |B| ≤ 1 -/
theorem case2B_B_ncard_le_one_k1 (hk1 : k = 1) (B : Set (Omega n k m))
    (hDisj₁ : Disjoint (↑(g₁ n k m).support) B)
    (hDisj₃ : Disjoint (↑(g₃ n k m).support) B) : B.ncard ≤ 1 := by
  have hSubset := case2B_B_subset_tailB B hDisj₁ hDisj₃
  rw [Set.ncard_le_one (Set.toFinite B)]
  intro a ha b hb
  have haTail := hSubset a ha
  have hbTail := hSubset b hb
  simp only [isTailB] at haTail hbTail
  have ha_eq : a.val = 6 + n := by omega
  have hb_eq : b.val = 6 + n := by omega
  ext1; omega
