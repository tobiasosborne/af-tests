/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Core
import AfTests.Primitivity.Lemma11_2
import AfTests.Primitivity.Lemma11_5_FixedPoints
import AfTests.Primitivity.Lemma11_5_CycleSupport
import AfTests.Primitivity.Lemma11_5_Defs
import AfTests.Primitivity.Lemma11_5_SupportCover
import AfTests.Primitivity.Lemma11_5_Case2
import AfTests.Transitivity.Lemma05ListProps
import AfTests.Primitivity.Lemma11_5_ZpowBlocks
import AfTests.Primitivity.Lemma11_5_OrbitHelpers_Core
import AfTests.Primitivity.Lemma11_5_OrbitHelpers
import AfTests.SignAnalysis.Lemma14

/-!
# Lemma 11.5: Symmetric Cases - Definitions and Basic Lemmas

Defines b₁, c₁ and their basic properties for symmetric case analysis.

## Main Results

* `b₁`, `c₁`: First tail B and C elements
* `b₁_mem_support_g₂`, `c₁_mem_support_g₃`: Support membership
* `lemma11_3_tail_B_in_block`, `lemma11_3_tail_C_in_block`: Tail in block
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

-- ============================================
-- SECTION 1: FIRST TAIL B AND C ELEMENTS
-- ============================================

/-- The first B-tail element b₁ (index 6+n in 0-indexed). -/
def b₁ (n k m : ℕ) (hk : k ≥ 1) : Omega n k m := ⟨6 + n, by omega⟩

/-- The first C-tail element c₁ (index 6+n+k in 0-indexed). -/
def c₁ (n k m : ℕ) (hm : m ≥ 1) : Omega n k m := ⟨6 + n + k, by omega⟩

/-- A set contains b₁ -/
def containsB₁ (B : Set (Omega n k m)) (hk : k ≥ 1) : Prop := b₁ n k m hk ∈ B

/-- A set contains c₁ -/
def containsC₁ (B : Set (Omega n k m)) (hm : m ≥ 1) : Prop := c₁ n k m hm ∈ B

-- ============================================
-- SECTION 2: b₁ AND c₁ IN SUPPORTS
-- ============================================

/-- b₁ is in the support of g₂ -/
theorem b₁_mem_support_g₂ (hk : k ≥ 1) : b₁ n k m hk ∈ (g₂ n k m).support := by
  have hNodup := g₂_list_nodup n k m
  have hNotSingleton : ∀ x, g₂CoreList n k m ++ tailBList n k m ≠ [x] := by
    intro x h; have : (g₂CoreList n k m ++ tailBList n k m).length = 1 := by rw [h]; simp
    have := g₂_cycle_length n k m; omega
  rw [b₁, g₂, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, tailBList, List.mem_map, List.mem_finRange]
  right; exact ⟨⟨0, hk⟩, trivial, by simp⟩

/-- c₁ is in the support of g₃ -/
theorem c₁_mem_support_g₃ (hm : m ≥ 1) : c₁ n k m hm ∈ (g₃ n k m).support := by
  have hNodup := g₃_list_nodup n k m
  have hNotSingleton : ∀ x, g₃CoreList n k m ++ tailCList n k m ≠ [x] := by
    intro x h; have : (g₃CoreList n k m ++ tailCList n k m).length = 1 := by rw [h]; simp
    have := g₃_cycle_length n k m; omega
  rw [c₁, g₃, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, tailCList, List.mem_map, List.mem_finRange]
  right; exact ⟨⟨0, hm⟩, trivial, by simp⟩

-- ============================================
-- SECTION 3: TAIL B/C IN BLOCK LEMMAS
-- ============================================

/-- If B contains b₁ and g₂(B) = B, then supp(g₂) ⊆ B -/
theorem lemma11_3_tail_B_in_block (hk : k ≥ 1) (B : Set (Omega n k m))
    (hB₁ : containsB₁ B hk) (hB : PreservesSet (g₂ n k m) B) :
    ((g₂ n k m).support : Set (Omega n k m)) ⊆ B := by
  have hCycle : (g₂ n k m).IsCycle := g₂_isCycle n k m
  have hMeet : ((g₂ n k m).support : Set (Omega n k m)) ∩ B ≠ ∅ := by
    rw [Set.nonempty_iff_ne_empty.symm]; use b₁ n k m hk; exact ⟨b₁_mem_support_g₂ hk, hB₁⟩
  rcases cycle_support_subset_or_disjoint hCycle hB with hSub | hDisj
  · exact hSub
  · exfalso; rw [Set.disjoint_iff_inter_eq_empty] at hDisj; exact hMeet hDisj

/-- If B contains c₁ and g₃(B) = B, then supp(g₃) ⊆ B -/
theorem lemma11_3_tail_C_in_block (hm : m ≥ 1) (B : Set (Omega n k m))
    (hC₁ : containsC₁ B hm) (hB : PreservesSet (g₃ n k m) B) :
    ((g₃ n k m).support : Set (Omega n k m)) ⊆ B := by
  have hCycle : (g₃ n k m).IsCycle := g₃_isCycle n k m
  have hMeet : ((g₃ n k m).support : Set (Omega n k m)) ∩ B ≠ ∅ := by
    rw [Set.nonempty_iff_ne_empty.symm]; use c₁ n k m hm; exact ⟨c₁_mem_support_g₃ hm, hC₁⟩
  rcases cycle_support_subset_or_disjoint hCycle hB with hSub | hDisj
  · exact hSub
  · exfalso; rw [Set.disjoint_iff_inter_eq_empty] at hDisj; exact hMeet hDisj

-- ============================================
-- SECTION 4: FIXED POINT LEMMAS FOR B/C
-- ============================================

/-- Tail B elements are not in supp(g₁) -/
theorem tailB_not_in_support_g₁ (_ : k ≥ 1) (i : Fin k) :
    (⟨6 + n + i.val, by omega⟩ : Omega n k m) ∉ (g₁ n k m).support := by
  simp only [g₁, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_notMem
  intro h; simp only [List.mem_append, g₁CoreList, tailAList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h <;> simp only [Fin.ext_iff] at h <;> omega
  · obtain ⟨j, _, hj⟩ := h; simp only [Fin.ext_iff] at hj; have := j.isLt; omega

/-- Tail B elements are not in supp(g₃) -/
theorem tailB_not_in_support_g₃ (_ : k ≥ 1) (i : Fin k) :
    (⟨6 + n + i.val, by omega⟩ : Omega n k m) ∉ (g₃ n k m).support := by
  simp only [g₃, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_notMem
  intro h; simp only [List.mem_append, g₃CoreList, tailCList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h <;> simp only [Fin.ext_iff] at h <;> omega
  · obtain ⟨j, _, hj⟩ := h; simp only [Fin.ext_iff] at hj; have := j.isLt; have := i.isLt; omega

/-- g₁ fixes b₁ -/
theorem g₁_fixes_b₁ (hk : k ≥ 1) : g₁ n k m (b₁ n k m hk) = b₁ n k m hk := by
  unfold b₁; exact fixed_outside_support _ _ (tailB_not_in_support_g₁ hk ⟨0, hk⟩)

/-- g₃ fixes b₁ -/
theorem g₃_fixes_b₁ (hk : k ≥ 1) : g₃ n k m (b₁ n k m hk) = b₁ n k m hk := by
  unfold b₁; exact fixed_outside_support _ _ (tailB_not_in_support_g₃ hk ⟨0, hk⟩)

/-- Tail C elements are not in supp(g₁) -/
theorem tailC_not_in_support_g₁ (_ : m ≥ 1) (i : Fin m) :
    (⟨6 + n + k + i.val, by omega⟩ : Omega n k m) ∉ (g₁ n k m).support := by
  simp only [g₁, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_notMem
  intro h; simp only [List.mem_append, g₁CoreList, tailAList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h <;> simp only [Fin.ext_iff] at h <;> omega
  · obtain ⟨j, _, hj⟩ := h; simp only [Fin.ext_iff] at hj; have := j.isLt; omega

/-- Tail C elements are not in supp(g₂) -/
theorem tailC_not_in_support_g₂ (_ : m ≥ 1) (i : Fin m) :
    (⟨6 + n + k + i.val, by omega⟩ : Omega n k m) ∉ (g₂ n k m).support := by
  simp only [g₂, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_notMem
  intro h; simp only [List.mem_append, g₂CoreList, tailBList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h <;> simp only [Fin.ext_iff] at h <;> omega
  · obtain ⟨j, _, hj⟩ := h; simp only [Fin.ext_iff] at hj; have := j.isLt; have := i.isLt; omega

/-- g₁ fixes c₁ -/
theorem g₁_fixes_c₁ (hm : m ≥ 1) : g₁ n k m (c₁ n k m hm) = c₁ n k m hm := by
  unfold c₁; exact fixed_outside_support _ _ (tailC_not_in_support_g₁ hm ⟨0, hm⟩)

/-- g₂ fixes c₁ -/
theorem g₂_fixes_c₁ (hm : m ≥ 1) : g₂ n k m (c₁ n k m hm) = c₁ n k m hm := by
  unfold c₁; exact fixed_outside_support _ _ (tailC_not_in_support_g₂ hm ⟨0, hm⟩)

-- ============================================
-- SECTION 5: CASE 2 STABILIZATION (k ≥ 1 and m ≥ 1)
-- ============================================

/-- **Case 2 Stabilization for k ≥ 1**: g₂(B) ≠ B forces g₁(B) = B and g₃(B) = B. -/
theorem case2_forces_stabilization_B (hk : k ≥ 1) (B : Set (Omega n k m))
    (hB₁ : b₁ n k m hk ∈ B)
    (h₁Disj : ¬PreservesSet (g₁ n k m) B → Disjoint (g₁ n k m '' B) B)
    (h₃Disj : ¬PreservesSet (g₃ n k m) B → Disjoint (g₃ n k m '' B) B) :
    PreservesSet (g₁ n k m) B ∧ PreservesSet (g₃ n k m) B := by
  constructor
  · by_contra hNotPres
    have hDisj := h₁Disj hNotPres
    have hFix : g₁ n k m (b₁ n k m hk) = b₁ n k m hk := g₁_fixes_b₁ hk
    have h_in_both := fixed_point_blocks_intersect (g₁ n k m) B (b₁ n k m hk) hB₁ hFix
    exact Set.disjoint_iff.mp hDisj h_in_both
  · by_contra hNotPres
    have hDisj := h₃Disj hNotPres
    have hFix : g₃ n k m (b₁ n k m hk) = b₁ n k m hk := g₃_fixes_b₁ hk
    have h_in_both := fixed_point_blocks_intersect (g₃ n k m) B (b₁ n k m hk) hB₁ hFix
    exact Set.disjoint_iff.mp hDisj h_in_both

/-- **Case 2 Stabilization for m ≥ 1**: g₃(B) ≠ B forces g₁(B) = B and g₂(B) = B. -/
theorem case2_forces_stabilization_C (hm : m ≥ 1) (B : Set (Omega n k m))
    (hC₁ : c₁ n k m hm ∈ B)
    (h₁Disj : ¬PreservesSet (g₁ n k m) B → Disjoint (g₁ n k m '' B) B)
    (h₂Disj : ¬PreservesSet (g₂ n k m) B → Disjoint (g₂ n k m '' B) B) :
    PreservesSet (g₁ n k m) B ∧ PreservesSet (g₂ n k m) B := by
  constructor
  · by_contra hNotPres
    have hDisj := h₁Disj hNotPres
    have hFix : g₁ n k m (c₁ n k m hm) = c₁ n k m hm := g₁_fixes_c₁ hm
    have h_in_both := fixed_point_blocks_intersect (g₁ n k m) B (c₁ n k m hm) hC₁ hFix
    exact Set.disjoint_iff.mp hDisj h_in_both
  · by_contra hNotPres
    have hDisj := h₂Disj hNotPres
    have hFix : g₂ n k m (c₁ n k m hm) = c₁ n k m hm := g₂_fixes_c₁ hm
    have h_in_both := fixed_point_blocks_intersect (g₂ n k m) B (c₁ n k m hm) hC₁ hFix
    exact Set.disjoint_iff.mp hDisj h_in_both

-- ============================================
-- SECTION 6: CASE 1b IMPOSSIBILITY (k ≥ 1 and m ≥ 1)
-- ============================================

theorem case1b_impossible_g₃ (B : Set (Omega n k m))
    (hSupp₂ : ((g₂ n k m).support : Set _) ⊆ B)
    (hDisj : Disjoint (g₃ n k m '' B) B) : False := by
  have h0_in_B : (⟨0, by omega⟩ : Omega n k m) ∈ B := hSupp₂ elem0_in_support_g₂
  have hFix : g₃ n k m (⟨0, by omega⟩ : Omega n k m) = ⟨0, by omega⟩ := g₃_fixes_elem0
  have h0_in_both := fixed_point_blocks_intersect (g₃ n k m) B _ h0_in_B hFix
  exact Set.disjoint_iff.mp hDisj h0_in_both

theorem case1b_impossible_g₁_from_g₂ (B : Set (Omega n k m))
    (hSupp₂ : ((g₂ n k m).support : Set _) ⊆ B)
    (hDisj : Disjoint (g₁ n k m '' B) B) : False := by
  have h4_in_B : (⟨4, by omega⟩ : Omega n k m) ∈ B := hSupp₂ elem4_in_support_g₂
  have hFix : g₁ n k m (⟨4, by omega⟩ : Omega n k m) = ⟨4, by omega⟩ := g₁_fixes_elem4
  have h4_in_both := fixed_point_blocks_intersect (g₁ n k m) B _ h4_in_B hFix
  exact Set.disjoint_iff.mp hDisj h4_in_both

theorem case1b_impossible_g₁ (B : Set (Omega n k m))
    (hSupp₃ : ((g₃ n k m).support : Set _) ⊆ B)
    (hDisj : Disjoint (g₁ n k m '' B) B) : False := by
  have h1_in_B : (⟨1, by omega⟩ : Omega n k m) ∈ B := hSupp₃ elem1_in_support_g₃
  have hFix : g₁ n k m (⟨1, by omega⟩ : Omega n k m) = ⟨1, by omega⟩ := g₁_fixes_elem1
  have h1_in_both := fixed_point_blocks_intersect (g₁ n k m) B _ h1_in_B hFix
  exact Set.disjoint_iff.mp hDisj h1_in_both

theorem case1b_impossible_g₂_from_g₃ (B : Set (Omega n k m))
    (hSupp₃ : ((g₃ n k m).support : Set _) ⊆ B)
    (hDisj : Disjoint (g₂ n k m '' B) B) : False := by
  have h2_in_B : (⟨2, by omega⟩ : Omega n k m) ∈ B := hSupp₃ elem2_in_support_g₃
  have hFix : g₂ n k m (⟨2, by omega⟩ : Omega n k m) = ⟨2, by omega⟩ := g₂_fixes_elem2
  have h2_in_both := fixed_point_blocks_intersect (g₂ n k m) B _ h2_in_B hFix
  exact Set.disjoint_iff.mp hDisj h2_in_both

-- ============================================
-- SECTION 7: CASE 2 IMPOSSIBILITY (k ≥ 1 and m ≥ 1)
-- ============================================

theorem case2_impossible_B (hk : k ≥ 1) (B : Set (Omega n k m))
    (BS : BlockSystemOn n k m) (hInv : IsHInvariant BS) (hB_in_BS : B ∈ BS.blocks)
    (hg₂Disj : Disjoint (g₂ n k m '' B) B)
    (hb₁_in_B : b₁ n k m hk ∈ B)
    (hg₁_pres : PreservesSet (g₁ n k m) B) (hg₃_pres : PreservesSet (g₃ n k m) B)
    (hBlock : ∀ j : ℕ, (g₂ n k m ^ j) '' B = B ∨ Disjoint ((g₂ n k m ^ j) '' B) B)
    (hNT_lower : 1 < B.ncard) : False := by
  have hB_subset_supp_g₂ : B ⊆ ↑(g₂ n k m).support := by
    intro x hxB
    by_contra hx_not_supp
    have hFix : g₂ n k m x = x := Equiv.Perm.notMem_support.mp hx_not_supp
    have hx_in_img : x ∈ g₂ n k m '' B := ⟨x, hxB, hFix⟩
    exact Set.disjoint_iff.mp hg₂Disj ⟨hx_in_img, hxB⟩

  have hB_disj_supp_g₁ : Disjoint (↑(g₁ n k m).support) B := by
    have hCyc : (g₁ n k m).IsCycle := g₁_isCycle n k m (by omega)
    rcases cycle_support_subset_or_disjoint hCyc hg₁_pres with hSub | hDisj
    · exfalso
      have h5_in_B : (⟨5, by omega⟩ : Omega n k m) ∈ B := hSub elem5_in_support_g₁
      have h5_not : (⟨5, by omega⟩ : Omega n k m) ∉ (g₂ n k m).support := elem5_not_in_support_g₂
      exact h5_not (hB_subset_supp_g₂ h5_in_B)
    · exact hDisj

  have hB_disj_supp_g₃ : Disjoint (↑(g₃ n k m).support) B := by
    have hCyc : (g₃ n k m).IsCycle := g₃_isCycle n k m
    rcases cycle_support_subset_or_disjoint hCyc hg₃_pres with hSub | hDisj
    · exfalso
      have h2_in_B : (⟨2, by omega⟩ : Omega n k m) ∈ B := hSub elem2_in_support_g₃
      have h2_not : (⟨2, by omega⟩ : Omega n k m) ∉ (g₂ n k m).support := elem2_not_in_support_g₂
      exact h2_not (hB_subset_supp_g₂ h2_in_B)
    · exact hDisj

  have hB_subset_tailB : ∀ x ∈ B, isTailB x :=
    case2_B_subset_tailB B hB_subset_supp_g₂ hB_disj_supp_g₁ hB_disj_supp_g₃

  by_cases hk1 : k = 1
  · -- k=1
    have hB_ncard_le_k : B.ncard ≤ k := by
      have hTailB_finite : Set.Finite {x : Omega n k m | isTailB x} := Set.toFinite _
      have hB_subset_tailB_set : B ⊆ {x : Omega n k m | isTailB x} := fun x hx => hB_subset_tailB x hx
      calc B.ncard ≤ {x : Omega n k m | isTailB x}.ncard := Set.ncard_le_ncard hB_subset_tailB_set hTailB_finite
        _ = k := by
          have h_eq : {x : Omega n k m | isTailB x} = Set.range (fun i : Fin k => (⟨6 + n + i.val, by omega⟩ : Omega n k m)) := by
            ext x; simp [Set.mem_setOf_eq, Set.mem_range, isTailB]; constructor <;> intro h
            · use ⟨x.val - 6 - n, by have := x.isLt; omega⟩; ext; simp; omega
            · obtain ⟨i, hi⟩ := h; rw [← hi]; constructor <;> simp <;> omega
          rw [h_eq, Set.ncard_range_of_injective]
          · simp
          · intro i j h; ext; simp at h; exact h
    omega
  · -- k >= 2: Use orbit argument
    have hk2 : k ≥ 2 := by omega
    -- Step 1: b₁ ∈ supp(g₂), g₂ is a cycle, so ∃ j mapping b₁ to 0
    have hb₁_in_supp : b₁ n k m hk ∈ (g₂ n k m).support := b₁_mem_support_g₂ hk
    have h0_in_supp : (⟨0, by omega⟩ : Omega n k m) ∈ (g₂ n k m).support := elem0_in_support_g₂
    have hCyc : (g₂ n k m).IsCycle := g₂_isCycle n k m
    rw [mem_support] at hb₁_in_supp h0_in_supp
    obtain ⟨j, hj⟩ := hCyc.exists_zpow_eq hb₁_in_supp h0_in_supp
    -- Step 2: Define B' = g₂^j '' B, containing 0
    let B' := (g₂ n k m ^ j) '' B
    have h0_in_B' : (⟨0, by omega⟩ : Omega n k m) ∈ B' := ⟨b₁ n k m hk, hb₁_in_B, hj⟩
    have hB'_card : B'.ncard = B.ncard := Set.ncard_image_of_injective _ (g₂ n k m ^ j).injective
    have hB'_card_gt_1 : 1 < B'.ncard := by rw [hB'_card]; exact hNT_lower
    -- Step 3: B' ⊆ supp(g₂)
    have hB'_subset_supp : B' ⊆ (g₂ n k m).support := by
      intro x hx; obtain ⟨y, hyB, hyx⟩ := hx
      have hy_in_supp : y ∈ (g₂ n k m).support := hB_subset_supp_g₂ hyB
      simp only [Finset.mem_coe] at hy_in_supp ⊢
      rw [← hyx]
      exact Equiv.Perm.zpow_apply_mem_support.mpr hy_in_supp
    -- Step 4: g₁(0) = 5 ∉ supp(g₂), so g₁(0) ∉ B'
    have hg₁_0_not_in_B' : g₁ n k m ⟨0, by omega⟩ ∉ B' := by
      rw [g₁_elem0_eq_elem5]; intro h_contra
      exact elem5_not_in_support_g₂ (hB'_subset_supp h_contra)
    -- Step 5: g₁(B') ≠ B' (since 0 ∈ B' but g₁(0) ∉ B')
    have hg₁_B'_ne : g₁ n k m '' B' ≠ B' := by
      intro h_eq
      have : g₁ n k m ⟨0, by omega⟩ ∈ g₁ n k m '' B' := Set.mem_image_of_mem _ h0_in_B'
      rw [h_eq] at this; exact hg₁_0_not_in_B' this
    -- Step 6: Find y ∈ B', y ≠ 0
    have hB'_has_other : ∃ y ∈ B', y ≠ (⟨0, by omega⟩ : Omega n k m) := by
      by_contra h; push_neg at h
      have hSub : B' ⊆ {⟨0, by omega⟩} := fun y hy => Set.mem_singleton_iff.mpr (h y hy)
      have hLe : B'.ncard ≤ 1 := Set.ncard_le_ncard hSub (Set.finite_singleton _) |>.trans
        (by simp [Set.ncard_singleton])
      omega
    obtain ⟨y, hy_in_B', hy_ne_0⟩ := hB'_has_other
    have hy_in_supp : y ∈ (g₂ n k m).support := hB'_subset_supp hy_in_B'
    -- Step 7: Case analysis on y
    -- y ∈ supp(g₂) = {0, 1, 3, 4} ∪ tailB, y ≠ 0
    -- If y ∈ {1, 4} ∪ tailB, g₁ fixes y
    by_cases hy_eq_1 : y = ⟨1, by omega⟩
    · -- y = 1: g₁ fixes 1
      have hg₁_fixes_y : g₁ n k m y = y := by rw [hy_eq_1]; exact g₁_fixes_elem1
      have hy_in_g₁B' : y ∈ g₁ n k m '' B' := by rw [← hg₁_fixes_y]; exact Set.mem_image_of_mem _ hy_in_B'
      have hB'_in_BS : B' ∈ BS.blocks := g₂_zpow_preserves_blocks BS hInv B hB_in_BS j
      have hg₁B'_in_BS : g₁ n k m '' B' ∈ BS.blocks := hInv.1 B' hB'_in_BS
      have hDisj : Disjoint B' (g₁ n k m '' B') := BS.isPartition.1 hB'_in_BS hg₁B'_in_BS hg₁_B'_ne.symm
      exact Set.disjoint_iff.mp hDisj ⟨hy_in_B', hy_in_g₁B'⟩
    · by_cases hy_eq_4 : y = ⟨4, by omega⟩
      · -- y = 4: g₁ fixes 4
        have hg₁_fixes_y : g₁ n k m y = y := by rw [hy_eq_4]; exact g₁_fixes_elem4
        have hy_in_g₁B' : y ∈ g₁ n k m '' B' := by rw [← hg₁_fixes_y]; exact Set.mem_image_of_mem _ hy_in_B'
        have hB'_in_BS : B' ∈ BS.blocks := g₂_zpow_preserves_blocks BS hInv B hB_in_BS j
        have hg₁B'_in_BS : g₁ n k m '' B' ∈ BS.blocks := hInv.1 B' hB'_in_BS
        have hDisj : Disjoint B' (g₁ n k m '' B') := BS.isPartition.1 hB'_in_BS hg₁B'_in_BS hg₁_B'_ne.symm
        exact Set.disjoint_iff.mp hDisj ⟨hy_in_B', hy_in_g₁B'⟩
      · -- y ≠ 0, 1, 4, so y = 3 or y ∈ tailB
        by_cases hy_tailB : isTailB y
        · -- y ∈ tailB: g₁ fixes tailB
          have hg₁_fixes_y : g₁ n k m y = y := g₁_fixes_tailB y hy_tailB
          have hy_in_g₁B' : y ∈ g₁ n k m '' B' := by rw [← hg₁_fixes_y]; exact Set.mem_image_of_mem _ hy_in_B'
          have hB'_in_BS : B' ∈ BS.blocks := g₂_zpow_preserves_blocks BS hInv B hB_in_BS j
          have hg₁B'_in_BS : g₁ n k m '' B' ∈ BS.blocks := hInv.1 B' hB'_in_BS
          have hDisj : Disjoint B' (g₁ n k m '' B') := BS.isPartition.1 hB'_in_BS hg₁B'_in_BS hg₁_B'_ne.symm
          exact Set.disjoint_iff.mp hDisj ⟨hy_in_B', hy_in_g₁B'⟩
        · -- y must be 3 (only remaining element in supp(g₂))
          -- y ∈ supp(g₂), y ≠ 0, 1, 4, y ∉ tailB → y = 3
          -- This case means B' ⊇ {0, 3}
          -- Sub-case analysis on |B'|
          by_cases hB'_card_eq_2 : B'.ncard = 2
          · -- B' = {0, 3}: Use g₂² block dichotomy argument (k ≥ 2)
            -- First establish y = 3 (since y ∈ supp(g₂), y ≠ 0, 1, 4, y ∉ tailB)
            have hy_eq_3 : y = ⟨3, by omega⟩ := by
              have hy_in_supp' : y ∈ (g₂ n k m).support := hB'_subset_supp hy_in_B'
              have h_y_cases : y.val = 0 ∨ y.val = 1 ∨ y.val = 3 ∨ y.val = 4 ∨ isTailB y := by
                simp only [g₂, Equiv.Perm.mem_support, ne_eq] at hy_in_supp'
                by_contra h_not; push_neg at h_not
                have hy_fixed : g₂ n k m y = y := by
                  apply List.formPerm_apply_of_notMem; intro hmem
                  simp only [List.mem_append, g₂CoreList, tailBList, List.mem_cons,
                    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at hmem
                  rcases hmem with hCore | hTail
                  · rcases hCore with h | h | h | h <;> (simp only [Fin.ext_iff] at h; omega)
                  · obtain ⟨i, _, hi⟩ := hTail
                    have : isTailB y := by simp only [isTailB, ← hi, Fin.val_mk]; omega
                    exact h_not.2.2.2.2 this
                exact hy_in_supp' hy_fixed
              rcases h_y_cases with h0 | h1 | h3 | h4 | hB
              · exact absurd (Fin.ext h0) hy_ne_0
              · exact absurd (Fin.ext h1) hy_eq_1
              · exact Fin.ext h3
              · exact absurd (Fin.ext h4) hy_eq_4
              · exact absurd hB hy_tailB
            -- Now {0, 3} ⊆ B' and B' = {0, 3}
            have h03_subset : ({⟨0, by omega⟩, ⟨3, by omega⟩} : Set (Omega n k m)) ⊆ B' := by
              intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
              rcases hz with rfl | rfl
              · exact h0_in_B'
              · rw [← hy_eq_3]; exact hy_in_B'
            have h03_card : ({⟨0, by omega⟩, ⟨3, by omega⟩} : Set (Omega n k m)).ncard = 2 := by
              rw [Set.ncard_pair]; exact fun h => by simp only [Fin.ext_iff] at h; omega
            have hB'_eq_03 : B' = {⟨0, by omega⟩, ⟨3, by omega⟩} := by
              apply (Set.eq_of_subset_of_ncard_le h03_subset _ (Set.toFinite _)).symm
              rw [hB'_card_eq_2, h03_card]
            -- Use set_0_3_not_g₂_closed: ∃ x ∈ {0, 3}, g₂²(x) ∉ {0, 3}
            obtain ⟨x, hx_in, hx_out⟩ := set_0_3_not_g₂_closed hk2
            -- Step 1: B' ∈ BS.blocks
            have hB'_in_BS : B' ∈ BS.blocks := g₂_zpow_preserves_blocks BS hInv B hB_in_BS j
            -- Step 2: g₂²(B') ∈ BS.blocks
            have hg₂sq_B'_in_BS : (g₂ n k m ^ (2 : ℕ)) '' B' ∈ BS.blocks := by
              have hg₂B'_in : (g₂ n k m) '' B' ∈ BS.blocks := hInv.2.1 _ hB'_in_BS
              have hg₂g₂B'_in : (g₂ n k m) '' ((g₂ n k m) '' B') ∈ BS.blocks := hInv.2.1 _ hg₂B'_in
              convert hg₂g₂B'_in using 1
              ext w; simp only [Set.mem_image, pow_two, Equiv.Perm.coe_mul, Function.comp_apply]
              constructor
              · rintro ⟨z, hz, rfl⟩; exact ⟨g₂ n k m z, ⟨z, hz, rfl⟩, rfl⟩
              · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩; exact ⟨w, hw, rfl⟩
            -- Step 3: g₂²(B') ≠ B'
            have hg₂sq_B'_ne : (g₂ n k m ^ (2 : ℕ)) '' B' ≠ B' := by
              intro h_eq
              have hx_in_B' : x ∈ B' := by rw [hB'_eq_03]; exact hx_in
              have hg₂sq_x_in : (g₂ n k m ^ (2 : ℕ)) x ∈ (g₂ n k m ^ (2 : ℕ)) '' B' :=
                Set.mem_image_of_mem _ hx_in_B'
              rw [h_eq] at hg₂sq_x_in
              have hx_out' : (g₂ n k m ^ (2 : ℕ)) x ∉ B' := by rw [hB'_eq_03]; exact hx_out
              exact hx_out' hg₂sq_x_in
            -- Step 4: g₂²(B') ∩ B' ≠ ∅ (g₂²(3) = 0 ∈ B')
            have h_not_disjoint : ¬Disjoint ((g₂ n k m ^ (2 : ℕ)) '' B') B' := by
              rw [Set.not_disjoint_iff]
              use ⟨0, by omega⟩
              constructor
              · -- 0 ∈ g₂²(B') because g₂²(3) = 0 and 3 ∈ B'
                rw [hB'_eq_03]
                have h3_in : (⟨3, by omega⟩ : Omega n k m) ∈ ({⟨0, by omega⟩, ⟨3, by omega⟩} : Set _) :=
                  Set.mem_insert_of_mem _ rfl
                use ⟨3, by omega⟩, h3_in
                exact g₂_pow2_elem3_eq_elem0
              · -- 0 ∈ B' = {0, 3}
                rw [hB'_eq_03]; exact Set.mem_insert _ _
            -- Step 5: Contradiction
            have hDichotomy := BS.isPartition.1 hg₂sq_B'_in_BS hB'_in_BS hg₂sq_B'_ne
            exact h_not_disjoint hDichotomy
          · -- |B'| > 2: Find z ∈ B' \ {0, 3}, which must be g₁-fixed
            have hB'_card_gt_2 : B'.ncard > 2 := by omega
            have h03_subset : ({⟨0, by omega⟩, ⟨3, by omega⟩} : Set (Omega n k m)) ⊆ B' := by
              intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
              rcases hz with rfl | rfl
              · exact h0_in_B'
              · -- y = 3 is the only remaining case, and y ∈ B'
                -- We need to show 3 ∈ B' using the fact that y must equal 3
                -- Since y ≠ 0, 1, 4, ¬tailB, and y ∈ supp(g₂), y must be 3
                have hy_in_supp' : y ∈ (g₂ n k m).support := hB'_subset_supp hy_in_B'
                have h_y_cases : y.val = 0 ∨ y.val = 1 ∨ y.val = 3 ∨ y.val = 4 ∨ isTailB y := by
                  simp only [g₂, Equiv.Perm.mem_support, ne_eq] at hy_in_supp'
                  by_contra h_not
                  push_neg at h_not
                  have hy_fixed : g₂ n k m y = y := by
                    apply List.formPerm_apply_of_notMem
                    intro hmem
                    simp only [List.mem_append, g₂CoreList, tailBList, List.mem_cons,
                      List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at hmem
                    rcases hmem with hCore | hTail
                    · rcases hCore with h | h | h | h <;> (simp only [Fin.ext_iff] at h; omega)
                    · obtain ⟨i, _, hi⟩ := hTail
                      have : isTailB y := by simp only [isTailB, ← hi, Fin.val_mk]; omega
                      exact h_not.2.2.2.2 this
                  exact hy_in_supp' hy_fixed
                rcases h_y_cases with h0 | h1 | h3 | h4 | hB
                · have : y = ⟨0, by omega⟩ := Fin.ext h0; exact absurd this hy_ne_0
                · have : y = ⟨1, by omega⟩ := Fin.ext h1; exact absurd this hy_eq_1
                · have hy_eq_3 : y = ⟨3, by omega⟩ := Fin.ext h3
                  rw [← hy_eq_3]; exact hy_in_B'
                · have : y = ⟨4, by omega⟩ := Fin.ext h4; exact absurd this hy_eq_4
                · exact absurd hB hy_tailB
            have hDiff_nonempty : (B' \ {⟨0, by omega⟩, ⟨3, by omega⟩}).Nonempty := by
              by_contra h; rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at h
              have := Set.ncard_le_ncard h (Set.toFinite _)
              have h03_card : ({⟨0, by omega⟩, ⟨3, by omega⟩} : Set (Omega n k m)).ncard = 2 := by
                rw [Set.ncard_pair]; exact fun h => by simp only [Fin.ext_iff] at h; omega
              rw [h03_card] at this; omega
            obtain ⟨z, hz_diff⟩ := hDiff_nonempty
            simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz_diff
            obtain ⟨hz_in_B', hz_ne_0, hz_ne_3⟩ := hz_diff
            -- z ∈ supp(g₂), z ≠ 0, 3, so z ∈ {1, 4} ∪ tailB, all g₁-fixed
            have hz_in_supp : z ∈ (g₂ n k m).support := hB'_subset_supp hz_in_B'
            have hg₁_fixes_z : g₁ n k m z = z := by
              have hz_cases : z.val = 0 ∨ z.val = 1 ∨ z.val = 3 ∨ z.val = 4 ∨ isTailB z := by
                simp only [g₂, Equiv.Perm.mem_support, ne_eq] at hz_in_supp
                by_contra h_not; push_neg at h_not
                have hz_fixed : g₂ n k m z = z := by
                  apply List.formPerm_apply_of_notMem
                  intro hmem
                  simp only [List.mem_append, g₂CoreList, tailBList, List.mem_cons,
                    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at hmem
                  rcases hmem with hCore | hTail
                  · rcases hCore with h | h | h | h <;> (simp only [Fin.ext_iff] at h; omega)
                  · obtain ⟨i, _, hi⟩ := hTail
                    have : isTailB z := by simp only [isTailB, ← hi, Fin.val_mk]; omega
                    exact h_not.2.2.2.2 this
                exact hz_in_supp hz_fixed
              rcases hz_cases with h0 | h1 | h3 | h4 | hB
              · have : z = ⟨0, by omega⟩ := Fin.ext h0; exact absurd this hz_ne_0
              · have hz_eq : z = ⟨1, by omega⟩ := Fin.ext h1; rw [hz_eq]; exact g₁_fixes_elem1
              · have : z = ⟨3, by omega⟩ := Fin.ext h3; exact absurd this hz_ne_3
              · have hz_eq : z = ⟨4, by omega⟩ := Fin.ext h4; rw [hz_eq]; exact g₁_fixes_elem4
              · exact g₁_fixes_tailB z hB
            have hz_in_g₁B' : z ∈ g₁ n k m '' B' := by rw [← hg₁_fixes_z]; exact Set.mem_image_of_mem _ hz_in_B'
            have hB'_in_BS : B' ∈ BS.blocks := g₂_zpow_preserves_blocks BS hInv B hB_in_BS j
            have hg₁B'_in_BS : g₁ n k m '' B' ∈ BS.blocks := hInv.1 B' hB'_in_BS
            have hDisj : Disjoint B' (g₁ n k m '' B') := BS.isPartition.1 hB'_in_BS hg₁B'_in_BS hg₁_B'_ne.symm
            exact Set.disjoint_iff.mp hDisj ⟨hz_in_B', hz_in_g₁B'⟩

theorem case2_impossible_C (hm : m ≥ 1) (B : Set (Omega n k m))
    (BS : BlockSystemOn n k m) (hInv : IsHInvariant BS) (hB_in_BS : B ∈ BS.blocks)
    (hg₃Disj : Disjoint (g₃ n k m '' B) B)
    (hc₁_in_B : c₁ n k m hm ∈ B)
    (hg₁_pres : PreservesSet (g₁ n k m) B) (hg₂_pres : PreservesSet (g₂ n k m) B)
    (hBlock : ∀ j : ℕ, (g₃ n k m ^ j) '' B = B ∨ Disjoint ((g₃ n k m ^ j) '' B) B)
    (hNT_lower : 1 < B.ncard) : False := by
  have hB_subset_supp_g₃ : B ⊆ ↑(g₃ n k m).support := by
    intro x hxB
    by_contra hx_not_supp
    have hFix : g₃ n k m x = x := Equiv.Perm.notMem_support.mp hx_not_supp
    have hx_in_img : x ∈ g₃ n k m '' B := ⟨x, hxB, hFix⟩
    exact Set.disjoint_iff.mp hg₃Disj ⟨hx_in_img, hxB⟩

  have hB_disj_supp_g₁ : Disjoint (↑(g₁ n k m).support) B := by
    have hCyc : (g₁ n k m).IsCycle := g₁_isCycle n k m (by omega)
    rcases cycle_support_subset_or_disjoint hCyc hg₁_pres with hSub | hDisj
    · exfalso
      have h0_in_B : (⟨0, by omega⟩ : Omega n k m) ∈ B := hSub elem0_in_support_g₁
      have h0_not : (⟨0, by omega⟩ : Omega n k m) ∉ (g₃ n k m).support := elem0_not_in_support_g₃
      exact h0_not (hB_subset_supp_g₃ h0_in_B)
    · exact hDisj

  have hB_disj_supp_g₂ : Disjoint (↑(g₂ n k m).support) B := by
    have hCyc : (g₂ n k m).IsCycle := g₂_isCycle n k m
    rcases cycle_support_subset_or_disjoint hCyc hg₂_pres with hSub | hDisj
    · exfalso
      have h3_in_B : (⟨3, by omega⟩ : Omega n k m) ∈ B := hSub elem3_in_support_g₂'
      have h3_not : (⟨3, by omega⟩ : Omega n k m) ∉ (g₃ n k m).support := elem3_not_in_support_g₃
      exact h3_not (hB_subset_supp_g₃ h3_in_B)
    · exact hDisj

  have hB_subset_tailC : ∀ x ∈ B, isTailC x :=
    case2_C_subset_tailC B hB_subset_supp_g₃ hB_disj_supp_g₁ hB_disj_supp_g₂

  by_cases hm1 : m = 1
  · have hB_ncard_le_m : B.ncard ≤ m := by
      have hTailC_finite : Set.Finite {x : Omega n k m | isTailC x} := Set.toFinite _
      have hB_subset_tailC_set : B ⊆ {x : Omega n k m | isTailC x} := fun x hx => hB_subset_tailC x hx
      calc B.ncard ≤ {x : Omega n k m | isTailC x}.ncard := Set.ncard_le_ncard hB_subset_tailC_set hTailC_finite
        _ = m := by
          have h_eq : {x : Omega n k m | isTailC x} = Set.range (fun i : Fin m => (⟨6 + n + k + i.val, by omega⟩ : Omega n k m)) := by
            ext x; simp [Set.mem_setOf_eq, Set.mem_range, isTailC]; constructor <;> intro h
            · use ⟨x.val - 6 - n - k, by have := x.isLt; omega⟩; ext; simp; omega
            · obtain ⟨i, hi⟩ := h; rw [← hi]; simp
          rw [h_eq, Set.ncard_range_of_injective]
          · simp
          · intro i j hij; simp only [Fin.ext_iff] at hij ⊢; omega
    omega
  · -- m >= 2
    have hm2 : m ≥ 2 := by omega
    -- Step 1: Find j such that g₃^j(c₁) = 4
    have hc₁_in_supp : c₁ n k m hm ∈ (g₃ n k m).support := c₁_mem_support_g₃ hm
    have h4_in_supp : (⟨4, by omega⟩ : Omega n k m) ∈ (g₃ n k m).support := elem4_in_support_g₃
    have hCyc : (g₃ n k m).IsCycle := g₃_isCycle n k m
    rw [mem_support] at hc₁_in_supp h4_in_supp
    obtain ⟨j, hj⟩ := hCyc.exists_zpow_eq hc₁_in_supp h4_in_supp
    -- Step 2: Define B' and establish basic properties
    let B' := (g₃ n k m ^ j) '' B
    have h4_in_B' : (⟨4, by omega⟩ : Omega n k m) ∈ B' := ⟨c₁ n k m hm, hc₁_in_B, hj⟩
    have hB'_card : B'.ncard = B.ncard := Set.ncard_image_of_injective _ (g₃ n k m ^ j).injective
    have hB'_card_gt_1 : 1 < B'.ncard := by rw [hB'_card]; exact hNT_lower
    have hB'_subset_supp : B' ⊆ (g₃ n k m).support := by
      intro x hx; obtain ⟨y, hyB, hyx⟩ := hx
      have hy_in_supp : y ∈ (g₃ n k m).support := hB_subset_supp_g₃ hyB
      simp only [Finset.mem_coe] at hy_in_supp ⊢
      rw [← hyx]; exact Equiv.Perm.zpow_apply_mem_support.mpr hy_in_supp
    have hB'_in_BS : B' ∈ BS.blocks := g₃_zpow_preserves_blocks BS hInv B hB_in_BS j
    -- Step 3: Show g₂(B') ≠ B'
    have hg₂_4_not_in_B' : g₂ n k m ⟨4, by omega⟩ ∉ B' := by
      rw [OrbitCore.g₂_elem4_eq_elem0']; intro h_contra
      exact elem0_not_in_support_g₃ (hB'_subset_supp h_contra)
    have hg₂_B'_ne : g₂ n k m '' B' ≠ B' := by
      intro h_eq
      have : g₂ n k m ⟨4, by omega⟩ ∈ g₂ n k m '' B' := Set.mem_image_of_mem _ h4_in_B'
      rw [h_eq] at this; exact hg₂_4_not_in_B' this
    -- Step 4: Case analysis - find g₂-fixed element or handle B' = {1, 4}
    by_cases hB'_small : ∃ z ∈ B', z ≠ (⟨1, by omega⟩ : Omega n k m) ∧ z ≠ (⟨4, by omega⟩ : Omega n k m)
    · -- Case 4a: ∃ z ∈ B' with z ∉ {1, 4}
      obtain ⟨z, hz_in_B', hz_ne_1, hz_ne_4⟩ := hB'_small
      -- z ∈ supp(g₃) \ {1, 4} = {2, 5} ∪ tailC, all g₂-fixed
      have hz_in_supp : z ∈ (g₃ n k m).support := hB'_subset_supp hz_in_B'
      have hg₂_fixes_z : g₂ n k m z = z := by
        have hz_cases : z.val = 1 ∨ z.val = 2 ∨ z.val = 4 ∨ z.val = 5 ∨ isTailC z := by
          simp only [g₃, Equiv.Perm.mem_support, ne_eq] at hz_in_supp
          by_contra h_not; push_neg at h_not
          have hz_fixed : g₃ n k m z = z := by
            apply List.formPerm_apply_of_notMem
            intro hmem
            simp only [List.mem_append, g₃CoreList, tailCList, List.mem_cons,
              List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at hmem
            rcases hmem with hCore | hTail
            · rcases hCore with h | h | h | h <;> (simp only [Fin.ext_iff] at h; omega)
            · obtain ⟨i, _, hi⟩ := hTail
              have : isTailC z := by simp only [isTailC, ← hi, Fin.val_mk]; omega
              exact h_not.2.2.2.2 this
          exact hz_in_supp hz_fixed
        rcases hz_cases with h1 | h2 | h4 | h5 | hC
        · exact absurd (Fin.ext h1) hz_ne_1
        · have hz_eq : z = ⟨2, by omega⟩ := Fin.ext h2; rw [hz_eq]; exact g₂_fixes_elem2
        · exact absurd (Fin.ext h4) hz_ne_4
        · have hz_eq : z = ⟨5, by omega⟩ := Fin.ext h5; rw [hz_eq]; exact g₂_fixes_elem5
        · exact g₂_fixes_tailC z hC
      have hz_in_g₂B' : z ∈ g₂ n k m '' B' := by rw [← hg₂_fixes_z]; exact Set.mem_image_of_mem _ hz_in_B'
      have hg₂B'_in_BS : g₂ n k m '' B' ∈ BS.blocks := hInv.2.1 B' hB'_in_BS
      have hDisj : Disjoint B' (g₂ n k m '' B') := BS.isPartition.1 hB'_in_BS hg₂B'_in_BS hg₂_B'_ne.symm
      exact Set.disjoint_iff.mp hDisj ⟨hz_in_B', hz_in_g₂B'⟩
    · -- Case 4b: B' ⊆ {1, 4}, so B' = {1, 4}
      push_neg at hB'_small
      -- hB'_small : ∀ z ∈ B', z ≠ 1 → z = 4  (implication form)
      have h1_in_B' : (⟨1, by omega⟩ : Omega n k m) ∈ B' := by
        have hB'_has_other : ∃ y ∈ B', y ≠ (⟨4, by omega⟩ : Omega n k m) := by
          by_contra h; push_neg at h
          have hSub : B' ⊆ {⟨4, by omega⟩} := fun y hy => Set.mem_singleton_iff.mpr (h y hy)
          have hLe : B'.ncard ≤ 1 := Set.ncard_le_ncard hSub (Set.finite_singleton _) |>.trans
            (by simp [Set.ncard_singleton])
          omega
        obtain ⟨y, hy_in, hy_ne_4⟩ := hB'_has_other
        by_cases hy_eq_1 : y = ⟨1, by omega⟩
        · rw [← hy_eq_1]; exact hy_in
        · exact absurd (hB'_small y hy_in hy_eq_1) hy_ne_4
      have hB'_eq_14 : B' = {⟨1, by omega⟩, ⟨4, by omega⟩} := by
        ext z; constructor
        · intro hz
          by_cases h1 : z = ⟨1, by omega⟩
          · simp [h1]
          · simp [hB'_small z hz h1]
        · intro hz; simp at hz; rcases hz with rfl | rfl <;> assumption
      -- Sub-step 4b.2: use hBlock to derive contradiction
      -- Case split on m = 2 vs m ≥ 3
      by_cases hm_eq_2 : m = 2
      · -- Case m = 2: g₃²(c₁) = 2, but 2 ∉ tailC, contradicting B ⊆ tailC
        have hg₃_pow2_c₁ : (g₃ n k m ^ (2 : ℕ)) (c₁ n k m hm) = ⟨2, by omega⟩ := by
          simp only [c₁]; exact OrbitCore.g₃_pow2_c₁_eq_elem2 hm_eq_2
        have h2_not_tailC : ¬isTailC (⟨2, by omega⟩ : Omega n k m) := by
          simp only [isTailC]; omega
        -- g₃²(c₁) ∈ g₃²(B) since c₁ ∈ B
        have hc₁_in_g₃pow2B : (g₃ n k m ^ (2 : ℕ)) (c₁ n k m hm) ∈ ⇑(g₃ n k m ^ (2 : ℕ)) '' B :=
          Set.mem_image_of_mem _ hc₁_in_B
        -- By hBlock 2: either g₃²(B) = B or Disjoint
        rcases hBlock 2 with hEq | hDisj
        · -- If g₃²(B) = B, then 2 ∈ B
          rw [hEq] at hc₁_in_g₃pow2B
          have h2_in_B : (⟨2, by omega⟩ : Omega n k m) ∈ B := by
            rw [← hg₃_pow2_c₁]; exact hc₁_in_g₃pow2B
          exact h2_not_tailC (hB_subset_tailC _ h2_in_B)
        · -- If Disjoint: B = {c₁, c₂} but g₃(c₁) = c₂ ∈ B, contradicting hg₃Disj
          -- Since m = 2, tailC = {c₁, c₂} and |B| = 2, B ⊆ tailC implies B = {c₁, c₂}
          have hc₂ : (⟨7 + n + k, by omega⟩ : Omega n k m) ∈ B := by
            have hTailC_eq : {x : Omega n k m | isTailC x} = {c₁ n k m hm, ⟨7 + n + k, by omega⟩} := by
              ext x; simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
              constructor
              · intro hx; simp only [isTailC, c₁] at hx ⊢
                rcases Nat.lt_succ_iff_lt_or_eq.mp (by omega : x.val < 6 + n + k + 2) with h | h
                · left; ext; simp only [Fin.val_mk]; omega
                · right; ext; simp only [Fin.val_mk]; omega
              · intro hx; rcases hx with rfl | rfl
                · simp only [isTailC, c₁, hm_eq_2]; omega
                · simp only [isTailC, hm_eq_2]; constructor <;> omega
            have hB_sub : B ⊆ {c₁ n k m hm, ⟨7 + n + k, by omega⟩} := by
              intro x hx; rw [← hTailC_eq]; exact hB_subset_tailC x hx
            have hc₁_ne_c₂ : c₁ n k m hm ≠ (⟨7 + n + k, by omega⟩ : Omega n k m) := by
              simp only [c₁, ne_eq, Fin.ext_iff, Fin.val_mk]; omega
            have hCard2 : ({c₁ n k m hm, ⟨7 + n + k, by omega⟩} : Set (Omega n k m)).ncard = 2 := by
              rw [Set.ncard_pair hc₁_ne_c₂]
            have hB_eq : B = {c₁ n k m hm, ⟨7 + n + k, by omega⟩} := by
              apply Set.eq_of_subset_of_ncard_le hB_sub
              rw [hCard2]; exact hNT_lower
            rw [hB_eq]; simp
          -- g₃(c₁) = c₂, so c₂ ∈ g₃(B)
          have hg₃_c₁ : g₃ n k m (c₁ n k m hm) = ⟨7 + n + k, by omega⟩ := by
            simp only [c₁]
            have h := @OrbitCore.g₃_c₁_eq_c₂ n k m (by omega : m ≥ 2)
            convert h using 2 <;> omega
          have hc₂_in_g₃B : (⟨7 + n + k, by omega⟩ : Omega n k m) ∈ g₃ n k m '' B := by
            rw [← hg₃_c₁]; exact Set.mem_image_of_mem _ hc₁_in_B
          -- But c₂ ∈ B, contradicting Disjoint g₃(B) B
          exact Set.disjoint_iff.mp hg₃Disj ⟨hc₂_in_g₃B, hc₂⟩
      · -- Case m ≥ 3
        have hm3 : m ≥ 3 := by omega
        -- g₃(c₁) = c₂
        have hg₃_c₁ : g₃ n k m (c₁ n k m hm) = ⟨6 + n + k + 1, by omega⟩ := by
          simp only [c₁]
          exact @OrbitCore.g₃_c₁_eq_c₂ n k m (by omega : m ≥ 2)
        -- Case split: is c₂ in B?
        by_cases hc₂_in_B : (⟨6 + n + k + 1, by omega⟩ : Omega n k m) ∈ B
        · -- c₂ ∈ B: contradiction with hg₃Disj
          have hc₂_in_g₃B : (⟨6 + n + k + 1, by omega⟩ : Omega n k m) ∈ g₃ n k m '' B := by
            rw [← hg₃_c₁]; exact Set.mem_image_of_mem _ hc₁_in_B
          exact Set.disjoint_iff.mp hg₃Disj ⟨hc₂_in_g₃B, hc₂_in_B⟩
        · -- c₂ ∉ B: use hBlock 2 to get contradiction
          -- g₃²(c₁) = c₃, which is a tailC element
          have hg₃_pow2_c₁ : (g₃ n k m ^ (2 : ℕ)) (c₁ n k m hm) = ⟨6 + n + k + 2, by omega⟩ := by
            simp only [c₁]; exact OrbitCore.g₃_pow2_c₁_eq_c₃ hm3
          have hc₃_in_g₃pow2B : (⟨6 + n + k + 2, by omega⟩ : Omega n k m) ∈ ⇑(g₃ n k m ^ (2 : ℕ)) '' B := by
            rw [← hg₃_pow2_c₁]; exact Set.mem_image_of_mem _ hc₁_in_B
          -- By hBlock 2: either g₃²(B) = B or Disjoint
          rcases hBlock 2 with hEq | hDisj2
          · -- Equality case: g₃²(B) = B implies c₃ ∈ B
            -- Then B = {c₁, c₃} and g₃²(B) = {c₃, g₃²(c₃)}
            -- But g₃²(c₃) ∉ {c₁, c₃} since g₃ cycle length 4+m, 2∤4+m, 4∤4+m
            have hc₃_in_B : (⟨6 + n + k + 2, by omega⟩ : Omega n k m) ∈ B := by
              rw [← hEq]; exact hc₃_in_g₃pow2B
            -- c₃ is a tailC element
            have hc₃_tailC : isTailC (⟨6 + n + k + 2, by omega⟩ : Omega n k m) := by
              simp only [isTailC]; omega
            -- Since |B| = 2, c₁ ∈ B, c₃ ∈ B, c₁ ≠ c₃, we have B = {c₁, c₃}
            have hc₁_ne_c₃ : c₁ n k m hm ≠ (⟨6 + n + k + 2, by omega⟩ : Omega n k m) := by
              simp only [c₁, ne_eq, Fin.ext_iff, Fin.val_mk]; omega
            have hB_sub : B ⊆ {c₁ n k m hm, ⟨6 + n + k + 2, by omega⟩} := by
              intro x hx
              have hx_tailC := hB_subset_tailC x hx
              -- x is tailC, and |B| = 2 with c₁, c₃ ∈ B
              -- Since c₂ ∉ B and x ∈ B, if x ≠ c₁ and x ≠ c₃, B would have > 2 elements
              by_contra hx_not
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx_not
              -- B contains c₁, c₃, x with x ≠ c₁, x ≠ c₃
              have h3 : ({c₁ n k m hm, ⟨6 + n + k + 2, by omega⟩, x} : Set (Omega n k m)).ncard ≥ 3 := by
                rw [Set.ncard_insert_of_not_mem, Set.ncard_insert_of_not_mem, Set.ncard_singleton]
                · simp only [Set.mem_singleton_iff]; exact hx_not.2
                · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
                  exact ⟨hc₁_ne_c₃, hx_not.2.symm⟩
              have hB_ge_3 : B.ncard ≥ 3 := by
                apply Set.ncard_le_ncard (s := {c₁ n k m hm, ⟨6 + n + k + 2, by omega⟩, x})
                · intro y hy
                  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
                  rcases hy with rfl | rfl | rfl <;> assumption
                · exact Set.toFinite B
              omega
            have hB_eq : B = {c₁ n k m hm, ⟨6 + n + k + 2, by omega⟩} := by
              apply Set.eq_of_subset_of_ncard_le hB_sub
              rw [Set.ncard_pair hc₁_ne_c₃]; exact hNT_lower
            -- Now g₃²(B) = {g₃²(c₁), g₃²(c₃)} = {c₃, g₃²(c₃)}
            -- For g₃²(B) = B, need g₃²(c₃) ∈ {c₁, c₃}
            -- But g₃ is a cycle of length 4+m, and 2,4 don't divide 4+m for m≥1
            -- So g₃²(c₃) ≠ c₃ and g₃⁴(c₁) ≠ c₁
            -- g₃²(c₃) = c₁ would mean g₃⁴(c₁) = c₁, contradiction
            have hOrd : orderOf (g₃ n k m) = (g₃ n k m).support.card := hCyc.orderOf
            have hCycLen : (g₃ n k m).support.card = 4 + m := AfTests.SignAnalysis.g₃_support_card n k m
            have h4m_gt_4 : 4 + m > 4 := by omega
            have h4m_gt_2 : 4 + m > 2 := by omega
            -- g₃²(c₃) ≠ c₃: would require g₃² = 1, but orderOf g₃ = 4+m > 2
            have hg₃2_c₃_ne_c₃ : (g₃ n k m ^ (2 : ℕ)) (⟨6 + n + k + 2, by omega⟩ : Omega n k m) ≠
                ⟨6 + n + k + 2, by omega⟩ := by
              intro heq
              have hc₃_in_supp : (⟨6 + n + k + 2, by omega⟩ : Omega n k m) ∈ (g₃ n k m).support :=
                hB_subset_supp_g₃ hc₃_in_B
              -- g₃²(c₃) = c₃ with c₃ in support implies g₃² = 1 (by IsCycle.pow_eq_one_iff)
              have hpow2_eq_one : g₃ n k m ^ (2 : ℕ) = 1 := by
                rw [hCyc.pow_eq_one_iff]
                exact ⟨⟨6 + n + k + 2, by omega⟩, Equiv.Perm.mem_support.mp hc₃_in_supp, heq⟩
              -- g₃² = 1 implies orderOf g₃ | 2
              have hdvd : orderOf (g₃ n k m) ∣ 2 := orderOf_dvd_of_pow_eq_one hpow2_eq_one
              rw [hOrd, hCycLen] at hdvd
              have hle := Nat.le_of_dvd (by norm_num : (2 : ℕ) > 0) hdvd
              omega
            -- g₃²(c₃) ≠ c₁: would require g₃⁴(c₁) = c₁, but orderOf g₃ = 4+m doesn't divide 4
            have hg₃2_c₃_ne_c₁ : (g₃ n k m ^ (2 : ℕ)) (⟨6 + n + k + 2, by omega⟩ : Omega n k m) ≠
                c₁ n k m hm := by
              intro heq
              -- g₃²(c₃) = c₁ means g₃²(g₃²(c₁)) = c₁, i.e., g₃⁴(c₁) = c₁
              have hg₃4_c₁ : (g₃ n k m ^ (4 : ℕ)) (c₁ n k m hm) = c₁ n k m hm := by
                have h4eq : (4 : ℕ) = 2 + 2 := by norm_num
                calc (g₃ n k m ^ (4 : ℕ)) (c₁ n k m hm)
                    = (g₃ n k m ^ (2 + 2)) (c₁ n k m hm) := by rw [h4eq]
                    _ = (g₃ n k m ^ 2 * g₃ n k m ^ 2) (c₁ n k m hm) := by rw [pow_add]
                    _ = (g₃ n k m ^ (2 : ℕ)) ((g₃ n k m ^ (2 : ℕ)) (c₁ n k m hm)) := by
                        simp only [Equiv.Perm.coe_mul, Function.comp_apply]
                    _ = (g₃ n k m ^ (2 : ℕ)) (⟨6 + n + k + 2, by omega⟩) := by rw [hg₃_pow2_c₁]
                    _ = c₁ n k m hm := heq
              have hc₁_in_supp : c₁ n k m hm ∈ (g₃ n k m).support := hB_subset_supp_g₃ hc₁_in_B
              -- g₃⁴(c₁) = c₁ with c₁ in support implies g₃⁴ = 1 (by IsCycle.pow_eq_one_iff)
              have hpow4_eq_one : g₃ n k m ^ (4 : ℕ) = 1 := by
                rw [hCyc.pow_eq_one_iff]
                exact ⟨c₁ n k m hm, Equiv.Perm.mem_support.mp hc₁_in_supp, hg₃4_c₁⟩
              have hdvd : orderOf (g₃ n k m) ∣ 4 := orderOf_dvd_of_pow_eq_one hpow4_eq_one
              rw [hOrd, hCycLen] at hdvd
              have hle := Nat.le_of_dvd (by norm_num : (4 : ℕ) > 0) hdvd
              omega
            -- Now: g₃²(B) = {c₃, g₃²(c₃)} but g₃²(c₃) ∉ {c₁, c₃} = B
            have hg₃2_c₃_not_in_B : (g₃ n k m ^ (2 : ℕ)) (⟨6 + n + k + 2, by omega⟩ : Omega n k m) ∉ B := by
              rw [hB_eq]; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
              push_neg; exact ⟨hg₃2_c₃_ne_c₁, hg₃2_c₃_ne_c₃⟩
            -- But g₃²(c₃) ∈ g₃²(B) = B by hEq
            have hg₃2_c₃_in_g₃2B : (g₃ n k m ^ (2 : ℕ)) (⟨6 + n + k + 2, by omega⟩ : Omega n k m) ∈
                ⇑(g₃ n k m ^ (2 : ℕ)) '' B := Set.mem_image_of_mem _ hc₃_in_B
            rw [hEq] at hg₃2_c₃_in_g₃2B
            exact hg₃2_c₃_not_in_B hg₃2_c₃_in_g₃2B
          · -- Disjoint case: c₃ ∉ B
            sorry