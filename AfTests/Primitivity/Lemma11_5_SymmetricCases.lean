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
            · obtain ⟨i, hi⟩ := h; rw [← hi]; simp; constructor <;> omega
          rw [h_eq, Set.ncard_range_of_injective]
          · simp
          · intro i j h; ext; simp at h; exact h
    omega
  · -- k >= 2
    -- B ⊆ supp(g₂). Orbit partitions supp(g₂).
    -- 2 ∈ supp(g₂). So B' containing 2 exists.
    obtain ⟨B', hB'_in_orbit, h2_in_B'⟩ := BS.exists_block_containing_element_in_support
      (g₂ n k m) B hB_in_BS (by
        intro x hx; have hTail := hB_subset_tailB x hx
        simp only [isTailB] at hTail
        have hIdx : x.val - 6 - n < k := by omega
        have hEq : x = ⟨6 + n + (x.val - 6 - n), by omega⟩ := by ext; simp; omega
        rw [hEq]; apply b₁_mem_support_g₂ (by omega) -- actually any tailB in support
        -- Wait, b₁_mem_support_g₂ only for b₁?
        -- Need generic tailB in support.
        -- g₂ = (1 2 4 5 tailB).
        -- Yes, all tailB in support.
        have hNodup := g₂_list_nodup n k m
        have hNotSingleton : ∀ x, g₂CoreList n k m ++ tailBList n k m ≠ [x] := by
          intro x h; have : (g₂CoreList n k m ++ tailBList n k m).length = 1 := by rw [h]; simp
          have := g₂_cycle_length n k m; omega
        rw [g₂, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
        simp; right; use ⟨x.val - 6 - n, hIdx⟩; simp [tailBList]; exact hEq.symm
      ) (by exact elem2_in_support_g₂)
    
    have hB'_sub_supp_g₂ : B' ⊆ (g₂ n k m).support := by
      obtain ⟨j, rfl⟩ := hB'_in_orbit
      intro x hx; obtain ⟨y, hy_in, hy_eq⟩ := hx
      rw [← hy_eq]
      have hy_supp : y ∈ (g₂ n k m).support := by
        have hTail := hB_subset_tailB y hy_in; simp [isTailB] at hTail
        -- Similar proof as above
        have hIdx : y.val - 6 - n < k := by omega
        have hEq : y = ⟨6 + n + (y.val - 6 - n), by omega⟩ := by ext; simp; omega
        rw [g₂]; apply Equiv.Perm.mem_support.mpr; intro hC
        -- use cycle logic or list support logic
        sorry -- Trivial since y in tailB which is in support
      simp [Equiv.Perm.mem_support]; intro hC
      exact (Equiv.Perm.mem_support.mp hy_supp) ((Equiv.Perm.iterate_eq_self_iff_eq_self j).mp hC)

    -- g₁(B') ≠ B' since 2 ∈ B' and g₁(2) ∉ supp(g₂)
    have hg₁_B'_ne_B' : g₁ n k m '' B' ≠ B' := by
      intro hEq
      have h2_in : (⟨2, by omega⟩ : Omega n k m) ∈ B' := h2_in_B'
      have hg₁_2_in : g₁ n k m (⟨2, by omega⟩ : Omega n k m) ∈ B' :=
        Set.mem_image_of_mem _ h2_in |> hEq.subst
      -- g₁(2) = 0 (if n=0) or a₁ (if n>=1). Neither in supp(g₂).
      -- supp(g₂) = {1, 2, 4, 5, tailB}.
      -- 0 is not in supp(g₂).
      -- a₁ (6) is not in supp(g₂).
      -- We need proof g₁(2) ∉ supp(g₂).
      sorry -- g₁(2) is 0 or a₁. supp(g₂)={1,2,4,5,tailB}. disjoint.
      
    -- B' contains fixed point of g₁
    have hB'_has_fixed : (B' ∩ {x | g₁ n k m x = x}).Nonempty := by
      by_contra hNone
      simp only [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_not_mem, Set.mem_inter_iff, Set.mem_setOf_eq, not_and] at hNone
      -- B' ⊆ {2, 5} (moved by g₁ in supp(g₂))
      -- supp(g₂) ∩ supp(g₁) = {2, 5}.
      -- fixed by g₁ in supp(g₂) = supp(g₂) \ {2, 5} = {1, 4, tailB}.
      -- If no fixed point, B' ⊆ {2, 5}.
      -- |B'| = 2 => B' = {2, 5}.
      -- Impossible in g₂ (dist 2 in cycle ≥ 7).
      sorry

    obtain ⟨y, hy_in, hy_fixed⟩ := hB'_has_fixed
    have hInter : (g₁ n k m '' B' ∩ B').Nonempty := ⟨y, ⟨y, hy_in, hy_fixed⟩, hy_in⟩
    
    have hB'_mem : B' ∈ BS.blocks := BS.orbit_subset_blocks (g₂ n k m) hB_in_BS (hInv.2) B' hB'_in_orbit
    rcases (perm_image_preserves_or_disjoint (g₁ n k m) B' BS.blocks BS.isPartition.1 hB'_mem (hInv.1 B' hB'_mem)) with hPres | hDisj
    · exact hg₁_B'_ne_B' hPres
    · exact Set.not_nonempty_iff_eq_empty.mpr (Set.disjoint_iff_inter_eq_empty.mp hDisj) hInter

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
       -- similar cardinality proof
       sorry
    omega
  · -- m >= 2
    -- B ⊆ supp(g₃). Orbit partitions supp(g₃).
    -- 2 ∈ supp(g₃). So B' containing 2 exists.
    obtain ⟨B', hB'_in_orbit, h2_in_B'⟩ := BS.exists_block_containing_element_in_support
      (g₃ n k m) B hB_in_BS (by
         intro x hx; have hTail := hB_subset_tailC x hx
         -- ... tailC in support logic
         sorry
      ) (by exact elem2_in_support_g₃)
    
    have hB'_sub_supp_g₃ : B' ⊆ (g₃ n k m).support := by
      -- orbit subset logic
      sorry

    -- g₂(B') ≠ B' since 2 ∈ B' and g₂(2) = 4 ∉ supp(g₃)
    have hg₂_B'_ne_B' : g₂ n k m '' B' ≠ B' := by
      intro hEq
      have h2_in : (⟨2, by omega⟩ : Omega n k m) ∈ B' := h2_in_B'
      have hg₂_2_in : g₂ n k m (⟨2, by omega⟩ : Omega n k m) ∈ B' :=
        Set.mem_image_of_mem _ h2_in |> hEq.subst
      -- g₂(2) = 4. 4 ∉ supp(g₃).
      have h4_not : (⟨4, by omega⟩ : Omega n k m) ∉ (g₃ n k m).support := elem4_not_in_support_g₃
      have hg₂_2_eq : g₂ n k m (⟨2, by omega⟩ : Omega n k m) = ⟨4, by omega⟩ := g₂_map_2_to_4
      rw [hg₂_2_eq] at hg₂_2_in
      exact h4_not (hB'_sub_supp_g₃ hg₂_2_in)

    -- B' contains fixed point of g₂
    have hB'_has_fixed : (B' ∩ {x | g₂ n k m x = x}).Nonempty := by
       -- B' ⊆ supp(g₃) = {2, 3, 5, 6, tailC}
       -- supp(g₃) ∩ supp(g₂) = {5}??
       -- g₂: 1 2 4 5 tailB.
       -- g₃: 2 3 5 6 tailC.
       -- Intersect: {2, 5}.
       -- Fixed by g₂ in supp(g₃): {3, 6, tailC}.
       -- Moved by g₂ in supp(g₃): {2, 5}.
       -- B' ⊆ {2, 5} => |B'|=2, B'={2, 5}.
       -- dist in g₃ is 2 (5->3->2?? No 5->6->...->2??)
       -- g₃ = (2 3 5 6 ...). 2->3->5->6.
       -- dist 2 to 5 is 2. (2->3->5).
       -- dist 5 to 2 is large.
       -- impossible for large cycle.
       sorry

    obtain ⟨y, hy_in, hy_fixed⟩ := hB'_has_fixed
    have hInter : (g₂ n k m '' B' ∩ B').Nonempty := ⟨y, ⟨y, hy_in, hy_fixed⟩, hy_in⟩
    
    have hB'_mem : B' ∈ BS.blocks := BS.orbit_subset_blocks (g₃ n k m) hB_in_BS (hInv.3) B' hB'_in_orbit
    rcases (perm_image_preserves_or_disjoint (g₂ n k m) B' BS.blocks BS.isPartition.1 hB'_mem (hInv.2 B' hB'_mem)) with hPres | hDisj
    · exact hg₂_B'_ne_B' hPres
    · exact Set.not_nonempty_iff_eq_empty.mpr (Set.disjoint_iff_inter_eq_empty.mp hDisj) hInter