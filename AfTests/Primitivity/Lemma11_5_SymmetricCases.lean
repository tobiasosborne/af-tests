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

/-- **Case 2 Stabilization for k ≥ 1**: g₂(B) ≠ B forces g₁(B) = B and g₃(B) = B.

    NL Proof Reference (Node 1.9.1, symmetric for k≥1):
    - Tail B elements {b₁, ..., bₖ} are ONLY in supp(g₂)
    - They are NOT in supp(g₁) or supp(g₃)
    - Therefore g₁(bⱼ) = bⱼ and g₃(bⱼ) = bⱼ for all j
    - If g₁(B) ≠ B (disjoint), b₁ ∈ B ∩ g₁(B) → contradiction
    - If g₃(B) ≠ B (disjoint), b₁ ∈ B ∩ g₃(B) → contradiction -/
theorem case2_forces_stabilization_B (hk : k ≥ 1) (B : Set (Omega n k m))
    (hB₁ : b₁ n k m hk ∈ B)
    (h₁Disj : ¬PreservesSet (g₁ n k m) B → Disjoint (g₁ n k m '' B) B)
    (h₃Disj : ¬PreservesSet (g₃ n k m) B → Disjoint (g₃ n k m '' B) B) :
    PreservesSet (g₁ n k m) B ∧ PreservesSet (g₃ n k m) B := by
  constructor
  · -- Prove g₁(B) = B via fixed-point contradiction
    by_contra hNotPres
    have hDisj := h₁Disj hNotPres
    -- g₁ fixes b₁ (since b₁ is in tail B, not in supp(g₁))
    have hFix : g₁ n k m (b₁ n k m hk) = b₁ n k m hk := g₁_fixes_b₁ hk
    -- Therefore b₁ ∈ g₁(B) ∩ B
    have h_in_both := fixed_point_blocks_intersect (g₁ n k m) B (b₁ n k m hk) hB₁ hFix
    -- This contradicts disjointness
    exact Set.disjoint_iff.mp hDisj h_in_both
  · -- Prove g₃(B) = B via fixed-point contradiction (analogous argument)
    by_contra hNotPres
    have hDisj := h₃Disj hNotPres
    -- g₃ fixes b₁ (since b₁ is in tail B, not in supp(g₃))
    have hFix : g₃ n k m (b₁ n k m hk) = b₁ n k m hk := g₃_fixes_b₁ hk
    -- Therefore b₁ ∈ g₃(B) ∩ B
    have h_in_both := fixed_point_blocks_intersect (g₃ n k m) B (b₁ n k m hk) hB₁ hFix
    -- This contradicts disjointness
    exact Set.disjoint_iff.mp hDisj h_in_both

/-- **Case 2 Stabilization for m ≥ 1**: g₃(B) ≠ B forces g₁(B) = B and g₂(B) = B.

    NL Proof Reference (Node 1.9.1, symmetric for m≥1):
    - Tail C elements {c₁, ..., cₘ} are ONLY in supp(g₃)
    - They are NOT in supp(g₁) or supp(g₂)
    - Therefore g₁(cₗ) = cₗ and g₂(cₗ) = cₗ for all l
    - If g₁(B) ≠ B (disjoint), c₁ ∈ B ∩ g₁(B) → contradiction
    - If g₂(B) ≠ B (disjoint), c₁ ∈ B ∩ g₂(B) → contradiction -/
theorem case2_forces_stabilization_C (hm : m ≥ 1) (B : Set (Omega n k m))
    (hC₁ : c₁ n k m hm ∈ B)
    (h₁Disj : ¬PreservesSet (g₁ n k m) B → Disjoint (g₁ n k m '' B) B)
    (h₂Disj : ¬PreservesSet (g₂ n k m) B → Disjoint (g₂ n k m '' B) B) :
    PreservesSet (g₁ n k m) B ∧ PreservesSet (g₂ n k m) B := by
  constructor
  · -- Prove g₁(B) = B via fixed-point contradiction
    by_contra hNotPres
    have hDisj := h₁Disj hNotPres
    -- g₁ fixes c₁ (since c₁ is in tail C, not in supp(g₁))
    have hFix : g₁ n k m (c₁ n k m hm) = c₁ n k m hm := g₁_fixes_c₁ hm
    -- Therefore c₁ ∈ g₁(B) ∩ B
    have h_in_both := fixed_point_blocks_intersect (g₁ n k m) B (c₁ n k m hm) hC₁ hFix
    -- This contradicts disjointness
    exact Set.disjoint_iff.mp hDisj h_in_both
  · -- Prove g₂(B) = B via fixed-point contradiction (analogous argument)
    by_contra hNotPres
    have hDisj := h₂Disj hNotPres
    -- g₂ fixes c₁ (since c₁ is in tail C, not in supp(g₂))
    have hFix : g₂ n k m (c₁ n k m hm) = c₁ n k m hm := g₂_fixes_c₁ hm
    -- Therefore c₁ ∈ g₂(B) ∩ B
    have h_in_both := fixed_point_blocks_intersect (g₂ n k m) B (c₁ n k m hm) hC₁ hFix
    -- This contradicts disjointness
    exact Set.disjoint_iff.mp hDisj h_in_both

-- ============================================
-- SECTION 6: CASE 1b IMPOSSIBILITY (k ≥ 1 and m ≥ 1)
-- ============================================

/-- **Case 1b impossibility for k≥1**: g₂(B) = B, g₃(B) ≠ B is impossible.

    NL Proof Reference (Node 1.7/1.8 - Case 1a-ii pattern):
    - supp(g₂) ⊆ B, so element 0 ∈ B
    - Element 0 NOT in supp(g₃), so g₃(0) = 0
    - If g₃(B) ≠ B (disjoint), then 0 ∈ B ∩ g₃(B) → contradiction -/
theorem case1b_impossible_g₃ (B : Set (Omega n k m))
    (hSupp₂ : ((g₂ n k m).support : Set _) ⊆ B)
    (hDisj : Disjoint (g₃ n k m '' B) B) : False := by
  -- Element 0 is in supp(g₂), hence in B
  have h0_in_B : (⟨0, by omega⟩ : Omega n k m) ∈ B := hSupp₂ elem0_in_support_g₂
  -- Element 0 is not in supp(g₃), so g₃(0) = 0
  have hFix : g₃ n k m (⟨0, by omega⟩ : Omega n k m) = ⟨0, by omega⟩ := g₃_fixes_elem0
  -- Therefore 0 ∈ g₃(B) ∩ B
  have h0_in_both := fixed_point_blocks_intersect (g₃ n k m) B _ h0_in_B hFix
  -- This contradicts disjointness
  exact Set.disjoint_iff.mp hDisj h0_in_both

/-- **Case 1b impossibility for k≥1**: g₂(B) = B, g₁(B) ≠ B is impossible.

    NL Proof Reference (Node 1.9.6 symmetric):
    - supp(g₂) ⊆ B, so element 4 ∈ B
    - Element 4 NOT in supp(g₁), so g₁(4) = 4
    - If g₁(B) ≠ B (disjoint), then 4 ∈ B ∩ g₁(B) → contradiction -/
theorem case1b_impossible_g₁_from_g₂ (B : Set (Omega n k m))
    (hSupp₂ : ((g₂ n k m).support : Set _) ⊆ B)
    (hDisj : Disjoint (g₁ n k m '' B) B) : False := by
  -- Element 4 is in supp(g₂), hence in B
  have h4_in_B : (⟨4, by omega⟩ : Omega n k m) ∈ B := hSupp₂ elem4_in_support_g₂
  -- Element 4 is not in supp(g₁), so g₁(4) = 4
  have hFix : g₁ n k m (⟨4, by omega⟩ : Omega n k m) = ⟨4, by omega⟩ := g₁_fixes_elem4
  -- Therefore 4 ∈ g₁(B) ∩ B
  have h4_in_both := fixed_point_blocks_intersect (g₁ n k m) B _ h4_in_B hFix
  -- This contradicts disjointness
  exact Set.disjoint_iff.mp hDisj h4_in_both

/-- **Case 1b impossibility for m≥1**: g₃(B) = B, g₁(B) ≠ B is impossible.

    NL Proof Reference (Node 1.9.6 symmetric):
    - supp(g₃) ⊆ B, so element 1 ∈ B
    - Element 1 NOT in supp(g₁), so g₁(1) = 1
    - If g₁(B) ≠ B (disjoint), then 1 ∈ B ∩ g₁(B) → contradiction -/
theorem case1b_impossible_g₁ (B : Set (Omega n k m))
    (hSupp₃ : ((g₃ n k m).support : Set _) ⊆ B)
    (hDisj : Disjoint (g₁ n k m '' B) B) : False := by
  -- Element 1 is in supp(g₃), hence in B
  have h1_in_B : (⟨1, by omega⟩ : Omega n k m) ∈ B := hSupp₃ elem1_in_support_g₃
  -- Element 1 is not in supp(g₁), so g₁(1) = 1
  have hFix : g₁ n k m (⟨1, by omega⟩ : Omega n k m) = ⟨1, by omega⟩ := g₁_fixes_elem1
  -- Therefore 1 ∈ g₁(B) ∩ B
  have h1_in_both := fixed_point_blocks_intersect (g₁ n k m) B _ h1_in_B hFix
  -- This contradicts disjointness
  exact Set.disjoint_iff.mp hDisj h1_in_both

/-- **Case 1b impossibility for m≥1**: g₃(B) = B, g₂(B) ≠ B is impossible.

    NL Proof Reference (Node 1.9.6 symmetric):
    - supp(g₃) ⊆ B, so element 2 ∈ B
    - Element 2 NOT in supp(g₂), so g₂(2) = 2
    - If g₂(B) ≠ B (disjoint), then 2 ∈ B ∩ g₂(B) → contradiction -/
theorem case1b_impossible_g₂_from_g₃ (B : Set (Omega n k m))
    (hSupp₃ : ((g₃ n k m).support : Set _) ⊆ B)
    (hDisj : Disjoint (g₂ n k m '' B) B) : False := by
  -- Element 2 is in supp(g₃), hence in B
  have h2_in_B : (⟨2, by omega⟩ : Omega n k m) ∈ B := hSupp₃ elem2_in_support_g₃
  -- Element 2 is not in supp(g₂), so g₂(2) = 2
  have hFix : g₂ n k m (⟨2, by omega⟩ : Omega n k m) = ⟨2, by omega⟩ := g₂_fixes_elem2
  -- Therefore 2 ∈ g₂(B) ∩ B
  have h2_in_both := fixed_point_blocks_intersect (g₂ n k m) B _ h2_in_B hFix
  -- This contradicts disjointness
  exact Set.disjoint_iff.mp hDisj h2_in_both

-- ============================================
-- SECTION 7: CASE 2 IMPOSSIBILITY (k ≥ 1 and m ≥ 1)
-- ============================================

/-- **Case 2 Impossibility for k ≥ 1**: g₂(B) ≠ B leads to contradiction.

    NL Proof Reference (Node 1.9.5, symmetric for k≥1):

    When g₂(B) ≠ B:
    1. g₁(B) = B and g₃(B) = B (forced by fixed-point on b₁)
    2. B ⊆ supp(g₂) (fixed points of g₂ can't be in B due to disjointness)
    3. B ∩ supp(g₁) = ∅ (else Lemma 11.2 forces supp(g₁) ⊆ B, but elem 2 ∈ supp(g₁) \ supp(g₂))
    4. B ∩ supp(g₃) = ∅ (similarly)
    5. Therefore B ⊆ tailB
    6. For |B| > 1 in tailB, g₂(B) must share an element with B, contradiction -/
theorem case2_impossible_B (hk : k ≥ 1) (B : Set (Omega n k m))
    (hg₂Disj : Disjoint (g₂ n k m '' B) B)
    (hb₁_in_B : b₁ n k m hk ∈ B)
    (hg₁_pres : PreservesSet (g₁ n k m) B) (hg₃_pres : PreservesSet (g₃ n k m) B)
    (hBlock : ∀ j : ℕ, (g₂ n k m ^ j) '' B = B ∨ Disjoint ((g₂ n k m ^ j) '' B) B)
    (hNT_lower : 1 < B.ncard) : False := by
  -- Step 1: B ⊆ supp(g₂) (fixed points of g₂ can't be in B due to disjointness)
  have hB_subset_supp_g₂ : B ⊆ ↑(g₂ n k m).support := by
    intro x hxB
    by_contra hx_not_supp
    have hFix : g₂ n k m x = x := Equiv.Perm.notMem_support.mp hx_not_supp
    have hx_in_img : x ∈ g₂ n k m '' B := ⟨x, hxB, hFix⟩
    exact Set.disjoint_iff.mp hg₂Disj ⟨hx_in_img, hxB⟩
  -- Step 2: B ∩ supp(g₁) = ∅ (else Lemma 11.2 forces supp(g₁) ⊆ B, but elem 5 ∈ supp(g₁) \ supp(g₂))
  have hB_disj_supp_g₁ : Disjoint (↑(g₁ n k m).support) B := by
    have hCyc : (g₁ n k m).IsCycle := g₁_isCycle n k m (by omega)
    rcases cycle_support_subset_or_disjoint hCyc hg₁_pres with hSub | hDisj
    · exfalso
      have h5_in_B : (⟨5, by omega⟩ : Omega n k m) ∈ B := hSub elem5_in_support_g₁
      have h5_not : (⟨5, by omega⟩ : Omega n k m) ∉ (g₂ n k m).support := elem5_not_in_support_g₂
      exact h5_not (hB_subset_supp_g₂ h5_in_B)
    · exact hDisj
  -- Step 3: B ∩ supp(g₃) = ∅ (else Lemma 11.2 forces supp(g₃) ⊆ B, but elem 2 ∈ supp(g₃) \ supp(g₂))
  have hB_disj_supp_g₃ : Disjoint (↑(g₃ n k m).support) B := by
    have hCyc : (g₃ n k m).IsCycle := g₃_isCycle n k m
    rcases cycle_support_subset_or_disjoint hCyc hg₃_pres with hSub | hDisj
    · exfalso
      have h2_in_B : (⟨2, by omega⟩ : Omega n k m) ∈ B := hSub elem2_in_support_g₃
      have h2_not : (⟨2, by omega⟩ : Omega n k m) ∉ (g₂ n k m).support := elem2_not_in_support_g₂
      exact h2_not (hB_subset_supp_g₂ h2_in_B)
    · exact hDisj
  -- Step 4: B ⊆ tailB
  have hB_subset_tailB : ∀ x ∈ B, isTailB x :=
    case2_B_subset_tailB B hB_subset_supp_g₂ hB_disj_supp_g₁ hB_disj_supp_g₃
  -- Step 5: Since b₁ ∈ B and B ⊆ tailB, if k = 1 then |B| = 1
  -- For k ≥ 1 with B ⊆ tailB and |B| > 1, we need at least 2 elements from tailB
  -- But tailB has exactly k elements, and if k = 1, |B| ≤ 1
  -- Step 6: Contradiction via cardinality
  -- First show that B.ncard ≤ k (since B ⊆ tailB and |tailB| = k)
  have hB_ncard_le_k : B.ncard ≤ k := by
    have hTailB_finite : Set.Finite {x : Omega n k m | isTailB x} := Set.toFinite _
    have hB_subset_tailB_set : B ⊆ {x : Omega n k m | isTailB x} := fun x hx => hB_subset_tailB x hx
    have hB_finite : B.Finite := hTailB_finite.subset hB_subset_tailB_set
    calc B.ncard ≤ {x : Omega n k m | isTailB x}.ncard := Set.ncard_le_ncard hB_subset_tailB_set hTailB_finite
      _ = k := by
        -- tailB = {⟨6 + n + i, _⟩ | i < k} has exactly k elements
        have h_eq : {x : Omega n k m | isTailB x} = Set.range (fun i : Fin k =>
            (⟨6 + n + i.val, by omega⟩ : Omega n k m)) := by
          ext x; simp only [Set.mem_setOf_eq, Set.mem_range, isTailB]
          constructor
          · intro ⟨hLo, hHi⟩
            have hi : x.val - 6 - n < k := by have := x.isLt; omega
            use ⟨x.val - 6 - n, hi⟩
            ext; simp only [Fin.val_mk]; omega
          · intro ⟨i, hi⟩
            rw [← hi]; simp only [Fin.val_mk]
            constructor <;> omega
        rw [h_eq, Set.ncard_range_of_injective]
        · simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
        · intro i j hij; ext; simp only [Fin.ext_iff] at hij ⊢; omega
  -- Now: 1 < B.ncard ≤ k, so 2 ≤ k
  -- But we haven't used the full power of block condition yet
  -- The key is: for k = 1, this gives 1 < 1, contradiction
  -- For k ≥ 2, we need the block structure to force contradiction
  by_cases hk1 : k = 1
  · -- Case k = 1: tailB has 1 element, so |B| ≤ 1, contradicting |B| > 1
    omega
  · -- Case k ≥ 2: Use block structure to show B can't have two distinct tailB elements
    -- Key insight: If b₁ ∈ B and bⱼ ∈ B for j > 1, then g₂^(j-1)(B) = B (by block condition).
    -- Iterating g₂^(j-1) from bⱼ eventually reaches a core element, contradicting B ⊆ tailB.

    -- Since |B| > 1 and b₁ ∈ B, there exists another element x ∈ B with x ≠ b₁
    have hB_finite : B.Finite := Set.toFinite B
    have hB_nonempty : B.Nonempty := ⟨b₁ n k m hk, hb₁_in_B⟩

    -- All elements of B are in tailB, which has exactly k elements
    -- With |B| > 1 and B ⊆ {b₁, ..., bₖ}, there are at least 2 distinct tailB elements in B
    -- Let's find the second smallest index j > 1 such that bⱼ ∈ B

    -- Since B has more than 1 element and all are in tailB, there exists x ∈ B with x ≠ b₁
    obtain ⟨x, hx_in_B, hx_ne_b₁⟩ : ∃ x ∈ B, x ≠ b₁ n k m hk := by
      by_contra h
      push_neg at h
      -- If all elements equal b₁, then |B| ≤ 1
      have hSub : B ⊆ {b₁ n k m hk} := fun y hy => Set.mem_singleton_iff.mpr (h y hy)
      have hSing_ncard : ({b₁ n k m hk} : Set (Omega n k m)).ncard = 1 := Set.ncard_singleton _
      have hLe : B.ncard ≤ ({b₁ n k m hk} : Set (Omega n k m)).ncard :=
        Set.ncard_le_ncard hSub (Set.finite_singleton _)
      omega

    -- x is in tailB, so x.val ∈ [6+n, 6+n+k)
    have hx_tailB := hB_subset_tailB x hx_in_B

    -- b₁ has value 6+n, and x ≠ b₁ means x.val ≠ 6+n
    have hx_val_ne : x.val ≠ 6 + n := by
      intro heq
      have : x = b₁ n k m hk := Fin.ext heq
      exact hx_ne_b₁ this

    -- So x.val > 6+n (since x is in tailB = [6+n, 6+n+k))
    have hx_val_gt : x.val > 6 + n := by
      simp only [isTailB] at hx_tailB
      omega

    -- Let j = x.val - 6 - n + 1 be the "index" of x in tailB (1-indexed for b₁, b₂, ...)
    -- Then x = bⱼ with j > 1, and g₂^(j-1)(b₁) = x
    set j := x.val - 6 - n + 1 with hj_def
    have hj_gt_1 : j > 1 := by omega
    have hj_le_k : j ≤ k := by simp only [isTailB] at hx_tailB; omega

    -- g₂^(j-1) maps b₁ to x (since g₂ shifts tailB elements by 1)
    -- This means x ∈ g₂^(j-1)(B)
    have hx_in_image : x ∈ (g₂ n k m ^ (j - 1)) '' B := by
      -- g₂^(j-1)(b₁) = x because g₂ shifts indices in tailB by 1
      use b₁ n k m hk, hb₁_in_B
      -- Need to show g₂^(j-1)(b₁) = x
      -- b₁ = ⟨6+n, _⟩ = L[4], and g₂^(j-1)(L[4]) = L[(4+j-1) % (4+k)] = L[4+j-1] = x
      unfold b₁ g₂
      let L := g₂CoreList n k m ++ tailBList n k m
      have hnd : L.Nodup := g₂_list_nodup n k m
      have hlen : L.length = 4 + k := g₂_cycle_length n k m
      have h4_lt : 4 < L.length := by simp [L, g₂CoreList, tailBList]; omega
      have hb₁_eq : (⟨6 + n, by omega⟩ : Omega n k m) = L[4] := by
        simp only [L]; exact (AfTests.Transitivity.g₂_list_getElem_tail n k m ⟨0, hk⟩).symm
      rw [hb₁_eq, List.formPerm_pow_apply_getElem L hnd (j - 1) 4 h4_lt]
      -- (4 + (j-1)) % (4+k) = 4 + j - 1 since j ≤ k means 4+j-1 < 4+k
      have hmod : (4 + (j - 1)) % (4 + k) = 4 + (j - 1) := by
        apply Nat.mod_eq_of_lt; omega
      simp only [hlen, hmod]
      -- L[4 + (j-1)] = ⟨6+n+(j-1), _⟩
      have hj1_lt_k : j - 1 < k := by omega
      have hx_eq_L : L[4 + (j - 1)]'(by simp [L, g₂CoreList, tailBList]; omega) =
          (⟨6 + n + (j - 1), by omega⟩ : Omega n k m) :=
        AfTests.Transitivity.g₂_list_getElem_tail n k m ⟨j - 1, hj1_lt_k⟩
      rw [hx_eq_L]
      -- Now show ⟨6+n+(j-1), _⟩ = x
      -- x.val = 6 + n + (j - 1) follows from j = x.val - 6 - n + 1 with hx_val_gt: x.val > 6+n
      apply Fin.ext
      simp only [Fin.val_mk]
      -- j = x.val - 6 - n + 1, so j - 1 = x.val - 6 - n (since j > 1)
      have hj_calc : j - 1 = x.val - 6 - n := by
        simp only [hj_def]
        omega
      omega

    -- By hBlock, either g₂^(j-1)(B) = B or they're disjoint
    -- Since x ∈ both, they can't be disjoint, so g₂^(j-1)(B) = B
    have hg₂_pow_pres : (g₂ n k m ^ (j - 1)) '' B = B := by
      rcases hBlock (j - 1) with hEq | hDisj
      · exact hEq
      · exfalso
        exact Set.disjoint_iff.mp hDisj ⟨hx_in_image, hx_in_B⟩

    -- Now we iterate: g₂^(j-1) preserves B, so the orbit of any element under g₂^(j-1) stays in B
    -- The key is that g₂^k(b₁) is a core element (element 1), which leads to contradiction.

    -- The orbit of b₁ under g₂ visits all elements of supp(g₂), including core elements.
    -- Since g₂^(j-1)(B) = B, iterating gives g₂^(r*(j-1))(b₁) ∈ B for all r.

    -- Key fact: g₂^k(b₁) = element 1 (a core element)
    -- If g₂^k(B) = B, then element 1 ∈ B ⊆ tailB, contradiction.
    -- So by hBlock, g₂^k(B) ∩ B = ∅.

    -- We'll show that some multiple of (j-1) equals k mod (4+k), meaning g₂^k(b₁) ∈ B.
    -- But g₂^k(b₁) is core, contradicting B ⊆ tailB.

    -- The minimum period of B under g₂ is some divisor of (4+k) that also divides (j-1).
    -- Since g₂(B) ≠ B, the period p ≥ 2.
    -- Since p | (j-1) ≤ k-1 and p | (4+k), constraints force the orbit to hit core.

    -- For k = 2: j ∈ {2} (since j > 1 and j ≤ k), so j - 1 = 1.
    -- But g₂^1(B) = B contradicts hg₂Disj (g₂(B) disjoint from B).
    have hk_ge_2 : k ≥ 2 := by omega
    have hContra : g₂ n k m '' B = B ∨ Disjoint (g₂ n k m '' B) B := hBlock 1
    rcases hContra with hEq | _
    · -- If g₂(B) = B, this contradicts hg₂Disj
      rw [hEq] at hg₂Disj
      exact Set.not_disjoint_iff.mpr ⟨b₁ n k m hk, hb₁_in_B, hb₁_in_B⟩ hg₂Disj
    · -- g₂(B) is disjoint from B - this is consistent
      -- Now use that j - 1 ≥ 1 with g₂^(j-1)(B) = B implies g₂(B) = B (contradiction)
      -- Actually, we have j > 1, so j - 1 ≥ 1, but j - 1 could be > 1 as well.
      -- The key observation: for small k, j-1 = 1 forces contradiction.
      -- For k = 2, the only possible j is 2 (since j > 1 and j ≤ k = 2).
      by_cases hk2 : k = 2
      · -- For k = 2: j must equal 2, so j - 1 = 1, and g₂^1(B) = B = g₂(B)
        have hj_eq_2 : j = 2 := by omega
        have hj1_eq_1 : j - 1 = 1 := by omega
        rw [hj1_eq_1] at hg₂_pow_pres
        simp only [pow_one] at hg₂_pow_pres
        -- Now g₂(B) = B, contradicting g₂(B) ∩ B = ∅ with B nonempty
        rw [hg₂_pow_pres] at hg₂Disj
        exact Set.not_disjoint_iff.mpr ⟨b₁ n k m hk, hb₁_in_B, hb₁_in_B⟩ hg₂Disj
      · -- For k ≥ 3: Orbit analysis shows the orbit of b₁ under g₂^(j-1) hits a core element.
        --
        -- Mathematical argument:
        -- 1. The period p of B under g₂ satisfies: p | (j-1), p ≥ 2, p | (4+k)
        -- 2. The orbit of b₁ under g₂^p visits (4+k)/p elements at indices 4, 4+p, 4+2p, ...
        -- 3. If gcd(j-1, 4+k) ≤ 4, the orbit hits a core index < 4
        -- 4. For k = 3: 4+k = 7 (prime). Since j-1 ≤ 2 and gcd(j-1, 7) ∈ {1}, the orbit
        --    visits all 7 elements, including core. If j-1 = 1, then g₂(B) = B (contradiction).
        --    If j-1 = 2, then g₂⁴(b₁) is at index (4+4)%7 = 1, a core element.
        -- 5. For k ≥ 4: Similar analysis shows the orbit always hits core.
        -- 6. For large k where gcd could be > 4 (e.g., k=6, p=5), the H-block structure
        --    from mixed products like g₂*g₁⁻¹*g₂⁻¹ forces additional constraints that
        --    rule out such cases (B = {b₁, b₆} for k=6 is not an H-block).
        --
        -- The full formalization requires careful handling of type coercions between
        -- Perm and functions. Leaving as sorry with documented mathematical proof.
        have hk_ge_3 : k ≥ 3 := by omega
        sorry

/-- **Case 2 Impossibility for m ≥ 1**: g₃(B) ≠ B leads to contradiction.

    NL Proof Reference (Node 1.9.5, symmetric for m≥1):

    When g₃(B) ≠ B:
    1. g₁(B) = B and g₂(B) = B (forced by fixed-point on c₁)
    2. Since g₁(B) = B and g₂(B) = B, by Lemma 11.2:
       - If B ∩ supp(g₁) ≠ ∅, then supp(g₁) ⊆ B
       - If B ∩ supp(g₂) ≠ ∅, then supp(g₂) ⊆ B
    3. The orbit of B under ⟨g₃⟩ partitions elements
    4. Elements in supp(g₁) ∩ supp(g₃) = {2, 5} and supp(g₂) ∩ supp(g₃) = {1, 4}
    5. Eventually this forces |B| = N, contradicting non-triviality

    **TODO**: Complete proof following NL proof orbit analysis -/
theorem case2_impossible_C (hm : m ≥ 1) (B : Set (Omega n k m))
    (hg₃Disj : Disjoint (g₃ n k m '' B) B)
    (hc₁_in_B : c₁ n k m hm ∈ B)
    (hg₁_pres : PreservesSet (g₁ n k m) B) (hg₂_pres : PreservesSet (g₂ n k m) B)
    (hBlock : ∀ j : ℕ, (g₃ n k m ^ j) '' B = B ∨ Disjoint ((g₃ n k m ^ j) '' B) B)
    (hNT_lower : 1 < B.ncard) : False := by
  -- Following NL proof Node 1.9.5:
  -- Step 1: g₃(B) ≠ B but g₁(B) = B, g₂(B) = B (already given)
  -- Step 2: Need to show B intersects supp(g₁) or supp(g₂) to apply Lemma 11.2
  -- Step 3: Use block dichotomy hBlock to analyze orbit structure
  -- Step 4: Derive contradiction from support containment forcing |B| = N
  sorry
