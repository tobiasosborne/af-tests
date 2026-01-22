/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Core
import AfTests.Primitivity.Lemma11_2
import AfTests.Primitivity.Lemma11_5_Cases
import AfTests.Primitivity.Lemma11_5_SupportCover
import AfTests.Primitivity.Lemma11_5_Case2_Helpers
import AfTests.Transitivity.Lemma05ListProps
import AfTests.Primitivity.Lemma11_5_Defs
import AfTests.Primitivity.Lemma11_5_OrbitInfra

/-!
# Lemma 11.5: Case 2 Analysis

Helper lemmas for Case 2 (g₁(B) ≠ B) in the no non-trivial blocks proof.

## Main Results

* `elem1_not_in_support_g₁`: Element 1 is not in supp(g₁)
* `elem4_not_in_support_g₁`: Element 4 is not in supp(g₁)
* `case2_impossible`: Case 2 leads to contradiction

## Proof Strategy

In Case 2, g₁(B) ≠ B forces g₂(B) = g₃(B) = B via fixed-point argument.
Elements 1 and 4 (not in supp(g₁)) are fixed by g₁, so cannot be in B.
The block B' containing 1, 4 must have g₂(B') = B' (since g₂(4) = 1).
By Lemma 11.2, supp(g₂) ⊆ B', including 0, 3 ∈ supp(g₁).
This contradicts g₁(B') = B' and a₁ ∈ B ≠ B'.
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

-- ============================================
-- SECTION 1: ELEMENTS 1, 4 NOT IN supp(g₁)
-- ============================================

/-- Element 1 is NOT in supp(g₁) (not in g₁CoreList = [0, 5, 3, 2]) -/
theorem elem1_not_in_support_g₁ :
    (⟨1, by omega⟩ : Omega n k m) ∉ (g₁ n k m).support := by
  simp only [g₁, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_notMem
  intro h
  simp only [List.mem_append, g₁CoreList, tailAList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h
    all_goals simp only [Fin.ext_iff] at h; omega
  · obtain ⟨j, _, hj⟩ := h
    simp only [Fin.ext_iff] at hj
    omega

/-- Element 4 is NOT in supp(g₁) -/
theorem elem4_not_in_support_g₁ :
    (⟨4, by omega⟩ : Omega n k m) ∉ (g₁ n k m).support := by
  simp only [g₁, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_notMem
  intro h
  simp only [List.mem_append, g₁CoreList, tailAList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h
    all_goals simp only [Fin.ext_iff] at h; omega
  · obtain ⟨j, _, hj⟩ := h
    simp only [Fin.ext_iff] at hj
    omega

/-- g₁ fixes element 1 -/
theorem g₁_fixes_elem1 :
    g₁ n k m (⟨1, by omega⟩ : Omega n k m) = ⟨1, by omega⟩ :=
  fixed_outside_support _ _ elem1_not_in_support_g₁

/-- g₁ fixes element 4 -/
theorem g₁_fixes_elem4 :
    g₁ n k m (⟨4, by omega⟩ : Omega n k m) = ⟨4, by omega⟩ :=
  fixed_outside_support _ _ elem4_not_in_support_g₁

-- ============================================
-- SECTION 2: CASE 2 FIXED-POINT CONTRADICTION
-- ============================================

/-- If g₁(B) ≠ B (disjoint) and g₁ fixes x, then x ∉ B -/
theorem fixed_elem_not_in_block_of_disjoint {B : Set (Omega n k m)}
    (x : Omega n k m) (hFix : g₁ n k m x = x) (hDisj : Disjoint (g₁ n k m '' B) B) :
    x ∉ B := by
  intro hx
  have hx_in_both : x ∈ g₁ n k m '' B ∩ B := ⟨⟨x, hx, hFix⟩, hx⟩
  exact Set.disjoint_iff.mp hDisj hx_in_both

/-- In Case 2, element 1 is not in B -/
theorem case2_elem1_not_in_B (B : Set (Omega n k m))
    (hDisj : Disjoint (g₁ n k m '' B) B) :
    (⟨1, by omega⟩ : Omega n k m) ∉ B :=
  fixed_elem_not_in_block_of_disjoint _ g₁_fixes_elem1 hDisj

/-- In Case 2, element 4 is not in B -/
theorem case2_elem4_not_in_B (B : Set (Omega n k m))
    (hDisj : Disjoint (g₁ n k m '' B) B) :
    (⟨4, by omega⟩ : Omega n k m) ∉ B :=
  fixed_elem_not_in_block_of_disjoint _ g₁_fixes_elem4 hDisj

-- ============================================
-- SECTION 3: B DISJOINT FROM supp(g₂) ∪ supp(g₃)
-- ============================================

/-- If x ∈ supp(g₂) ∩ B and g₂(B) = B, then supp(g₂) ⊆ B.
    But supp(g₂) includes 1 and 4, which are not in B (Case 2).
    Therefore B ∩ supp(g₂) = ∅. -/
theorem case2_B_disjoint_supp_g₂ (B : Set (Omega n k m))
    (hg₁Disj : Disjoint (g₁ n k m '' B) B) (hg₂_pres : PreservesSet (g₂ n k m) B) :
    Disjoint (↑(g₂ n k m).support) B := by
  by_contra hMeet
  rw [Set.not_disjoint_iff] at hMeet
  obtain ⟨x, hx_supp, hx_B⟩ := hMeet
  -- If B ∩ supp(g₂) ≠ ∅ and g₂(B) = B, then by Lemma 11.2, supp(g₂) ⊆ B
  have hCyc := g₂_isCycle n k m
  have hSupp : (↑(g₂ n k m).support : Set _) ⊆ B :=
    (cycle_support_subset_or_disjoint hCyc hg₂_pres).resolve_right fun h =>
      Set.not_nonempty_iff_eq_empty.mpr
        (Set.disjoint_iff_inter_eq_empty.mp h) ⟨x, hx_supp, hx_B⟩
  -- But supp(g₂) includes element 1, which is not in B
  have h1_in_supp : (⟨1, by omega⟩ : Omega n k m) ∈ (g₂ n k m).support := elem1_in_support_g₂
  have h1_in_B := hSupp h1_in_supp
  exact case2_elem1_not_in_B B hg₁Disj h1_in_B

/-- Similarly for g₃ -/
theorem case2_B_disjoint_supp_g₃ (B : Set (Omega n k m))
    (hg₁Disj : Disjoint (g₁ n k m '' B) B) (hg₃_pres : PreservesSet (g₃ n k m) B) :
    Disjoint (↑(g₃ n k m).support) B := by
  by_contra hMeet
  rw [Set.not_disjoint_iff] at hMeet
  obtain ⟨x, hx_supp, hx_B⟩ := hMeet
  have hCyc := g₃_isCycle n k m
  have hSupp : (↑(g₃ n k m).support : Set _) ⊆ B :=
    (cycle_support_subset_or_disjoint hCyc hg₃_pres).resolve_right fun h =>
      Set.not_nonempty_iff_eq_empty.mpr
        (Set.disjoint_iff_inter_eq_empty.mp h) ⟨x, hx_supp, hx_B⟩
  -- But supp(g₃) includes element 1, which is not in B
  have h1_in_supp : (⟨1, by omega⟩ : Omega n k m) ∈ (g₃ n k m).support := elem1_in_support_g₃
  have h1_in_B := hSupp h1_in_supp
  exact case2_elem1_not_in_B B hg₁Disj h1_in_B

-- ============================================
-- SECTION 4: MAIN CASE 2 IMPOSSIBILITY
-- ============================================

/-- **Case 2 Impossibility**: g₁(B) ≠ B leads to contradiction.

    When g₁(B) ≠ B:
    1. g₂(B) = B and g₃(B) = B (forced by fixed-point on a₁)
    2. B is disjoint from supp(g₂) and supp(g₃) (else Lemma 11.2 gives contradiction)
    3. Since supp(g₂) ∪ supp(g₃) covers all core elements {0,1,2,3,4,5} and tailB ∪ tailC,
       B ⊆ tailA
    4. But a₁ ∈ B and B is non-trivial with |B| > 1, requiring |tailA| = n ≥ |B| ≥ 2

    For n ≥ 3, we use the global block system structure.
    Since B ⊆ supp(g₁), the orbit {g₁^j(B)} partitions supp(g₁).
    One block B' must contain 5 ∈ supp(g₁).
    This B' is also a subset of supp(g₁).
    But g₂(5) ∉ supp(g₁), so B' is not preserved by g₂.
    Also B' must intersect g₂(B') at some fixed point of g₂ (since |B'| > 1).
    This contradicts the block property for g₂. -/
theorem case2_impossible (hn : n ≥ 1) (B : Set (Omega n k m))
    (BS : BlockSystemOn n k m) (hInv : IsHInvariant BS) (hB_in_BS : B ∈ BS.blocks)
    (hg₁Disj : Disjoint (g₁ n k m '' B) B)
    (ha₁_in_B : a₁ n k m hn ∈ B)
    (hg₂_pres : PreservesSet (g₂ n k m) B) (hg₃_pres : PreservesSet (g₃ n k m) B)
    (hNT_lower : 1 < B.ncard) : False := by
  -- Step 1: B disjoint from supp(g₂) and supp(g₃)
  have hDisj₂ := case2_B_disjoint_supp_g₂ B hg₁Disj hg₂_pres
  have hDisj₃ := case2_B_disjoint_supp_g₃ B hg₁Disj hg₃_pres
  -- Step 2: B ⊆ tailA
  have hB_subset_tailA : ∀ x ∈ B, isTailA x := case2_B_subset_tailA B hDisj₂ hDisj₃
  -- Step 3: |B| ≤ n (since B ⊆ tailA and |tailA| = n)
  have hB_ncard_le_n : B.ncard ≤ n := by
    have hTailA_finite : Set.Finite {x : Omega n k m | isTailA x} := Set.toFinite _
    have hB_subset : B ⊆ {x : Omega n k m | isTailA x} := fun x hx => hB_subset_tailA x hx
    have hB_finite : B.Finite := hTailA_finite.subset hB_subset
    calc B.ncard ≤ {x : Omega n k m | isTailA x}.ncard := Set.ncard_le_ncard hB_subset hTailA_finite
      _ = n := by
        have h_eq : {x : Omega n k m | isTailA x} = Set.range (fun i : Fin n =>
            (⟨6 + i.val, by omega⟩ : Omega n k m)) := by
          ext x; simp only [Set.mem_setOf_eq, Set.mem_range, isTailA]
          constructor
          · intro ⟨hLo, hHi⟩
            have hi : x.val - 6 < n := by omega
            use ⟨x.val - 6, hi⟩
            ext; simp only [Fin.val_mk]; omega
          · intro ⟨i, hi⟩
            rw [← hi]; simp only [Fin.val_mk]; constructor <;> omega
        rw [h_eq, Set.ncard_range_of_injective]
        · simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
        · intro i j hij; ext; simp only [Fin.ext_iff] at hij ⊢; omega
  -- Case split on n
  by_cases hn1 : n = 1
  · -- n = 1: |tailA| = 1, so |B| ≤ 1, contradicting |B| > 1
    omega
  · by_cases hn2 : n = 2
    · -- n = 2: B ⊆ tailA = {a₁, a₂}. Since a₁ ∈ B and |B| > 1, B = {a₁, a₂}.
      -- g₁(a₁) = a₂ ∈ g₁(B), and a₂ ∈ B, so g₁(B) ∩ B ≠ ∅. Contradiction!
      -- Define a₂ = element 7
      have hn2' : n ≥ 2 := by omega
      let a₂ : Omega n k m := ⟨7, by omega⟩
      -- g₁(a₁) = a₂ (using g₁_a₁_eq_7)
      have hg₁_a₁ : g₁ n k m (a₁ n k m hn) = a₂ := g₁_a₁_eq_7 hn2'
      -- Since |B| > 1 and B ⊆ tailA with |tailA| = 2, there exists x ∈ B, x ≠ a₁
      have hB_has_two : ∃ x ∈ B, x ≠ a₁ n k m hn := by
        by_contra h; push_neg at h
        have hSub : B ⊆ {a₁ n k m hn} := fun y hy => Set.mem_singleton_iff.mpr (h y hy)
        have hLe : B.ncard ≤ ({a₁ n k m hn} : Set (Omega n k m)).ncard :=
          Set.ncard_le_ncard hSub (Set.finite_singleton _)
        simp only [Set.ncard_singleton] at hLe
        omega
      obtain ⟨x, hx_in_B, hx_ne_a₁⟩ := hB_has_two
      -- x is in tailA, so x.val ∈ {6, 7} (since n = 2)
      have hx_tailA := hB_subset_tailA x hx_in_B
      simp only [isTailA, hn2] at hx_tailA
      -- x.val = 6 or x.val = 7
      have hx_val : x.val = 6 ∨ x.val = 7 := by omega
      rcases hx_val with hx6 | hx7
      · -- x.val = 6 means x = a₁, contradiction
        have hx_eq : x = a₁ n k m hn := by unfold a₁; exact Fin.ext hx6
        exact hx_ne_a₁ hx_eq
      · -- x.val = 7 means x = a₂
        have hx_eq_a₂ : x = a₂ := Fin.ext hx7
        -- a₂ ∈ B
        have ha₂_in_B : a₂ ∈ B := hx_eq_a₂ ▸ hx_in_B
        -- g₁(a₁) = a₂ ∈ g₁(B)
        have ha₂_in_g₁B : a₂ ∈ g₁ n k m '' B := ⟨a₁ n k m hn, ha₁_in_B, hg₁_a₁⟩
        -- a₂ ∈ g₁(B) ∩ B
        have ha₂_in_both : a₂ ∈ g₁ n k m '' B ∩ B := ⟨ha₂_in_g₁B, ha₂_in_B⟩
        -- This contradicts disjointness
        exact Set.disjoint_iff.mp hg₁Disj ha₂_in_both
    · -- n ≥ 3: Fixed-point argument via block system
      -- Key insight: {0, 3} is NOT a valid block for g₁ because
      -- g₁²({0,3}) = {3, a₁} overlaps with {0,3} at element 3.
      -- So any block B' containing 0 must contain y ∉ {0, 3}, which is g₂-fixed.
      have hn3 : n ≥ 3 := by omega
      -- The g₁-orbit of B partitions supp(g₁). Since 0 ∈ supp(g₁), some B' contains 0.
      -- We need to show this B' also contains a g₂-fixed element.
      -- For now, we admit this orbit construction and derive contradiction.
      -- TODO: Add orbit infrastructure lemmas
      sorry