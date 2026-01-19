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
    (cycle_support_subset_or_disjoint hCyc hg₂_pres).resolve_right
      (fun h => Set.not_nonempty_iff_eq_empty.mpr (Set.disjoint_iff_inter_eq_empty.mp h) ⟨x, hx_supp, hx_B⟩)
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
    (cycle_support_subset_or_disjoint hCyc hg₃_pres).resolve_right
      (fun h => Set.not_nonempty_iff_eq_empty.mpr (Set.disjoint_iff_inter_eq_empty.mp h) ⟨x, hx_supp, hx_B⟩)
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

    The actual contradiction comes from the block size constraints. -/
theorem case2_impossible (hn : n ≥ 1) (B : Set (Omega n k m))
    (hg₁Disj : Disjoint (g₁ n k m '' B) B)
    (ha₁_in_B : a₁ n k m hn ∈ B)
    (hg₂_pres : PreservesSet (g₂ n k m) B) (hg₃_pres : PreservesSet (g₃ n k m) B)
    (hNT_lower : 1 < B.ncard) : False := by
  -- B is disjoint from supp(g₂) and supp(g₃)
  have hDisj₂ := case2_B_disjoint_supp_g₂ B hg₁Disj hg₂_pres
  have hDisj₃ := case2_B_disjoint_supp_g₃ B hg₁Disj hg₃_pres
  -- a₁ ∈ B, so g₁(a₁) ∈ g₁ '' B. Since g₁ '' B ∩ B = ∅, g₁(a₁) ∉ B.
  have hg₁a₁_not_in_B : g₁ n k m (a₁ n k m hn) ∉ B := by
    intro h
    have himg : g₁ n k m (a₁ n k m hn) ∈ g₁ n k m '' B := ⟨a₁ n k m hn, ha₁_in_B, rfl⟩
    exact Set.disjoint_iff.mp hg₁Disj ⟨himg, h⟩
  -- Since B is disjoint from supp(g₂) ∪ supp(g₃), and these cover all of Ω except tailA,
  -- every element of B must be in tailA.
  -- For any x ∈ B, x must be of the form ⟨6 + i, _⟩ for some i < n.
  -- The key observation:
  -- 1. a₁ = ⟨6, _⟩ ∈ B
  -- 2. g₁(a₁) = ⟨7, _⟩ (when n ≥ 2) or ⟨0, _⟩ (when n = 1), and g₁(a₁) ∉ B
  -- 3. For n = 1: tailA = {⟨6, _⟩}, so B ⊆ {a₁} and |B| ≤ 1
  -- 4. For n = 2: ⟨7, _⟩ ∉ B (since g₁(a₁) = ⟨7, _⟩ ∉ B), so B ⊆ {⟨6, _⟩} and |B| ≤ 1
  -- In both cases, |B| ≤ 1, contradicting |B| > 1.
  -- The proof uses that any second element b ∈ B would need to satisfy constraints
  -- that are impossible for small n.
  -- The key constraint: every element of B is in tailA (not in supp(g₂) ∪ supp(g₃))
  -- And if x ∈ B with x ≠ last_tailA_elem, then g₁(x) = x+1 must not be in B
  -- This forces B to have "gaps" - can't have consecutive tailA elements
  -- For the orbit structure to work out, this severely limits |B|
  --
  -- The core argument: B ⊆ tailA and the orbit of B under g₁ must have specific structure.
  -- Since g₁ is a cycle and we need g₁(B) ∩ B = ∅, the orbit size r divides cycle_length.
  -- Combined with B ⊆ tailA (n elements), we get strong constraints.
  -- For small n, this forces |B| ≤ 1.
  --
  -- For n ≥ 3, the orbit structure combined with g₁(B) ∩ B = ∅ forces |B| ≤ 1.
  have hB_small : B.ncard ≤ 1 := case2_B_ncard_le_one hn B hDisj₂ hDisj₃ hg₁Disj ha₁_in_B
  omega
