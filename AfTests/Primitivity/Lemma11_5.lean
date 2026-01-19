/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Core
import AfTests.Primitivity.Lemma11_2
import AfTests.Primitivity.Lemma11_3
import AfTests.Primitivity.Lemma11_4
import AfTests.Primitivity.Lemma11_5_FixedPoints
import AfTests.Primitivity.Lemma11_5_Cases
import AfTests.Primitivity.Lemma11_5_SupportCover
import AfTests.Primitivity.Lemma11_5_Case2

/-!
# Lemma 11.5: No Non-trivial Blocks

If n + k + m ≥ 1, then H admits no non-trivial block system on Ω.

## Main Results

* `lemma11_5_no_nontrivial_blocks`: H has no non-trivial block system when n+k+m ≥ 1

## Proof Outline

Assume for contradiction that B is a non-trivial H-invariant block system.
WLOG n ≥ 1 (by symmetry of generators). Let B be the block containing a₁.

**Case 1: g₁(B) = B**
By Lemma 11.3, supp(g₁) ⊆ B, so B contains {1,3,4,6,a₁,...,aₙ}.

  **Case 1a: g₂(B) = B**
  By Lemma 11.2, supp(g₂) ⊆ B. Now B contains {1,2,3,4,5,6,aᵢ,bⱼ}.
  - If g₃(B) = B: supp(g₃) ⊆ B, so B = Ω. Contradiction (non-trivial).
  - If g₃(B) ≠ B: Fixed point argument - g₃ fixes {1,4,aᵢ,bⱼ} ⊆ B,
    so g₃(B) ∩ B ≠ ∅. Contradiction.

  **Case 1b: g₂(B) ≠ B**
  Fixed point argument - g₂ fixes {3,6,aᵢ} ⊆ B, so g₂(B) ∩ B ≠ ∅. Contradiction.

**Case 2: g₁(B) ≠ B**
Fixed point argument - g₂,g₃ fix {aᵢ} ⊆ B, forcing g₂(B) = g₃(B) = B.
Then Lemma 11.2 forces supports into blocks, eventually |B| = N.

## Reference

See `examples/lemmas/lemma11_5_no_nontrivial_blocks.md` for the natural language proof.
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

-- ============================================
-- SECTION 1: NON-TRIVIAL BLOCK SYSTEM
-- ============================================

/-- A block system on Ω with block size d -/
structure BlockSystemOn (n k m : ℕ) where
  blocks : Set (Set (Omega n k m))
  blockSize : ℕ
  isPartition : blocks.PairwiseDisjoint id ∧ ⋃₀ blocks = Set.univ
  allSameSize : ∀ B ∈ blocks, B.ncard = blockSize

/-- A block system is H-invariant if all generators preserve it -/
def IsHInvariant (BS : BlockSystemOn n k m) : Prop :=
  BlockSystemInvariant (g₁ n k m) BS.blocks ∧
  BlockSystemInvariant (g₂ n k m) BS.blocks ∧
  BlockSystemInvariant (g₃ n k m) BS.blocks

/-- A block system is non-trivial if 1 < blockSize < |Ω| -/
def IsNontrivial (BS : BlockSystemOn n k m) : Prop :=
  1 < BS.blockSize ∧ BS.blockSize < 6 + n + k + m

-- ============================================
-- SECTION 2: CASE ANALYSIS HELPERS
-- ============================================

/-- If σ fixes x ∈ B and σ(B) ≠ B, then σ(B) ∩ B ≠ ∅ (contradiction) -/
theorem fixed_point_blocks_intersect {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) (B : Set α) (x : α) (hx : x ∈ B) (hFix : σ x = x) :
    x ∈ σ '' B ∩ B := by
  refine ⟨?_, hx⟩
  rw [Set.mem_image]
  exact ⟨x, hx, hFix⟩

/-- Case 1b impossibility: g₂(B) ≠ B is impossible when supp(g₁) ⊆ B and n ≥ 1 -/
theorem case1b_impossible (hn : n ≥ 1) (B : Set (Omega n k m))
    (hSupp : ((g₁ n k m).support : Set _) ⊆ B)
    (hDisj : Disjoint (g₂ n k m '' B) B) : False := by
  -- Element 2 (= "3" in 1-indexed) is in supp(g₁), hence in B
  have h2_in_supp : (⟨2, by omega⟩ : Omega n k m) ∈ (g₁ n k m).support :=
    elem2_in_support_g₁ hn
  have h2_in_B : (⟨2, by omega⟩ : Omega n k m) ∈ B := hSupp h2_in_supp
  -- Element 2 is not in supp(g₂), so g₂(2) = 2
  have hFix : g₂ n k m (⟨2, by omega⟩ : Omega n k m) = ⟨2, by omega⟩ := g₂_fixes_elem2
  -- Therefore 2 ∈ g₂(B) ∩ B
  have h2_in_both := fixed_point_blocks_intersect (g₂ n k m) B _ h2_in_B hFix
  -- This contradicts disjointness
  exact Set.disjoint_iff.mp hDisj h2_in_both

/-- Case 2: g₁(B) ≠ B forces g₂(B) = B and g₃(B) = B

    Given that B is part of a block system (so non-preservation implies disjointness),
    we show g₂ and g₃ must preserve B by fixed-point arguments. -/
theorem case2_forces_stabilization (hn : n ≥ 1) (B : Set (Omega n k m))
    (hA : a₁ n k m hn ∈ B)
    (h₂Disj : ¬PreservesSet (g₂ n k m) B → Disjoint (g₂ n k m '' B) B)
    (h₃Disj : ¬PreservesSet (g₃ n k m) B → Disjoint (g₃ n k m '' B) B) :
    PreservesSet (g₂ n k m) B ∧ PreservesSet (g₃ n k m) B := by
  constructor
  · -- Prove g₂(B) = B
    by_contra hNotPres
    have hDisj := h₂Disj hNotPres
    -- g₂ fixes a₁ (since a₁ is in tail A, not in supp(g₂))
    have hFix : g₂ n k m (a₁ n k m hn) = a₁ n k m hn := by
      unfold a₁
      exact g₂_fixes_tailA hn ⟨0, hn⟩
    -- Therefore a₁ ∈ g₂(B) ∩ B
    have h_in_both := fixed_point_blocks_intersect (g₂ n k m) B (a₁ n k m hn) hA hFix
    -- This contradicts disjointness
    exact Set.disjoint_iff.mp hDisj h_in_both
  · -- Prove g₃(B) = B (analogous argument)
    by_contra hNotPres
    have hDisj := h₃Disj hNotPres
    -- g₃ fixes a₁ (since a₁ is in tail A, not in supp(g₃))
    have hFix : g₃ n k m (a₁ n k m hn) = a₁ n k m hn := by
      unfold a₁
      exact g₃_fixes_tailA hn ⟨0, hn⟩
    -- Therefore a₁ ∈ g₃(B) ∩ B
    have h_in_both := fixed_point_blocks_intersect (g₃ n k m) B (a₁ n k m hn) hA hFix
    -- This contradicts disjointness
    exact Set.disjoint_iff.mp hDisj h_in_both

-- ============================================
-- SECTION 3: MAIN THEOREM
-- ============================================

/-- **Lemma 11.5: No Non-trivial Blocks**

    If n + k + m ≥ 1, then H admits no non-trivial H-invariant block system on Ω.

    The proof proceeds by case analysis on which generators stabilize the block
    containing a₁ (WLOG n ≥ 1), using fixed-point arguments to derive contradictions. -/
theorem lemma11_5_no_nontrivial_blocks (h : n + k + m ≥ 1) :
    ∀ BS : BlockSystemOn n k m, IsHInvariant BS → ¬IsNontrivial BS := by
  intro BS hInv hNT
  -- Extract the invariance conditions
  obtain ⟨hInv₁, hInv₂, hInv₃⟩ := hInv
  obtain ⟨hDisj, hCover⟩ := BS.isPartition
  -- WLOG n ≥ 1 (by symmetry, can relabel generators)
  -- For now, we handle the case n ≥ 1 directly; k ≥ 1 or m ≥ 1 cases are symmetric
  by_cases hn : n ≥ 1
  · -- Case: n ≥ 1. Let B be the block containing a₁
    -- Since BS.blocks covers Ω, there exists a block B containing a₁
    have ha₁_in_univ : a₁ n k m hn ∈ (Set.univ : Set (Omega n k m)) := Set.mem_univ _
    rw [← hCover] at ha₁_in_univ
    obtain ⟨B, hB_mem, ha₁_in_B⟩ := Set.mem_sUnion.mp ha₁_in_univ
    -- For any block in an H-invariant system, generator images are either equal or disjoint
    have hDichotomy₁ := perm_image_preserves_or_disjoint (g₁ n k m) B BS.blocks hDisj hB_mem
      (hInv₁ B hB_mem)
    have hDichotomy₂ := perm_image_preserves_or_disjoint (g₂ n k m) B BS.blocks hDisj hB_mem
      (hInv₂ B hB_mem)
    have hDichotomy₃ := perm_image_preserves_or_disjoint (g₃ n k m) B BS.blocks hDisj hB_mem
      (hInv₃ B hB_mem)
    -- Case 1: g₁(B) = B
    rcases hDichotomy₁ with hg₁_pres | hg₁_disj
    · -- Case 1: g₁ preserves B
      -- By Lemma 11.3, supp(g₁) ⊆ B
      have hSupp₁ : (↑(g₁ n k m).support : Set _) ⊆ B := by
        have hMeet : containsA₁ B hn := ha₁_in_B
        exact lemma11_3_tail_in_block hn B hMeet hg₁_pres
      -- Sub-case: g₂(B) = B vs g₂(B) ≠ B
      rcases hDichotomy₂ with hg₂_pres | hg₂_disj
      · -- Case 1a: g₂ also preserves B
        -- Element 0 ∈ supp(g₁) ⊆ B
        have h0_in_B : (⟨0, by omega⟩ : Omega n k m) ∈ B := hSupp₁ elem0_in_support_g₁
        -- Since 0 ∈ supp(g₂), and g₂(B) = B, by Lemma 11.2, supp(g₂) ⊆ B
        have hSupp₂ : (↑(g₂ n k m).support : Set _) ⊆ B := by
          have hMeet : (↑(g₂ n k m).support ∩ B).Nonempty := ⟨⟨0, by omega⟩, elem0_in_support_g₂, h0_in_B⟩
          have hCyc := g₂_isCycle n k m
          exact (cycle_support_subset_or_disjoint hCyc hg₂_pres).resolve_right
            (fun hDisj' => Set.not_nonempty_iff_eq_empty.mpr
              (Set.disjoint_iff_inter_eq_empty.mp hDisj') hMeet)
        -- Sub-sub-case: g₃(B) = B vs g₃(B) ≠ B
        rcases hDichotomy₃ with hg₃_pres | hg₃_disj
        · -- Case 1a-i: g₃ also preserves B
          -- By Lemma 11.2, supp(g₃) ⊆ B (since element 1 ∈ supp(g₂) ⊆ B is also in supp(g₃))
          have hSupp₃ : (↑(g₃ n k m).support : Set _) ⊆ B := by
            -- Element 1 is in supp(g₂) ⊆ B, and also in supp(g₃)
            have h1_in_B : (⟨1, by omega⟩ : Omega n k m) ∈ B := hSupp₂ elem1_in_support_g₂
            have hMeet : (↑(g₃ n k m).support ∩ B).Nonempty :=
              ⟨⟨1, by omega⟩, elem1_in_support_g₃, h1_in_B⟩
            have hCyc := g₃_isCycle n k m
            exact (cycle_support_subset_or_disjoint hCyc hg₃_pres).resolve_right
              (fun hDisj' => Set.not_nonempty_iff_eq_empty.mpr
                (Set.disjoint_iff_inter_eq_empty.mp hDisj') hMeet)
          -- Now B contains all three supports, so B = Ω
          have hB_eq_univ := case1a_i_supports_cover_univ B hSupp₁ hSupp₂ hSupp₃
          -- This means |B| = |Ω| = 6 + n + k + m, contradicting non-triviality
          have hBS_eq : BS.blockSize = 6 + n + k + m := by
            have hCard := BS.allSameSize B hB_mem
            rw [hB_eq_univ] at hCard
            simp only [Set.ncard_univ, Omega, Nat.card_eq_fintype_card, Fintype.card_fin] at hCard
            exact hCard.symm
          -- Non-triviality requires blockSize < 6 + n + k + m
          exact Nat.lt_irrefl _ (hBS_eq ▸ hNT.2)
        · -- Case 1a-ii: g₃ does not preserve B (disjoint)
          -- Element 0 ∈ supp(g₁) ⊆ B, and g₃ fixes 0 (not in supp(g₃))
          exact case1a_ii_impossible B h0_in_B hg₃_disj
      · -- Case 1b: g₂ does not preserve B (disjoint)
        exact case1b_impossible hn B hSupp₁ hg₂_disj
    · -- Case 2: g₁ does not preserve B (disjoint)
      -- By fixed-point argument, g₂ and g₃ must preserve B
      have hDisj₂ : ¬PreservesSet (g₂ n k m) B → Disjoint (g₂ n k m '' B) B := by
        intro hNot
        exact hDichotomy₂.resolve_left hNot
      have hDisj₃ : ¬PreservesSet (g₃ n k m) B → Disjoint (g₃ n k m '' B) B := by
        intro hNot
        exact hDichotomy₃.resolve_left hNot
      obtain ⟨hg₂_pres, hg₃_pres⟩ := case2_forces_stabilization hn B ha₁_in_B hDisj₂ hDisj₃
      -- Now use Case 2 impossibility theorem
      -- Need: 1 < B.ncard from non-triviality
      have hSize_lower : 1 < BS.blockSize := hNT.1
      have hB_size := BS.allSameSize B hB_mem
      rw [← hB_size] at hSize_lower
      exact case2_impossible hn B hg₁_disj ha₁_in_B hg₂_pres hg₃_pres hSize_lower
  · -- Case: n = 0, so k ≥ 1 or m ≥ 1. By symmetry, similar argument applies.
    -- The proof is symmetric: if k ≥ 1, use b₁ and g₂; if m ≥ 1, use c₁ and g₃
    -- Each case leads to the same case analysis structure
    -- TODO: Complete symmetric cases by generator relabeling
    sorry
