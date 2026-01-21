/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Core
import AfTests.Primitivity.Lemma11_2
import AfTests.Primitivity.Lemma11_3
import AfTests.Primitivity.Lemma11_4
import AfTests.Primitivity.Lemma11_5_Defs
import AfTests.Primitivity.Lemma11_5_CycleSupport
import AfTests.Primitivity.Lemma11_5_Case2
import AfTests.Primitivity.Lemma11_5_OrbitContinuation

/-!
# Lemma 11.5 Case 2: Correct Proof via Block B₁

The correct Case 2 argument uses the block B₁ containing element 1.
Since g₁(1) = 1, we have g₁(B₁) = B₁. Then either:
- supp(g₁) ⊆ B₁, so a₁ ∈ B₁ ≠ B (contradiction)
- B₁ ∩ supp(g₁) = ∅, but then g₂(B₁) contains 3 ∈ supp(g₁), leading to contradiction.
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

/-- If x is fixed by g and x ∈ B, and both B and g(B) are in a disjoint family,
    then g(B) = B -/
theorem block_fixed_of_fixed_point' {α : Type*}
    (g : Perm α) (B : Set α) (blocks : Set (Set α))
    (hDisj : blocks.PairwiseDisjoint id)
    (hB : B ∈ blocks) (hgB : g '' B ∈ blocks)
    (x : α) (hx : x ∈ B) (hFix : g x = x) : g '' B = B := by
  by_contra hNe
  have hx_in_both : x ∈ g '' B ∩ B := ⟨⟨x, hx, hFix⟩, hx⟩
  exact Set.disjoint_iff.mp (hDisj hgB hB hNe) hx_in_both

/-- g₂ maps element 1 to element 3 -/
theorem g₂_elem1_eq_elem3' : g₂ n k m (⟨1, by omega⟩ : Omega n k m) = ⟨3, by omega⟩ := by
  unfold g₂
  have hNodup := g₂_list_nodup n k m
  have h_len := g₂_cycle_length n k m
  have h_0_lt : 0 < (g₂CoreList n k m ++ tailBList n k m).length := by rw [h_len]; omega
  have h_idx : (g₂CoreList n k m ++ tailBList n k m)[0]'h_0_lt =
      (⟨1, by omega⟩ : Omega n k m) := by simp [g₂CoreList]
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 0 h_0_lt]
  simp only [h_len]
  have h_mod : (0 + 1) % (4 + k) = 1 := Nat.mod_eq_of_lt (by omega)
  simp only [h_mod]
  -- Index 1 is in the first part (g₂CoreList has 4 elements)
  have h_core_len : (g₂CoreList n k m).length = 4 := by simp [g₂CoreList]
  rw [List.getElem_append_left (by rw [h_core_len]; omega : 1 < (g₂CoreList n k m).length)]
  simp [g₂CoreList]

/-- Case 2: the orbit continuation eventually reaches a block preserved by g₁ with
    non-empty support intersection, forcing supp(g₁) into that block and a₁ ≠ B. -/
theorem case2_correct (hn : n ≥ 1) (BS : BlockSystemOn n k m) (hInv : IsHInvariant BS)
    (B : Set (Omega n k m)) (hB : B ∈ BS.blocks)
    (ha₁_in_B : a₁ n k m hn ∈ B)
    (hg₁_disj : Disjoint (g₁ n k m '' B) B)
    (hg₂_pres : PreservesSet (g₂ n k m) B)
    (hB_disj_g₂ : Disjoint (↑(g₂ n k m).support) B)
    (hB_subset_tailA : ∀ x ∈ B, isTailA x)
    (hSize : 1 < B.ncard) : False := by
  obtain ⟨hDisj, hCover⟩ := BS.isPartition
  have hInvOrig := hInv
  obtain ⟨hInv₁, hInv₂, _⟩ := hInv
  -- Find B₁, the block containing element 1
  have h1_in_univ : (⟨1, by omega⟩ : Omega n k m) ∈ (Set.univ : Set _) := Set.mem_univ _
  rw [← hCover] at h1_in_univ
  obtain ⟨B₁, hB₁_mem, h1_in_B₁⟩ := Set.mem_sUnion.mp h1_in_univ
  -- g₁(1) = 1, so g₁(B₁) = B₁
  have hg₁_fix_1 : g₁ n k m (⟨1, by omega⟩ : Omega n k m) = ⟨1, by omega⟩ := g₁_fixes_elem1
  have hg₁B₁_block : g₁ n k m '' B₁ ∈ BS.blocks := hInv₁ B₁ hB₁_mem
  have hg₁_pres_B₁ : g₁ n k m '' B₁ = B₁ :=
    block_fixed_of_fixed_point' (g₁ n k m) B₁ BS.blocks hDisj hB₁_mem hg₁B₁_block
      ⟨1, by omega⟩ h1_in_B₁ hg₁_fix_1
  -- g₁ is a cycle
  have hCyc : (g₁ n k m).IsCycle := g₁_isCycle n k m (by omega)
  -- Either supp(g₁) ⊆ B₁ or B₁ ∩ supp(g₁) = ∅
  rcases cycle_support_subset_or_disjoint hCyc hg₁_pres_B₁ with hSupp | hDisj₁
  · -- Case: supp(g₁) ⊆ B₁, so a₁ ∈ B₁
    have ha₁_in_B₁ : a₁ n k m hn ∈ B₁ := hSupp (a₁_mem_support_g₁ hn)
    -- 1 ∈ B₁ but 1 ∉ B (since 1 ∈ supp(g₂) and B ∩ supp(g₂) = ∅)
    have h1_not_in_B : (⟨1, by omega⟩ : Omega n k m) ∉ B := by
      intro h1B; exact Set.disjoint_iff.mp hB_disj_g₂ ⟨elem1_in_support_g₂, h1B⟩
    have hB_ne_B₁ : B ≠ B₁ := fun heq => h1_not_in_B (heq ▸ h1_in_B₁)
    exact Set.disjoint_iff.mp (hDisj hB hB₁_mem hB_ne_B₁) ⟨ha₁_in_B, ha₁_in_B₁⟩
  · -- Case: B₁ ∩ supp(g₁) = ∅
    -- g₂(1) = 3, so g₂(B₁) contains 3 ∈ supp(g₁)
    have hg₂_1 : g₂ n k m (⟨1, by omega⟩ : Omega n k m) = ⟨3, by omega⟩ := g₂_elem1_eq_elem3'
    have h3_in_g₂B₁ : (⟨3, by omega⟩ : Omega n k m) ∈ g₂ n k m '' B₁ :=
      ⟨⟨1, by omega⟩, h1_in_B₁, hg₂_1⟩
    have hg₂B₁_block : g₂ n k m '' B₁ ∈ BS.blocks := hInv₂ B₁ hB₁_mem
    have h3_in_supp : (⟨3, by omega⟩ : Omega n k m) ∈ (g₁ n k m).support := elem3_in_support_g₁
    have hg₁g₂B₁_block : g₁ n k m '' (g₂ n k m '' B₁) ∈ BS.blocks := hInv₁ _ hg₂B₁_block
    by_cases hg₁_pres_g₂B₁ : g₁ n k m '' (g₂ n k m '' B₁) = g₂ n k m '' B₁
    · -- g₁ preserves g₂(B₁), and 3 ∈ g₂(B₁) ∩ supp(g₁), so supp(g₁) ⊆ g₂(B₁)
      have hMeet : (↑(g₁ n k m).support ∩ (g₂ n k m '' B₁)).Nonempty :=
        ⟨⟨3, by omega⟩, h3_in_supp, h3_in_g₂B₁⟩
      have hSupp₃ : (↑(g₁ n k m).support : Set _) ⊆ g₂ n k m '' B₁ :=
        (cycle_support_subset_or_disjoint hCyc hg₁_pres_g₂B₁).resolve_right
          (fun hD => Set.not_nonempty_iff_eq_empty.mpr (Set.disjoint_iff_inter_eq_empty.mp hD) hMeet)
      have ha₁_in_g₂B₁ : a₁ n k m hn ∈ g₂ n k m '' B₁ := hSupp₃ (a₁_mem_support_g₁ hn)
      -- 3 ∉ B (since B ⊆ tailA and 3 is core)
      have h3_not_in_B : (⟨3, by omega⟩ : Omega n k m) ∉ B := by
        intro h3B; have := hB_subset_tailA _ h3B; simp only [isTailA] at this; omega
      have hB_ne_g₂B₁ : B ≠ g₂ n k m '' B₁ := fun heq => h3_not_in_B (heq ▸ h3_in_g₂B₁)
      exact Set.disjoint_iff.mp (hDisj hB hg₂B₁_block hB_ne_g₂B₁) ⟨ha₁_in_B, ha₁_in_g₂B₁⟩
    · -- Orbit continuation: g₂(B₁) contains 3 ∈ supp(g₁), and g₁(g₂(B₁)) contains 2 ∈ supp(g₁)
      -- Since B ⊆ tailA, B cannot be either of these (3, 2 are core elements)
      -- The orbit of g₂(B₁) partitions supp(g₁), so a₁ must be in some orbit block
      -- Either that block is B (contradiction via core elements) or not B (contradiction via partition)
      have hMeet : ((g₂ n k m '' B₁) ∩ ↑(g₁ n k m).support).Nonempty :=
        ⟨⟨3, by omega⟩, h3_in_g₂B₁, h3_in_supp⟩
      -- a₁ is in supp(g₁), so by the orbit partition it must be in some orbit block
      have ha₁_supp : a₁ n k m hn ∈ (g₁ n k m).support := a₁_mem_support_g₁ hn
      have hCover_supp := orbit_covers_support BS hInvOrig (g₂ n k m '' B₁) hg₂B₁_block hMeet
      have ha₁_in_orbit : a₁ n k m hn ∈ ⋃ C ∈ blockOrbit (g₁ n k m) (g₂ n k m '' B₁), C :=
        hCover_supp ha₁_supp
      simp only [Set.mem_iUnion] at ha₁_in_orbit
      obtain ⟨C, hC_orbit, ha₁_in_C⟩ := ha₁_in_orbit
      -- C is in the block system
      have hBlksFin : BS.blocks.Finite := Set.Finite.subset Set.finite_univ (Set.subset_univ _)
      have hC_block : C ∈ BS.blocks :=
        blockOrbit_subset_blocks (g₁_block_system_invariant BS hInvOrig) hBlksFin hg₂B₁_block hC_orbit
      -- Either C = B or C ≠ B
      by_cases hCB : C = B
      · -- C = B means B is in the orbit of g₂(B₁)
        obtain ⟨j, hj⟩ := hC_orbit
        -- We have hj : C = (g₁ ^ j) '' (g₂ '' B₁) and hCB : C = B
        -- Key insight: g₂(B₁) contains 3 (core) and g₁(g₂(B₁)) contains 2 (core)
        -- Since B ⊆ tailA, B cannot be g₂(B₁) or g₁(g₂(B₁))
        -- For other orbit positions, use that first few blocks all contain core elements
        have h3_not_tailA : ¬isTailA (⟨3, by omega⟩ : Omega n k m) := by
          simp only [isTailA]; omega
        have h2_not_tailA : ¬isTailA (⟨2, by omega⟩ : Omega n k m) := by
          simp only [isTailA]; omega
        -- 3 ∈ g₂(B₁), so if B = g₂(B₁) then B contains 3, contradicting B ⊆ tailA
        have hB_ne_g₂B₁ : B ≠ g₂ n k m '' B₁ := by
          intro heq
          have h3_in_B : (⟨3, by omega⟩ : Omega n k m) ∈ B := heq ▸ h3_in_g₂B₁
          exact h3_not_tailA (hB_subset_tailA _ h3_in_B)
        -- g₁(3) = 2 ∈ g₁(g₂(B₁)), so if B = g₁(g₂(B₁)) then B contains 2
        have h2_in_g₁g₂B₁ : (⟨2, by omega⟩ : Omega n k m) ∈ g₁ n k m '' (g₂ n k m '' B₁) :=
          ⟨⟨3, by omega⟩, h3_in_g₂B₁, g₁_elem3_eq_elem2⟩
        have hB_ne_g₁g₂B₁ : B ≠ g₁ n k m '' (g₂ n k m '' B₁) := by
          intro heq
          have h2_in_B : (⟨2, by omega⟩ : Omega n k m) ∈ B := heq ▸ h2_in_g₁g₂B₁
          exact h2_not_tailA (hB_subset_tailA _ h2_in_B)
        -- The orbit consists of g₁^j(g₂(B₁)) for j ∈ ℤ
        -- We've shown j ≠ 0 and j ≠ 1. For other j, use Lemma 11.4 cardinality argument:
        -- The support intersection size forces either:
        -- (1) |B ∩ supp(g₁)| = 1 (r = n+4), but then B is essentially a singleton
        --     since non-support elements include 1, tailB, tailC (not in tailA)
        -- (2) |B ∩ supp(g₁)| ≥ 2 (r < n+4), but cosets hit core elements
        -- Either way, B ⊆ tailA with |B| > 1 is impossible
        -- The detailed proof is deferred to a helper using Lemma 11.4 machinery
        rcases j with (j | j)
        · -- j is a natural number (non-negative)
          cases j with
          | zero => -- j = 0: B = g₂(B₁)
            -- hj : C = (g₁ ^ (0:ℤ)) '' (g₂ '' B₁) = g₂ '' B₁
            have hC_eq : C = g₂ n k m '' B₁ := by
              have h0 : Int.ofNat 0 = (0 : ℤ) := rfl
              rw [h0, zpow_zero, Equiv.Perm.coe_one, Set.image_id] at hj
              exact hj
            exact hB_ne_g₂B₁ (hCB.symm.trans hC_eq)
          | succ j' =>
            cases j' with
            | zero => -- j = 1: B = g₁(g₂(B₁))
              have hC_eq : C = g₁ n k m '' (g₂ n k m '' B₁) := by
                have h1 : Int.ofNat (0 + 1) = (1 : ℤ) := rfl
                rw [h1, zpow_one] at hj
                exact hj
              exact hB_ne_g₁g₂B₁ (hCB.symm.trans hC_eq)
            | succ _ => -- j ≥ 2: use cardinality argument (deferred)
              sorry
        · -- j is negative (Int.negSucc j'): power is -(j'+1) = -1, -2, -3, ...
          -- Key insight: g₁⁻¹(3) = 5 (core), g₁⁻²(3) = 0 (core)
          -- For all negative j, the orbit block contains a core element
          -- Deferred: full proof for all negative cases
          -- The key observation is that the first two negative positions hit core elements
          -- and the cycle structure ensures this pattern continues
          sorry
      · -- C ≠ B: a₁ ∈ C and a₁ ∈ B contradicts partition disjointness
        have hB_ne_C : B ≠ C := fun h => hCB h.symm
        exact Set.disjoint_iff.mp (hDisj hB hC_block hB_ne_C) ⟨ha₁_in_B, ha₁_in_C⟩
