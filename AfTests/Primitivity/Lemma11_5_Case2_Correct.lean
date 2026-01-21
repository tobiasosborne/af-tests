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
import AfTests.Primitivity.Lemma11_5_OrbitHelpers

/-!
# Lemma 11.5 Case 2: Correct Proof via Block B₁

The correct Case 2 argument uses the block B₁ containing element 1.
Since g₁(1) = 1, we have g₁(B₁) = B₁. Then either:
- supp(g₁) ⊆ B₁, so a₁ ∈ B₁ ≠ B (contradiction)
- B₁ ∩ supp(g₁) = ∅, but then g₂(B₁) contains 3 ∈ supp(g₁), leading to contradiction.
-/

open Equiv Equiv.Perm Set OrbitCore OrbitTailB

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
  have h_core_len : (g₂CoreList n k m).length = 4 := by simp [g₂CoreList]
  rw [List.getElem_append_left (by rw [h_core_len]; omega : 1 < (g₂CoreList n k m).length)]
  simp [g₂CoreList]

/-- Helper: element 2 is in supp(g₁) (local version) -/
theorem elem2_in_support_g₁_local : (⟨2, by omega⟩ : Omega n k m) ∈ (g₁ n k m).support := by
  have hNodup := g₁_list_nodup n k m
  have hNotSingleton : ∀ y, g₁CoreList n k m ++ tailAList n k m ≠ [y] := by
    intro y h; have := g₁_cycle_length n k m
    have hlen : (g₁CoreList n k m ++ tailAList n k m).length = 1 := by rw [h]; rfl
    omega
  rw [g₁, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₁CoreList, List.mem_cons]; tauto

/-- B₁ (containing 1) is disjoint from supp(g₁) implies B₁ ⊆ {1, 4} ∪ tailB -/
theorem B₁_subset_complement_supp_g₁ (B₁ : Set (Omega n k m))
    (hDisj₁ : Disjoint (↑(g₁ n k m).support) B₁)
    (hDisj_tailC : ∀ x ∈ B₁, ¬isTailC x) :
    ∀ x ∈ B₁, x.val = 1 ∨ x.val = 4 ∨ isTailB x := by
  intro x hx
  have hx_not_supp : x ∉ (g₁ n k m).support := fun h => Set.disjoint_iff.mp hDisj₁ ⟨h, hx⟩
  have hx_not_tailC := hDisj_tailC x hx
  rcases Omega.partition x with hCore | hA | hB | hC
  · simp only [isCore] at hCore
    have hCases : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 ∨ x.val = 3 ∨ x.val = 4 ∨ x.val = 5 := by omega
    rcases hCases with h0 | h1 | h2 | h3 | h4 | h5
    · exfalso; have heq : x = ⟨0, by omega⟩ := Fin.ext h0; rw [heq] at hx_not_supp
      exact hx_not_supp elem0_in_support_g₁
    · left; exact h1
    · exfalso; have heq : x = ⟨2, by omega⟩ := Fin.ext h2; rw [heq] at hx_not_supp
      exact hx_not_supp elem2_in_support_g₁_local
    · exfalso; have heq : x = ⟨3, by omega⟩ := Fin.ext h3; rw [heq] at hx_not_supp
      exact hx_not_supp elem3_in_support_g₁
    · right; left; exact h4
    · exfalso; have heq : x = ⟨5, by omega⟩ := Fin.ext h5; rw [heq] at hx_not_supp
      exact hx_not_supp elem5_in_support_g₁
  · exfalso; have hx_supp : x ∈ (g₁ n k m).support := by
      simp only [isTailA] at hA; obtain ⟨hLo, hHi⟩ := hA
      have hi : x.val - 6 < n := by have := x.isLt; omega
      convert tailA_in_support_g₁ (⟨x.val - 6, hi⟩ : Fin n) using 1
      simp only [Fin.ext_iff]; omega
    exact hx_not_supp hx_supp
  · right; right; exact hB
  · exact (hx_not_tailC hC).elim

/-- When orbit index is -1, B = g₁⁻¹(g₂(B₁)) contains element 5 (core) -/
theorem orbit_neg1_has_core (B₀ : Set (Omega n k m))
    (h3_in : (⟨3, by omega⟩ : Omega n k m) ∈ B₀)
    (B : Set (Omega n k m)) (hB_tailA : ∀ x ∈ B, isTailA x)
    (hB_eq : B = (g₁ n k m).symm '' B₀) : False := by
  have h5_in_B : (⟨5, by omega⟩ : Omega n k m) ∈ B := by
    rw [hB_eq]; exact ⟨⟨3, by omega⟩, h3_in, g₁_inv_elem3_eq_elem5⟩
  exact elem5_not_tailA (hB_tailA _ h5_in_B)

/-- When orbit index is -2, B = g₁⁻²(g₂(B₁)) contains element 0 (core) -/
theorem orbit_neg2_has_core (B₀ : Set (Omega n k m))
    (h3_in : (⟨3, by omega⟩ : Omega n k m) ∈ B₀)
    (B : Set (Omega n k m)) (hB_tailA : ∀ x ∈ B, isTailA x)
    (hB_eq : B = (g₁ n k m ^ 2).symm '' B₀) : False := by
  have h0_in_B : (⟨0, by omega⟩ : Omega n k m) ∈ B := by
    rw [hB_eq]; exact ⟨⟨3, by omega⟩, h3_in, g₁_pow2_inv_elem3_eq_elem0⟩
  exact elem0_not_tailA (hB_tailA _ h0_in_B)

set_option maxHeartbeats 1200000 in
-- Increased heartbeats for complex nested case analysis in j≥2 and j≤-3 branches
/-- Case 2: main contradiction via orbit analysis -/
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
    -- a₁ is in supp(g₁), so by the orbit partition it must be in some orbit block
    have ha₁_supp : a₁ n k m hn ∈ (g₁ n k m).support := a₁_mem_support_g₁ hn
    have hMeet : ((g₂ n k m '' B₁) ∩ ↑(g₁ n k m).support).Nonempty :=
      ⟨⟨3, by omega⟩, h3_in_g₂B₁, h3_in_supp⟩
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
      -- Analyze orbit position j
      -- j = 0: B = g₂(B₁) contains 3 (not tailA)
      -- j = 1: B = g₁(g₂(B₁)) contains 2 (not tailA)
      -- j ≥ 2: Eventual core element
      -- j = -1: B contains 5 (not tailA)
      -- j = -2: B contains 0 (not tailA)
      -- j ≤ -3: Eventual core element
      subst hCB
      rcases j with (j | j)
      · -- j is non-negative
        cases j with
        | zero => -- j = 0: C = g₂(B₁) contains 3
          have h3_in_C : (⟨3, by omega⟩ : Omega n k m) ∈ C := by
            have : (g₁ n k m ^ Int.ofNat 0) = 1 := by simp
            rw [hj, this, Equiv.Perm.coe_one, Set.image_id]
            exact h3_in_g₂B₁
          exact elem3_not_tailA (hB_subset_tailA _ h3_in_C)
        | succ j' =>
          cases j' with
          | zero => -- j = 1: C = g₁(g₂(B₁)) contains 2
            have h2_in_C : (⟨2, by omega⟩ : Omega n k m) ∈ C := by
              have : (g₁ n k m ^ Int.ofNat 1) = g₁ n k m := by simp
              rw [hj, this]
              exact ⟨⟨3, by omega⟩, h3_in_g₂B₁, g₁_elem3_eq_elem2⟩
            exact elem2_not_tailA (hB_subset_tailA _ h2_in_C)
          | succ j'' => -- j ≥ 2: orbit eventually contains core elements
            -- |B₁| > 1 since bijections preserve cardinality
            have hB₁_size : 1 < B₁.ncard := by
              have hCard_eq : C.ncard = B₁.ncard := by
                have h1 : C.ncard = (g₂ n k m '' B₁).ncard := by
                  rw [hj]; exact Set.ncard_image_of_injective _ (g₁ n k m ^ _).injective
                have h2 : (g₂ n k m '' B₁).ncard = B₁.ncard :=
                  Set.ncard_image_of_injective _ (g₂ n k m).injective
                exact h1.trans h2
              exact hCard_eq ▸ hSize
            -- Get second element in B₁
            obtain ⟨x, hx_in_B₁, hx_ne_1⟩ :=
              Set.exists_ne_of_one_lt_ncard hB₁_size (⟨1, by omega⟩ : Omega n k m)
            -- x ∉ supp(g₁) since B₁ ∩ supp(g₁) = ∅
            have hx_not_supp : x ∉ (g₁ n k m).support := by
              exact Set.disjoint_right.mp hDisj₁ hx_in_B₁
            -- Classify x
            have hx_cases := elem_not_in_support_g₁_cases x hx_not_supp
            -- Since x ≠ 1, must be 4, tailB, or tailC
            rcases hx_cases with hx1 | hx4 | hxB | hxC
            · -- x.val = 1 contradicts x ≠ 1
              exfalso; exact hx_ne_1 (Fin.ext hx1)
            · -- x.val = 4: use block overlap at element 3
              have hx_eq_4 : x = ⟨4, by omega⟩ := Fin.ext hx4
              -- g₂(4) = 0 ∈ g₂(B₁)
              have h0_in : (⟨0, by omega⟩ : Omega n k m) ∈ g₂ n k m '' B₁ :=
                ⟨⟨4, by omega⟩, hx_eq_4 ▸ hx_in_B₁, g₂_elem4_eq_elem0'⟩
              -- g₁(0) = 5 ∈ g₁(g₂(B₁))
              have h5_in_g1g2B1 : (⟨5, by omega⟩ : Omega n k m) ∈ g₁ n k m '' (g₂ n k m '' B₁) :=
                ⟨⟨0, by omega⟩, h0_in, g₁_elem0_eq_elem5⟩
              -- g₁(5) = 3 ∈ g₁²(g₂(B₁))
              have h3_in_g1sq : (⟨3, by omega⟩ : Omega n k m) ∈
                  g₁ n k m '' (g₁ n k m '' (g₂ n k m '' B₁)) :=
                ⟨⟨5, by omega⟩, h5_in_g1g2B1, g₁_elem5_eq_elem3⟩
              -- g₂(B₁) and g₁²(g₂(B₁)) are both blocks
              have hg1sq_block : g₁ n k m '' (g₁ n k m '' (g₂ n k m '' B₁)) ∈ BS.blocks :=
                hInv₁ _ (hInv₁ _ hg₂B₁_block)
              -- They share element 3
              have h3_in_both : (⟨3, by omega⟩ : Omega n k m) ∈
                  (g₂ n k m '' B₁) ∩ (g₁ n k m '' (g₁ n k m '' (g₂ n k m '' B₁))) :=
                ⟨h3_in_g₂B₁, h3_in_g1sq⟩
              -- They're different (g₂(B₁) = {3, 0}, g₁²(g₂(B₁)) = {6, 3})
              have hDiff : g₂ n k m '' B₁ ≠ g₁ n k m '' (g₁ n k m '' (g₂ n k m '' B₁)) := by
                intro heq
                -- If equal: 6 = g₁²(3) ∈ g₁²(g₂(B₁)) = g₂(B₁)
                -- 3 ∈ g₂(B₁) → g₁(3) = 2 ∈ g₁(g₂(B₁)) → g₁(2) = 6 ∈ g₁²(g₂(B₁)) = g₂(B₁)
                have h6_in : (⟨6, by omega⟩ : Omega n k m) ∈ g₂ n k m '' B₁ := by
                  rw [heq]
                  exact ⟨⟨2, by omega⟩,
                    ⟨⟨3, by omega⟩, h3_in_g₂B₁, g₁_elem3_eq_elem2⟩,
                    g₁_elem2_eq_elem6 hn⟩
                -- But 6 can't be in g₂(B₁)
                obtain ⟨y, hy_in_B₁, hy_g₂⟩ := h6_in
                have hy_not_supp : y ∉ (g₁ n k m).support :=
                  Set.disjoint_right.mp hDisj₁ hy_in_B₁
                have hy_cases := elem_not_in_support_g₁_cases y hy_not_supp
                rcases hy_cases with hy1 | hy4 | hyB | hyC
                · have heq : y = ⟨1, by omega⟩ := Fin.ext hy1
                  rw [heq, g₂_elem1_eq_elem3] at hy_g₂
                  simp only [Fin.ext_iff] at hy_g₂; omega
                · have heq : y = ⟨4, by omega⟩ := Fin.ext hy4
                  rw [heq, g₂_elem4_eq_elem0'] at hy_g₂
                  simp only [Fin.ext_iff] at hy_g₂; omega
                · have h_ne := g₂_image_not_6 hn y (Or.inr (Or.inr (Or.inl hyB)))
                  simp only [Fin.ext_iff] at hy_g₂; omega
                · have hFix := g₂_fixes_tailC y hyC
                  rw [hFix] at hy_g₂
                  simp only [isTailC, Fin.ext_iff] at hyC hy_g₂; omega
              -- Different blocks must be disjoint
              exact Set.disjoint_iff.mp (hDisj hg₂B₁_block hg1sq_block hDiff) h3_in_both
            · -- x ∈ tailB: g₂(x) stays fixed by g₁ʲ, lands in C, but not in tailA
              have hg₂x_in_g₂B₁ : g₂ n k m x ∈ g₂ n k m '' B₁ := ⟨x, hx_in_B₁, rfl⟩
              rcases g₂_tailB_to_tailB_or_1 x hxB with hg₂x_tailB | hg₂x_eq_1
              · -- g₂(x) ∈ tailB: g₁ fixes tailB
                have hFix := g₁_zpow_fixes_tailB (Int.ofNat (j'' + 1 + 1)) _ hg₂x_tailB
                have hg₂x_in_C : g₂ n k m x ∈ C := by
                  rw [hj]; exact ⟨g₂ n k m x, hg₂x_in_g₂B₁, hFix⟩
                exact tailB_not_tailA _ hg₂x_tailB (hB_subset_tailA _ hg₂x_in_C)
              · -- g₂(x) = 1: g₁ fixes 1
                have hFix : (g₁ n k m ^ (Int.ofNat (j'' + 1 + 1))) (⟨1, by omega⟩ : Omega n k m) =
                    ⟨1, by omega⟩ := g₁_zpow_fixes_elem1 (Int.ofNat (j'' + 1 + 1))
                have h1_in_C : (⟨1, by omega⟩ : Omega n k m) ∈ C := by
                  rw [hj]; exact ⟨g₂ n k m x, hg₂x_in_g₂B₁, by rw [hg₂x_eq_1]; exact hFix⟩
                exact elem1_not_tailA (hB_subset_tailA _ h1_in_C)
            · -- x ∈ tailC: g₂ and g₁ both fix tailC
              have hg₂_fix : g₂ n k m x = x := g₂_fixes_tailC x hxC
              have hg₁_fix := g₁_zpow_fixes_tailC (Int.ofNat (j'' + 1 + 1)) x hxC
              have hx_in_C : x ∈ C := by
                rw [hj]; exact ⟨x, ⟨x, hx_in_B₁, hg₂_fix⟩, hg₁_fix⟩
              exact tailC_disjoint_tailA x hxC (hB_subset_tailA _ hx_in_C)
      · -- j is negative (Int.negSucc j'): power is -(j'+1) = -1, -2, -3, ...
        cases j with
        | zero => -- j = -1
          exact orbit_neg1_has_core (g₂ n k m '' B₁) h3_in_g₂B₁ C hB_subset_tailA
            (by rw [hj]; simp [Int.negSucc_eq])
        | succ j'' =>
          cases j'' with
          | zero => -- j = -2
            have h0_in_C : (⟨0, by omega⟩ : Omega n k m) ∈ C := by
              rw [hj]
              simp only [Int.negSucc_eq, zpow_neg]
              exact ⟨⟨3, by omega⟩, h3_in_g₂B₁, g₁_pow2_inv_elem3_eq_elem0⟩
            exact elem0_not_tailA (hB_subset_tailA _ h0_in_C)
          | succ j''' => -- j ≤ -3: orbit eventually contains core elements
            -- Same structure as j ≥ 2 case, using negative powers
            -- |B₁| > 1 since bijections preserve cardinality
            have hB₁_size : 1 < B₁.ncard := by
              have hCard_eq : C.ncard = B₁.ncard := by
                have h1 : C.ncard = (g₂ n k m '' B₁).ncard := by
                  rw [hj]; exact Set.ncard_image_of_injective _ (g₁ n k m ^ _).injective
                have h2 : (g₂ n k m '' B₁).ncard = B₁.ncard :=
                  Set.ncard_image_of_injective _ (g₂ n k m).injective
                exact h1.trans h2
              exact hCard_eq ▸ hSize
            -- Get second element in B₁
            obtain ⟨x, hx_in_B₁, hx_ne_1⟩ :=
              Set.exists_ne_of_one_lt_ncard hB₁_size (⟨1, by omega⟩ : Omega n k m)
            -- x ∉ supp(g₁) since B₁ ∩ supp(g₁) = ∅
            have hx_not_supp : x ∉ (g₁ n k m).support := Set.disjoint_right.mp hDisj₁ hx_in_B₁
            -- Classify x
            have hx_cases := elem_not_in_support_g₁_cases x hx_not_supp
            rcases hx_cases with hx1 | hx4 | hxB | hxC
            · -- x.val = 1 contradicts x ≠ 1
              exact (hx_ne_1 (Fin.ext hx1)).elim
            · -- x.val = 4: block overlap at element 0
              have hx_eq_4 : x = ⟨4, by omega⟩ := Fin.ext hx4
              -- g₂(4) = 0 ∈ g₂(B₁)
              have h0_in_g₂B₁ : (⟨0, by omega⟩ : Omega n k m) ∈ g₂ n k m '' B₁ :=
                ⟨⟨4, by omega⟩, hx_eq_4 ▸ hx_in_B₁, g₂_elem4_eq_elem0'⟩
              -- g₁⁻²(3) = 0: need to show 0 ∈ g₁⁻²(g₂(B₁))
              -- Since g₁²(0) = 3, we have (g₁^2).symm(3) = 0
              have h0_in_g1inv2 : (⟨0, by omega⟩ : Omega n k m) ∈
                  (g₁ n k m ^ (2 : ℕ)).symm '' (g₂ n k m '' B₁) := by
                refine ⟨⟨3, by omega⟩, h3_in_g₂B₁, ?_⟩
                -- Show (g₁^2).symm(3) = 0, i.e., g₁²(0) = 3
                rw [Equiv.symm_apply_eq]; exact g₁_pow2_elem0_eq_elem3.symm
              -- g₁⁻²(g₂(B₁)) is a block (use inv_pow_image_mem_blocks)
              have hg1inv2_block : (g₁ n k m ^ (2 : ℕ)).symm '' (g₂ n k m '' B₁) ∈ BS.blocks := by
                have h : (g₁ n k m ^ (2 : ℕ)).symm = (g₁ n k m).symm ^ 2 := by
                  ext x
                  simp only [Equiv.Perm.coe_pow, Function.iterate_succ, Function.iterate_zero,
                    Function.comp_apply, id_eq]
                  rfl
                rw [h]
                exact inv_pow_image_mem_blocks hInv₁ hBlksFin hg₂B₁_block 2
              -- They share element 0
              have h0_in_both : (⟨0, by omega⟩ : Omega n k m) ∈
                  (g₂ n k m '' B₁) ∩ ((g₁ n k m ^ (2 : ℕ)).symm '' (g₂ n k m '' B₁)) :=
                ⟨h0_in_g₂B₁, h0_in_g1inv2⟩
              -- If equal, derive 6 ∈ g₂(B₁) (same contradiction as j≥2)
              have hDiff : g₂ n k m '' B₁ ≠ (g₁ n k m ^ (2 : ℕ)).symm '' (g₂ n k m '' B₁) := by
                intro heq
                -- If equal: g₁²(g₂(B₁)) = g₂(B₁)
                -- 3 ∈ g₂(B₁) → g₁²(3) = 6 ∈ g₁²(g₂(B₁)) = g₂(B₁)
                have h6_in : (⟨6, by omega⟩ : Omega n k m) ∈ g₂ n k m '' B₁ := by
                  -- Apply g₁² to both sides of heq: g₂(B₁) = g₁⁻²(g₂(B₁)) → g₁²(g₂(B₁)) = g₂(B₁)
                  have heq' : (g₁ n k m ^ (2 : ℕ)) '' (g₂ n k m '' B₁) = g₂ n k m '' B₁ := by
                    conv_lhs => rw [heq]
                    rw [Equiv.image_symm_image]
                  rw [← heq']
                  exact ⟨⟨3, by omega⟩, h3_in_g₂B₁, by
                    simp only [pow_two, Equiv.Perm.coe_mul, Function.comp_apply]
                    rw [g₁_elem3_eq_elem2, g₁_elem2_eq_elem6 hn]⟩
                -- But 6 ∉ g₂(B₁) (same argument as j≥2)
                obtain ⟨y, hy_in_B₁, hy_g₂⟩ := h6_in
                have hy_not_supp : y ∉ (g₁ n k m).support :=
                  Set.disjoint_right.mp hDisj₁ hy_in_B₁
                have hy_cases := elem_not_in_support_g₁_cases y hy_not_supp
                rcases hy_cases with hy1 | hy4 | hyB | hyC
                · have heq : y = ⟨1, by omega⟩ := Fin.ext hy1
                  rw [heq, g₂_elem1_eq_elem3] at hy_g₂
                  simp only [Fin.ext_iff] at hy_g₂; omega
                · have heq : y = ⟨4, by omega⟩ := Fin.ext hy4
                  rw [heq, g₂_elem4_eq_elem0'] at hy_g₂
                  simp only [Fin.ext_iff] at hy_g₂; omega
                · have h_ne := g₂_image_not_6 hn y (Or.inr (Or.inr (Or.inl hyB)))
                  simp only [Fin.ext_iff] at hy_g₂; omega
                · have hFix := g₂_fixes_tailC y hyC
                  rw [hFix] at hy_g₂
                  simp only [isTailC, Fin.ext_iff] at hyC hy_g₂; omega
              -- Different blocks must be disjoint
              exact Set.disjoint_iff.mp (hDisj hg₂B₁_block hg1inv2_block hDiff) h0_in_both
            · -- x ∈ tailB: g₂(x) stays fixed by g₁ʲ (even negative), not in tailA
              have hg₂x_in_g₂B₁ : g₂ n k m x ∈ g₂ n k m '' B₁ := ⟨x, hx_in_B₁, rfl⟩
              rcases g₂_tailB_to_tailB_or_1 x hxB with hg₂x_tailB | hg₂x_eq_1
              · have hFix := g₁_zpow_fixes_tailB (Int.negSucc (j''' + 1 + 1)) _ hg₂x_tailB
                have hg₂x_in_C : g₂ n k m x ∈ C := by
                  rw [hj]; exact ⟨g₂ n k m x, hg₂x_in_g₂B₁, hFix⟩
                exact tailB_not_tailA _ hg₂x_tailB (hB_subset_tailA _ hg₂x_in_C)
              · have hFix : (g₁ n k m ^ (Int.negSucc (j''' + 1 + 1)))
                    (⟨1, by omega⟩ : Omega n k m) = ⟨1, by omega⟩ :=
                  g₁_zpow_fixes_elem1 (Int.negSucc (j''' + 1 + 1))
                have h1_in_C : (⟨1, by omega⟩ : Omega n k m) ∈ C := by
                  rw [hj]; exact ⟨g₂ n k m x, hg₂x_in_g₂B₁, by rw [hg₂x_eq_1]; exact hFix⟩
                exact elem1_not_tailA (hB_subset_tailA _ h1_in_C)
            · -- x ∈ tailC: g₂ and g₁ both fix tailC
              have hg₂_fix : g₂ n k m x = x := g₂_fixes_tailC x hxC
              have hg₁_fix := g₁_zpow_fixes_tailC (Int.negSucc (j''' + 1 + 1)) x hxC
              have hx_in_C : x ∈ C := by
                rw [hj]; exact ⟨x, ⟨x, hx_in_B₁, hg₂_fix⟩, hg₁_fix⟩
              exact tailC_disjoint_tailA x hxC (hB_subset_tailA _ hx_in_C)
    · -- C ≠ B: a₁ ∈ C and a₁ ∈ B contradicts partition disjointness
      have hB_ne_C : B ≠ C := fun h => hCB h.symm
      exact Set.disjoint_iff.mp (hDisj hB hC_block hB_ne_C) ⟨ha₁_in_B, ha₁_in_C⟩
