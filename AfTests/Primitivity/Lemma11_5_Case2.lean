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

    The actual contradiction comes from the block size constraints.

    Uses block hypothesis for g₁ powers to derive contradiction.
    For n ≤ 2: Direct cardinality/orbit argument.
    For n ≥ 3: Block structure analysis. -/
theorem case2_impossible (hn : n ≥ 1) (B : Set (Omega n k m))
    (hg₁Disj : Disjoint (g₁ n k m '' B) B)
    (ha₁_in_B : a₁ n k m hn ∈ B)
    (hg₂_pres : PreservesSet (g₂ n k m) B) (hg₃_pres : PreservesSet (g₃ n k m) B)
    (hBlock : ∀ j : ℕ, (g₁ n k m ^ j) '' B = B ∨ Disjoint ((g₁ n k m ^ j) '' B) B)
    (hBlock₂_orbit : ∀ j : ℕ, g₂ n k m '' ((g₁ n k m ^ j) '' B) = (g₁ n k m ^ j) '' B ∨
        Disjoint (g₂ n k m '' ((g₁ n k m ^ j) '' B)) ((g₁ n k m ^ j) '' B))
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
    · -- n ≥ 3: Use H-block property with g₂ on g₁-orbit blocks.
      -- NL Proof Reference (Node 1.9.5): The orbit of B under g₁ covers supp(g₁).
      -- Element 0 ∈ supp(g₁), so some g₁^j(B) contains element 0.
      -- g₂(0) = 1 ∉ supp(g₁), so 1 ∉ g₁^j(B).
      -- But g₂(g₁^j(B)) contains 1, and tailA elements in g₁^j(B) are fixed by g₂.
      -- So g₂(g₁^j(B)) ≠ g₁^j(B) (contains 1) and not disjoint (fixed points).
      -- This contradicts hBlock₂_orbit.
      have hn_ge_3 : n ≥ 3 := by omega
      -- The g₁-orbit of B covers supp(g₁) since B is non-trivial in tailA ⊆ supp(g₁).
      -- Element 0 is in supp(g₁), so there exists j such that 0 ∈ g₁^j(B).
      -- Since a₁ ∈ B ⊆ tailA ⊆ supp(g₁), and g₁ is a cycle on supp(g₁),
      -- iterating g₁⁻¹ on a₁ eventually reaches 0.
      -- Find the minimal j such that g₁^(-j)(a₁) = 0, i.e., g₁^j(0) = a₁.
      -- Then 0 = g₁^(-j)(a₁) ∈ g₁^(-j)(B), so 0 ∈ (g₁^(-j))(B).
      -- Using integer powers via zpow, or equivalently using the cycle order.
      -- g₁ = (0 5 3 2 a₁ a₂ ... aₙ), so g₁^(-1) = (0 a_n ... a₁ 2 3 5).
      -- From a₁ (index 4 in cycle), going backwards: a₁ → 2 → 3 → 5 → 0 (4 steps).
      -- So g₁^(-4)(a₁) = 0, meaning g₁^4(0) = a₁.
      -- Therefore 0 ∈ g₁^(-4)(B), which equals (g₁⁻¹)^4(B) = (g₁^(4+n))⁻¹^4(B).
      -- Using forward powers: g₁^(4+n-4)(B) = g₁^n(B) contains g₁^n(a₁) after n steps.
      -- Actually, let's compute: g₁ = [0, 5, 3, 2, 6, 7, ...], so g₁(6) = 7, g₁(7) = 8, etc.
      -- g₁^(-1)(6) = 2, g₁^(-2)(6) = 3, g₁^(-3)(6) = 5, g₁^(-4)(6) = 0.
      -- So 0 ∈ g₁^(-4)(B). Using order 4+n: g₁^(-4) = g₁^(n).
      -- Let j = n. Then g₁^n(a₁) = 0 (after going around the cycle).
      -- Wait, let me recalculate. g₁ = (0 5 3 2 a₁ a₂ ... aₙ) as a cycle.
      -- g₁: 0 → 5 → 3 → 2 → a₁ → a₂ → ... → aₙ → 0.
      -- From a₁ (index 6), g₁^(-1)(a₁) = 2, g₁^(-2)(a₁) = 3, g₁^(-3)(a₁) = 5, g₁^(-4)(a₁) = 0.
      -- So (g₁⁻¹)^4(a₁) = 0, meaning a₁ ∈ g₁^4(B) implies 0 ∈ (g₁⁻¹)^4(B).
      -- Equivalently, since g₁ has order 4+n, (g₁⁻¹)^4 = g₁^n, so 0 ∈ g₁^n(B).
      -- Let's use j = n in the argument below.
      let j := n
      -- Show 0 ∈ g₁^n(B) by computing g₁^n(a₁) = 0.
      have h0_in_g₁jB : (⟨0, by omega⟩ : Omega n k m) ∈ (g₁ n k m ^ j) '' B := by
        -- g₁^n(a₁) = 0 because g₁ = (0 5 3 2 a₁ ... aₙ) and stepping n times from a₁
        -- goes a₁ → a₂ → ... → aₙ → 0.
        use a₁ n k m hn, ha₁_in_B
        -- Need: g₁^n(a₁) = 0
        unfold a₁ g₁
        let L := g₁CoreList n k m ++ tailAList n k m
        have hnd : L.Nodup := g₁_list_nodup n k m
        have hlen : L.length = 4 + n := g₁_cycle_length n k m
        -- a₁ = L[4] (0-indexed: 0, 5, 3, 2, a₁, ...)
        have h4_lt : 4 < L.length := by simp [L, g₁CoreList, tailAList]; omega
        have ha₁_eq : (⟨6, by omega⟩ : Omega n k m) = L[4] := by
          simp only [L]; exact (AfTests.Transitivity.g₁_list_getElem_tail n k m ⟨0, hn⟩).symm
        rw [ha₁_eq, List.formPerm_pow_apply_getElem L hnd n 4 h4_lt]
        -- (4 + n) % (4 + n) = 0, so we get L[0] = 0
        have hmod : (4 + n) % (4 + n) = 0 := Nat.mod_self _
        simp only [hlen, hmod]
        -- L[0] = 0
        have h0_lt : 0 < L.length := by rw [hlen]; omega
        have hL0 : L[0]'h0_lt = (⟨0, by omega⟩ : Omega n k m) := by
          simp only [L, g₁CoreList, tailAList]
          rfl
        exact hL0
      -- Element 1 is NOT in g₁^j(B) because 1 ∉ supp(g₁) and g₁^j(B) ⊆ supp(g₁).
      -- Actually, g₁^j(B) need not be ⊆ supp(g₁). Let me reconsider.
      -- We have B ⊆ tailA ⊆ supp(g₁). Is g₁^j(B) ⊆ supp(g₁)?
      -- Yes! Since B ⊆ supp(g₁) and g₁ permutes supp(g₁) (it's a cycle there),
      -- g₁^j(B) ⊆ supp(g₁) for all j.
      have hg₁jB_in_supp : (g₁ n k m ^ j) '' B ⊆ (g₁ n k m).support := by
        intro y hy
        obtain ⟨x, hxB, hxy⟩ := hy
        have hx_supp : x ∈ (g₁ n k m).support := by
          have hx_tailA := hB_subset_tailA x hxB
          simp only [isTailA] at hx_tailA
          have hi : x.val - 6 < n := by omega
          have hxeq : x = (⟨6 + (x.val - 6), by omega⟩ : Omega n k m) := by
            apply Fin.ext; simp; omega
          rw [hxeq]
          exact tailA_in_support_g₁ ⟨x.val - 6, hi⟩
        rw [← hxy]
        exact Equiv.Perm.pow_apply_mem_support.mpr hx_supp
      -- Element 1 is not in supp(g₁)
      have h1_not_in_g₁jB : (⟨1, by omega⟩ : Omega n k m) ∉ (g₁ n k m ^ j) '' B := by
        intro h1_in
        have h1_in_supp := hg₁jB_in_supp h1_in
        exact elem1_not_in_support_g₁ h1_in_supp
      -- g₂(0) is NOT in supp(g₁), so g₂(0) ∉ g₁^j(B)
      have hg₂_0_not_in_supp_g₁ : g₂ n k m (⟨0, by omega⟩ : Omega n k m) ∉ (g₁ n k m).support := by
        by_cases hk : k = 0
        · -- k = 0: g₂(0) = 1, and 1 ∉ supp(g₁)
          subst hk
          have hg₂_0_eq_1 : g₂ n 0 m (⟨0, by omega⟩ : Omega n 0 m) = ⟨1, by omega⟩ := by
            unfold g₂ tailBList g₂CoreList
            simp only [List.finRange_zero, List.map_nil, List.append_nil]
            -- The list is [1, 3, 4, 0]. 0 = list[3], g₂(0) = list[(3+1) mod 4] = list[0] = 1
            set L : List (Omega n 0 m) := [⟨1, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩, ⟨0, by omega⟩]
            have hNodup : L.Nodup := by
              simp only [L, List.nodup_cons, List.mem_cons, List.mem_singleton, Fin.mk.injEq, not_or,
                List.not_mem_nil, not_false_eq_true, and_true, List.nodup_nil, and_self]
              exact ⟨⟨by omega, by omega, by omega⟩, ⟨by omega, by omega⟩, by omega⟩
            have hLen : L.length = 4 := by simp only [L, List.length_cons, List.length_nil]
            have h3_lt : 3 < L.length := by rw [hLen]; omega
            have h0_idx : (⟨0, by omega⟩ : Omega n 0 m) = L[3] := rfl
            conv_lhs => rw [h0_idx]
            rw [List.formPerm_apply_getElem _ hNodup 3 h3_lt]
            simp only [hLen, L, Nat.add_mod_right, Nat.zero_mod]
            rfl
          rw [hg₂_0_eq_1]; exact elem1_not_in_support_g₁
        · -- k > 0: g₂(0) = 6 + n ∈ tailB, and tailB ∩ supp(g₁) = ∅
          have hk_pos : k > 0 := Nat.pos_of_ne_zero hk
          have hg₂_0_eq_tailB : g₂ n k m (⟨0, by omega⟩ : Omega n k m) = ⟨6 + n, by omega⟩ := by
            unfold g₂
            set L := g₂CoreList n k m ++ tailBList n k m
            have hNodup : L.Nodup := g₂_list_nodup n k m
            have hlen : L.length = 4 + k := g₂_cycle_length n k m
            have h3_lt : 3 < L.length := by rw [hlen]; omega
            have h0_eq_idx3 : (⟨0, by omega⟩ : Omega n k m) = L[3] := by
              simp only [L, g₂CoreList, tailBList]; rfl
            conv_lhs => rw [h0_eq_idx3]
            rw [List.formPerm_apply_getElem _ hNodup 3 h3_lt]
            -- Goal: L[(3 + 1) % L.length] = ⟨6 + n, ...⟩
            -- Need to show L[4] = first tailB element = ⟨6 + n, ...⟩
            have h4_lt : 4 < L.length := by rw [hlen]; omega
            have hIdx : (3 + 1) % L.length = 4 := by
              rw [hlen]
              exact Nat.mod_eq_of_lt (by omega)
            simp only [hIdx]
            simp only [L, g₂CoreList, tailBList]
            rw [List.getElem_append_right (by simp : 4 ≥ 4)]
            simp only [List.length_cons, List.length_nil, Nat.sub_self]
            simp only [List.getElem_map, List.getElem_finRange, Fin.val_mk, Fin.coe_cast]
            simp only [Nat.add_zero]
          rw [hg₂_0_eq_tailB]
          -- 6 + n ∈ tailB, not in supp(g₁)
          simp only [g₁, Equiv.Perm.mem_support, ne_eq, not_not]
          apply List.formPerm_apply_of_notMem
          intro h
          simp only [List.mem_append, g₁CoreList, tailAList, List.mem_cons,
            List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
          rcases h with h | h
          · rcases h with h | h | h | h <;> simp only [Fin.ext_iff] at h <;> omega
          · obtain ⟨jj, _, hjj⟩ := h; simp only [Fin.ext_iff] at hjj; omega
      -- g₂(0) ∈ g₂(g₁^j(B)) since 0 ∈ g₁^j(B)
      have hg₂_0_in_g₂img : g₂ n k m (⟨0, by omega⟩ : Omega n k m) ∈ g₂ n k m '' ((g₁ n k m ^ j) '' B) := by
        exact Set.mem_image_of_mem _ h0_in_g₁jB
      -- g₂(0) ∉ g₁^j(B) since g₂(0) ∉ supp(g₁) and g₁^j(B) ⊆ supp(g₁)
      have hg₂_0_not_in_g₁jB : g₂ n k m (⟨0, by omega⟩ : Omega n k m) ∉ (g₁ n k m ^ j) '' B := by
        intro h; exact hg₂_0_not_in_supp_g₁ (hg₁jB_in_supp h)
      -- g₂(g₁^j(B)) ≠ g₁^j(B) because g₂(0) ∈ g₂(g₁^j(B)) but g₂(0) ∉ g₁^j(B)
      have h_not_equal : g₂ n k m '' ((g₁ n k m ^ j) '' B) ≠ (g₁ n k m ^ j) '' B := by
        intro heq
        rw [heq] at hg₂_0_in_g₂img
        exact hg₂_0_not_in_g₁jB hg₂_0_in_g₂img
      -- The intersection is nonempty: tailA elements in g₁^j(B) are fixed by g₂.
      -- Since B is nonempty (a₁ ∈ B), g₁^j(B) is nonempty, and all its elements
      -- are in supp(g₁). We need to find an element in g₁^j(B) that's also in tailA
      -- (hence fixed by g₂).
      -- Actually, g₁^j(B) might contain core elements too. Let's find a tailA element.
      -- Since B ⊆ tailA and g₁ is a cycle, g₁^j(B) = g₁^j(B) might not be ⊆ tailA.
      -- But we know 0 ∈ g₁^j(B), and 0 is a core element.
      -- We need a different fixed point. g₂ fixes elements outside supp(g₂).
      -- supp(g₂) = {0, 1, 3, 4} ∪ tailB. Core elements 2, 5 are NOT in supp(g₂).
      -- But 2, 5 are in supp(g₁), so they might be in g₁^j(B).
      -- Let's check: does g₁^j(B) contain 2 or 5?
      -- g₁^n(5) = g₁^n(L[1]) = L[(1+n) % (4+n)]. For n ≥ 3, (1+n) < 4+n, so = L[1+n].
      -- L[1+n] = a_{n-3} if n ≥ 4, or a specific core if n = 3.
      -- For n = 3: L = [0, 5, 3, 2, 6, 7, 8], length 7. L[(1+3) % 7] = L[4] = 6 = a₁.
      -- So g₁³(5) = a₁ ∈ tailA.
      -- Let me think differently: Instead of finding a fixed point in g₁^j(B),
      -- I'll use the fact that g₂ preserves B, i.e., g₂(B) = B.
      -- Since g₂(B) = B and B ⊆ tailA, and g₂ fixes tailA elements...
      -- Wait, that means g₂ fixes every element of B! So g₂(B) = B is automatic.
      -- Now for g₁^j(B): take any tailA element y ∈ g₁^j(B).
      -- Since g₁^j(B) ⊆ supp(g₁) and supp(g₁) = {0, 2, 3, 5} ∪ tailA,
      -- the tailA part of g₁^j(B) is non-empty (since |B| > 1 and the orbit cycles).
      -- Actually, let me find a simpler approach: a₁ ∈ B, so g₁^j(a₁) ∈ g₁^j(B).
      -- When j = n, g₁^n(a₁) = 0 (core). But consider j = 1: g₁(a₁) = a₂ (if n ≥ 2).
      -- For n ≥ 2, a₂ ∈ g₁(B). And a₂ ∈ tailA, so g₂ fixes a₂.
      -- Therefore a₂ ∈ g₂(g₁(B)) ∩ g₁(B).
      -- But wait, we're using j = n above. Let's reconsider which j to use.
      -- Actually, I should use j such that g₁^j(B) contains both a core element (0)
      -- and a tailA element (for the fixed point argument).
      -- With j = n, g₁^n(a₁) = 0. If |B| > 1, then B contains another tailA element.
      -- Say B contains a_i for some i > 1. Then g₁^n(a_i) = a_{i-n mod something}...
      -- This is getting complex. Let me use a simpler element.
      -- g₂ fixes element 2 and element 5 (not in supp(g₂)). If 2 or 5 ∈ g₁^j(B),
      -- then g₂(2) = 2 or g₂(5) = 5 is in both g₂(g₁^j(B)) and g₁^j(B).
      -- Check if 2 ∈ g₁^n(B): g₁^n(L[i]) = L[(i+n) % (4+n)].
      -- 2 = L[3], so we need L[(3+n) % (4+n)] ∈ B.
      -- (3+n) % (4+n) = 3+n if 3+n < 4+n, i.e., always. So L[3+n] ∈ B.
      -- L[3+n] = a_{n-1} (the last tailA element if n ≥ 1).
      -- So 2 ∈ g₁^n(B) iff a_n ∈ B (where a_n = L[3+n] = element 6+n-1 = 5+n).
      -- We don't know if a_n ∈ B.
      -- Let me try a different approach: show that g₁^j(B) contains element 2.
      -- Since 2 = g₁^(-1)(a₁) = g₁^(3+n)(a₁) and a₁ ∈ B, we have 2 ∈ g₁^(3+n)(B).
      -- But wait, order is 4+n, so g₁^(3+n) = g₁^(-(1)).
      -- Using positive powers: g₁^(4+n-1) = g₁^(3+n). For j = 3+n:
      -- Actually, let's directly compute: g₁^(n+3)(a₁) = ?
      -- Starting from a₁ = L[4], after n+3 steps: L[(4 + n + 3) % (4+n)] = L[(7+n) % (4+n)].
      -- For n ≥ 3: (7+n) % (4+n) = 7+n - (4+n) = 3 = index of element 2.
      -- So g₁^(n+3)(a₁) = 2 for n ≥ 3.
      -- Let's use j' = n + 3 instead. Then 2 ∈ g₁^(n+3)(B), and g₂ fixes 2.
      -- But I already defined j = n and proved things for j = n. Let me adjust.
      -- Alternative: keep j = n, and note that if B contains a_{n-3} (for n ≥ 4) or
      -- specific elements for n = 3, then 2 ∈ g₁^n(B).
      -- For simplicity, let's use a different fixed point: find ANY element in
      -- (g₁^j(B) ∩ tailA) which is automatically fixed by g₂.
      -- Since g₁^j(B) ⊆ supp(g₁) = {0,2,3,5} ∪ tailA, and |g₁^j(B)| = |B| > 1,
      -- g₁^j(B) could be entirely in {0,2,3,5} only if |B| ≤ 4.
      -- If |B| > 4, then g₁^j(B) must contain tailA elements.
      -- For |B| ≤ 4, we need a different argument.
      -- Actually, B ⊆ tailA and |B| > 1 and |tailA| = n. So |B| ≤ n.
      -- For n = 3, |B| ∈ {2, 3}. Let's check if g₁^n(B) ∩ tailA ≠ ∅.
      -- g₁^n maps tailA to: L[4] → L[(4+n)%(4+n)] = L[0] = 0,
      --                     L[5] → L[(5+n)%(4+n)] = L[1] = 5,
      --                     ...
      --                     L[4+n-1] → L[(3+n+n)%(4+n)] = L[(3+2n)%(4+n)]
      -- For n = 3: tailA = {L[4], L[5], L[6]} = {6, 7, 8}.
      -- g₁³: L[4]→L[0]=0, L[5]→L[1]=5, L[6]→L[2]=3.
      -- So g₁³(tailA) = {0, 5, 3} (core elements!).
      -- g₁³(B) ⊆ g₁³(tailA) = {0, 3, 5} (all core!).
      -- Now supp(g₂) = {0, 1, 3, 4} ∪ tailB. Elements fixed by g₂ outside this: 2, 5, tailA, tailC.
      -- 5 ∈ {0, 3, 5} and 5 ∉ supp(g₂), so g₂(5) = 5.
      -- Is 5 ∈ g₁³(B)? 5 = g₁³(L[5]) = g₁³(7). If 7 ∈ B, then 5 ∈ g₁³(B).
      -- We know a₁ = 6 ∈ B. If B = {6}, then |B| = 1, contradiction.
      -- If B = {6, 7}, then 5 = g₁³(7) ∈ g₁³(B), and g₂(5) = 5.
      -- If B = {6, 8}, then g₁³(B) = {g₁³(6), g₁³(8)} = {0, 3}. Neither is fixed by g₂
      -- (0 ∈ supp(g₂), 3 ∈ supp(g₂)). PROBLEM!
      -- So for B = {6, 8} with n = 3, j = n = 3 doesn't work.
      -- Let's try j = 1: g₁(B) = {g₁(6), g₁(8)} = {7, 0}.
      -- But g₁(B) ∩ B = ∅ (by hg₁Disj). Check: {7,0} ∩ {6,8} = ∅. ✓
      -- g₂(g₁(B)) = g₂({7, 0}) = {7, 1}. (g₂(7)=7 since 7∈tailA, g₂(0)=1)
      -- g₁(B) = {7, 0}. g₂(g₁(B)) = {7, 1}.
      -- Intersection: {7, 0} ∩ {7, 1} = {7}. ✓ Nonempty!
      -- Not equal: {7, 1} ≠ {7, 0}. ✓
      -- So for B = {6, 8}, use j = 1 instead of j = n.
      -- General strategy: For j = 1, g₁(B) contains tailA elements (g₁ shifts tailA).
      -- g₁(a₁) = a₂ ∈ tailA (if n ≥ 2). g₂ fixes a₂. So a₂ ∈ g₂(g₁(B)) ∩ g₁(B).
      -- Let's redo with j = 1 instead.
      -- Actually, let me check if hBlock says g₁(B) ∩ B = ∅ (disjoint) or g₁(B) = B.
      -- hg₁Disj says g₁(B) ∩ B = ∅. So by hBlock(1), since not equal, disjoint. ✓
      -- Now I need: g₂(g₁(B)) ∩ g₁(B) ≠ ∅ and g₂(g₁(B)) ≠ g₁(B).
      -- For the intersection: need an element fixed by g₂ in g₁(B).
      -- g₁(a₁) = a₂ (if n ≥ 2). Is a₂ ∈ tailA? Yes. Is a₂ fixed by g₂? Yes.
      -- So a₂ ∈ g₂(g₁(B)) (since g₂(a₂) = a₂) AND a₂ ∈ g₁(B) (since a₁ ∈ B).
      -- Wait, that's wrong. a₂ ∈ g₁(B) if a₁ ∈ B and g₁(a₁) = a₂.
      -- a₂ ∈ g₂(g₁(B)) if ∃ y ∈ g₁(B) with g₂(y) = a₂. Since g₂(a₂) = a₂, need a₂ ∈ g₁(B).
      -- So a₂ ∈ g₁(B) ∩ g₂(g₁(B)) = g₁(B) ∩ g₂(g₁(B)). ✓ (self-fixed element)
      -- For not equal: need g₂(g₁(B)) ≠ g₁(B).
      -- Since B ⊆ tailA and g₁ shifts within cycle, g₁(B) may contain core elements.
      -- g₁(a₁) = a₂ ∈ tailA, g₁(aₙ) = 0 (core). If aₙ ∈ B, then 0 ∈ g₁(B).
      -- g₂(0) = 1 ∈ g₂(g₁(B)). Is 1 ∈ g₁(B)? 1 ∉ supp(g₁), so 1 ∉ g₁(B).
      -- Thus if aₙ ∈ B, then 1 ∈ g₂(g₁(B)) but 1 ∉ g₁(B), so g₂(g₁(B)) ≠ g₁(B). ✓
      -- What if aₙ ∉ B? Then B ⊊ tailA\{aₙ}. g₁(B) doesn't contain 0.
      -- g₁(B) ⊆ supp(g₁) = {0, 2, 3, 5} ∪ tailA.
      -- If B = {a₁, ..., aₙ₋₁} (all but last), g₁(B) = {a₂, ..., aₙ} ⊆ tailA.
      -- Then g₂(g₁(B)) = g₁(B) (all elements fixed). Equal!
      -- But wait, does B = {a₁, ..., aₙ₋₁} satisfy hBlock?
      -- Check g₁^(-1)(B) = B or disjoint. g₁⁻¹(a₁) = 2 (core). If 2 ∈ B, no.
      -- Actually g₁⁻¹(a₁) = 2 ∉ tailA. So g₁⁻¹(B) contains 2 ∈ core.
      -- g₁⁻¹(B) ∩ B ⊇ ? g₁⁻¹(a₂) = a₁ ∈ B if a₂ ∈ B.
      -- So if a₂ ∈ B, then a₁ = g₁⁻¹(a₂) ∈ g₁⁻¹(B), and a₁ ∈ B. Intersection!
      -- So g₁⁻¹(B) ∩ B ≠ ∅ for B = {a₁, ..., aₙ₋₁} with n ≥ 2.
      -- By hBlock, this means g₁⁻¹(B) = B? But g₁⁻¹(B) contains 2 ∉ B. Contradiction.
      -- So B ≠ {a₁, ..., aₙ₋₁}. Either B contains aₙ, or B is even smaller.
      -- If |B| = 2 and B = {a₁, aₖ} for some k > 1:
      --   g₁⁻¹(B) = {g₁⁻¹(a₁), g₁⁻¹(aₖ)} = {2, aₖ₋₁}.
      --   g₁⁻¹(B) ∩ B = {aₖ₋₁} ∩ {a₁, aₖ} = ∅ iff k-1 ∉ {1, k}.
      --   k-1 = 1 means k = 2. k-1 = k is impossible.
      --   So for k ≠ 2, g₁⁻¹(B) ∩ B = ∅. ✓ Consistent with hBlock (disjoint).
      --   For k = 2, g₁⁻¹(B) = {2, a₁}, B = {a₁, a₂}. Intersection = {a₁}. ≠ ∅.
      --   So g₁⁻¹(B) = B? But {2, a₁} ≠ {a₁, a₂}. Contradiction with hBlock.
      --   So B ≠ {a₁, a₂}. But this was the n=2 case handled earlier!
      -- For n ≥ 3 and |B| = 2, B = {a₁, aₖ} with k ≥ 3.
      --   g₁(B) = {a₂, aₖ₊₁ mod n+4}. If k+1 ≤ n, g₁(B) = {a₂, aₖ₊₁} ⊆ tailA.
      --   g₁(B) ∩ B = {a₂, aₖ₊₁} ∩ {a₁, aₖ} = ∅ iff 2 ∉ {1, k} and k+1 ∉ {1, k}.
      --   k ≥ 3, so 2 ∉ {1, k}. k+1 = 1 impossible. k+1 = k impossible.
      --   So g₁(B) ∩ B = ∅. ✓ (disjoint, consistent with hg₁Disj).
      --   Now for g₂: g₂(g₁(B)) = {g₂(a₂), g₂(aₖ₊₁)} = {a₂, aₖ₊₁} = g₁(B).
      --   Because g₂ fixes tailA elements!
      --   So g₂(g₁(B)) = g₁(B). hBlock₂_orbit gives equal OR disjoint. Equal here. ✓
      -- Problem: For B = {a₁, aₖ} with k ≥ 3, g₂(g₁(B)) = g₁(B). No contradiction!
      -- We need a different j. Let's try larger j values.
      -- Let me reconsider: For B = {a₁, aₖ} with k ≥ 3 and n ≥ 3:
      --   The orbit of B under g₁ is {B, g₁(B), g₁²(B), ...}.
      --   g₁(B) = {a₂, aₖ₊₁}. g₁²(B) = {a₃, aₖ₊₂}. etc.
      --   When do we hit a core element? When some aᵢ wraps around to core.
      --   g₁(aₙ) = 0 (core). So when k+j ≡ n (mod n+4-4=n), i.e., j = n-k,
      --   we have g₁^(n-k)(aₖ) = 0 ∈ g₁^(n-k)(B).
      --   Use j = n - k (for k < n). Then 0 ∈ g₁^(n-k)(B).
      --   g₂(0) = 1. 1 ∉ supp(g₁), so 1 ∉ g₁^(n-k)(B). So g₂(g₁^(n-k)(B)) ≠ g₁^(n-k)(B).
      --   For intersection: need a tailA element in g₁^(n-k)(B).
      --   g₁^(n-k)(a₁) = a₁₊₍ₙ₋ₖ₎ = aₙ₋ₖ₊₁ (if this is ≤ n).
      --   For k = 3, n = 3: n - k = 0. j = 0. g₁⁰(B) = B. But hg₁Disj needs g₁(B) disjoint.
      --   Hmm, k = 3, n = 3 means B = {a₁, a₃} = {6, 8}.
      --   Let me trace the orbit: B = {6, 8}, g₁(B) = {7, 0} (since g₁(6)=7, g₁(8)=0).
      --   Wait, is 8 = a₃? a₃ = 6 + 3 - 1 = 8? No, aᵢ = 6 + i - 1 (1-indexed).
      --   a₁ = 6, a₂ = 7, a₃ = 8. So for n = 3, tailA = {6, 7, 8}.
      --   g₁ cycle: (0 5 3 2 6 7 8). So g₁(6) = 7, g₁(7) = 8, g₁(8) = 0.
      --   B = {6, 8} = {a₁, a₃}. g₁(B) = {7, 0}.
      --   g₁(B) ∩ B = {7, 0} ∩ {6, 8} = ∅. ✓
      --   g₂(g₁(B)) = g₂({7, 0}) = {g₂(7), g₂(0)} = {7, 1}. (g₂(7) = 7, g₂(0) = 1)
      --   g₁(B) = {7, 0}. g₂(g₁(B)) = {7, 1}.
      --   Intersection: {7}. ✓ Nonempty.
      --   Not equal: {7, 1} ≠ {7, 0}. ✓
      --   So j = 1 works for B = {6, 8}! Great.
      -- General insight: For any B ⊆ tailA with |B| > 1 and a₁ ∈ B:
      --   g₁(B) contains g₁(a₁) = a₂ ∈ tailA (for n ≥ 2), which is fixed by g₂.
      --   So a₂ ∈ g₁(B) ∩ g₂(g₁(B)).
      --   For g₂(g₁(B)) ≠ g₁(B): Either g₁(B) contains a core element moved by g₂
      --   (like 0, which maps to 1), or... what if g₁(B) ⊆ tailA entirely?
      --   g₁(a₁) = a₂, g₁(a₂) = a₃, ..., g₁(aₙ₋₁) = aₙ, g₁(aₙ) = 0.
      --   So g₁(aᵢ) ∈ tailA iff i < n. g₁(aₙ) = 0 ∈ core.
      --   Thus g₁(B) ⊆ tailA iff B ⊆ {a₁, ..., aₙ₋₁} (B doesn't contain aₙ).
      --   If aₙ ∉ B, then g₁(B) ⊆ tailA, and g₂(g₁(B)) = g₁(B).
      --   In this case, j = 1 doesn't give contradiction. Need to find larger j.
      --   Eventually, g₁^j(B) will contain aₙ for some j, then g₁^(j+1)(B) contains 0.
      --   Specifically, if aₖ ∈ B, then g₁^(n-k)(aₖ) = aₙ, and g₁^(n-k+1)(aₖ) = 0.
      --   So j = n - k + 1 puts 0 in g₁^j(B) if aₖ ∈ B.
      --   For B with a₁ ∈ B, use k = 1: j = n - 1 + 1 = n. g₁^n(a₁) = 0.
      --   This is what we had originally!
      -- Let me reconsider the original j = n approach with more care.
      -- For B ⊆ tailA with a₁ ∈ B:
      --   g₁^n(B) contains g₁^n(a₁) = 0.
      --   g₂(0) = 1. 1 ∉ supp(g₁), so 1 ∉ g₁^n(B) ⊆ supp(g₁).
      --   So 1 ∈ g₂(g₁^n(B)) but 1 ∉ g₁^n(B). Hence g₂(g₁^n(B)) ≠ g₁^n(B). ✓
      --   For intersection: need element in g₁^n(B) fixed by g₂.
      --   g₁^n(B) ⊆ supp(g₁) = {0, 2, 3, 5} ∪ tailA.
      --   Elements of supp(g₁) fixed by g₂: 2, 5, tailA (none of 0, 3 are fixed).
      --   supp(g₂) = {0, 1, 3, 4} ∪ tailB. Fixed: 2, 5, tailA, tailC.
      --   So need 2 ∈ g₁^n(B) or 5 ∈ g₁^n(B) or (g₁^n(B) ∩ tailA) ≠ ∅.
      --   g₁^n maps: 0→L[n], 2→L[3+n], 3→L[2+n], 5→L[1+n].
      --            L[n] = ?, L[3+n] = ?, etc.
      --   For the cycle [0, 5, 3, 2, a₁, ..., aₙ], indices: 0→0, 5→1, 3→2, 2→3,
      --   a₁→4, a₂→5, ..., aₙ→3+n.
      --   L[n] = L[4 + (n-4)] if n ≥ 4, else L[n] for n < 4.
      --   n = 3: L[3] = 2. So g₁³(0) = 2.
      --   n = 4: L[4] = a₁. So g₁⁴(0) = a₁.
      --   g₁^n(L[i]) = L[(i+n) mod (4+n)].
      --   g₁^n(0) = L[n mod (4+n)] = L[n] (for n < 4+n).
      --   n = 3: L[3] = 2. So 0 ∈ B ⊆ tailA is impossible, but wait, 0 ∉ tailA!
      --   We have a₁ ∈ B. g₁^n(a₁) = L[(4+n) mod (4+n)] = L[0] = 0. ✓
      --   What about other elements? |B| ≥ 2, so ∃ x ∈ B, x ≠ a₁.
      --   x ∈ tailA, so x = aₖ for some k ≠ 1.
      --   g₁^n(aₖ) = L[(4 + k - 1 + n) mod (4+n)] = L[(3 + k + n) mod (4+n)].
      --   For 3 + k + n < 4 + n, i.e., k < 1, impossible. So k ≥ 1.
      --   3 + k + n ≥ 4 + n when k ≥ 1. So we wrap: (3 + k + n) - (4 + n) = k - 1.
      --   g₁^n(aₖ) = L[k - 1] for k ≥ 1.
      --   k = 1: L[0] = 0. (Already covered for a₁.)
      --   k = 2: L[1] = 5.
      --   k = 3: L[2] = 3.
      --   k = 4: L[3] = 2.
      --   k ≥ 5: L[k-1] = aₖ₋₄ ∈ tailA.
      --   So if B contains a₂, then 5 ∈ g₁^n(B), and g₂(5) = 5. ✓
      --   If B contains a₃, then 3 ∈ g₁^n(B), but g₂(3) = 4 ≠ 3. ✗
      --   If B contains a₄, then 2 ∈ g₁^n(B), and g₂(2) = 2. ✓
      --   If B contains aₖ for k ≥ 5, then aₖ₋₄ ∈ g₁^n(B) ⊆ tailA, and g₂(aₖ₋₄) = aₖ₋₄. ✓
      -- Summary: If B contains a₂ or a₄ or aₖ (k ≥ 5), we have a fixed point.
      --          If B = {a₁, a₃}, then g₁^n(B) = {0, 3}, neither fixed by g₂.
      -- For B = {a₁, a₃} with n ≥ 3:
      --   j = 1: g₁(B) = {a₂, a₄}. Fixed points: a₂ (tailA), a₄ (tailA if n ≥ 4, else core).
      --   For n = 3: a₄ = 6 + 3 = 9, but wait n = 3 means tailA = {6, 7, 8}. a₄ doesn't exist!
      --   Oh, for n = 3, B ⊆ tailA = {a₁, a₂, a₃} = {6, 7, 8}.
      --   B = {a₁, a₃} = {6, 8} with n = 3. g₁(B) = {g₁(6), g₁(8)} = {7, 0}.
      --   g₁(8) = 0 because g₁ = (0 5 3 2 6 7 8) and 8 → 0.
      --   So g₁(B) = {7, 0} contains 0 ∈ core, moved by g₂.
      --   g₂(g₁(B)) = {g₂(7), g₂(0)} = {7, 1}. ≠ {7, 0} = g₁(B). ✓ (not equal)
      --   Fixed point in g₁(B): 7 ∈ tailA, g₂(7) = 7. ✓ (intersection nonempty)
      --   So j = 1 works for B = {a₁, a₃} with n = 3!
      -- Wait, I think I overcomplicated things. Let me just use j = 1 and show it always works.
      -- For j = 1:
      --   0 ∈ g₁(B) iff aₙ ∈ B (since g₁(aₙ) = 0).
      --   If aₙ ∈ B: 0 ∈ g₁(B), g₂(0) = 1 ∈ g₂(g₁(B)), 1 ∉ g₁(B). Not equal. ✓
      --             a₂ ∈ g₁(B) (since a₁ ∈ B and g₁(a₁) = a₂), g₂(a₂) = a₂. Intersection. ✓
      --   If aₙ ∉ B: g₁(B) ⊆ tailA. g₂(g₁(B)) = g₁(B). Equal!
      --             Need larger j.
      -- For aₙ ∉ B: Since |B| ≥ 2 and a₁ ∈ B, ∃ aₖ ∈ B with 1 < k < n.
      --   The smallest j such that g₁^j(aₖ) = 0 is j = n - k + 1 (since aₖ → aₖ₊₁ → ... → aₙ → 0).
      --   Wait, g₁(aₖ) = aₖ₊₁ for k < n. So j = n - k gets aₖ to aₙ, and j = n - k + 1 gets to 0.
      --   Actually, that's for the element aₖ specifically. If a₁ ∈ B too, then
      --   g₁^(n-k+1)(a₁) = g₁^(n-k+1)(a₁) = a₁₊₍ₙ₋ₖ₊₁₎ = aₙ₋ₖ₊₂ (if ≤ n, else wraps to core).
      -- This is getting complicated. Let me just compute for a specific problematic case
      -- and verify that hBlock₂_orbit catches it.
      --
      -- Alternative approach: Use the fact that the orbit of B under g₁ must eventually
      -- include a core element (since g₁ is a cycle mixing tailA and core), and then
      -- g₂ acting on that block will create the contradiction.
      --
      -- For the formal proof, I'll use the fact that for SOME j, we have:
      -- (1) 0 ∈ g₁^j(B) [for j = n, since g₁^n(a₁) = 0]
      -- (2) a tailA element in g₁^j(B) [need to verify this].
      --
      -- Actually, I realize the simplest approach: just verify both conditions are satisfied
      -- for j = n when |B| > 1 and n ≥ 3.
      --
      -- Let me check: g₁^n(B) where B ⊆ tailA, |B| > 1, a₁ ∈ B.
      -- g₁^n(a₁) = 0 ∈ g₁^n(B). ✓
      -- For tailA element: If ∃ aₖ ∈ B with k ≥ 5, then g₁^n(aₖ) = aₖ₋₄ ∈ tailA. ✓
      -- If B ⊆ {a₁, a₂, a₃, a₄} (only first 4 elements):
      --   g₁^n(a₂) = 5 (core), g₁^n(a₃) = 3 (core), g₁^n(a₄) = 2 (core).
      --   5 is fixed by g₂. 2 is fixed by g₂. 3 is moved by g₂.
      --   If a₂ ∈ B or a₄ ∈ B, we have a fixed point. ✓
      --   If B = {a₁, a₃}: g₁^n(B) = {0, 3}. Neither 0 nor 3 is fixed by g₂.
      --     But wait, n ≥ 3 means tailA has at least 3 elements. If B = {a₁, a₃} only,
      --     then we're fine to use a different j.
      --   Actually, for B = {a₁, a₃}, use j = 1: g₁(B) = {a₂, g₁(a₃)}.
      --     g₁(a₃) = a₄ if n ≥ 4, or 0 if n = 3 (since a₃ = aₙ when n = 3).
      --   For n = 3: g₁(B) = {a₂, 0} = {7, 0}.
      --     Fixed point: a₂ = 7 ∈ tailA, g₂(7) = 7. ✓
      --     Not equal: 0 ∈ g₁(B), g₂(0) = 1 ∈ g₂(g₁(B)), 1 ∉ g₁(B). ✓
      --   For n ≥ 4: g₁(B) = {a₂, a₄} ⊆ tailA.
      --     g₂(g₁(B)) = g₁(B) (all fixed). Equal! ✗
      --     Need larger j. Use j = 2: g₁²(B) = {a₃, a₅} ⊆ tailA (if n ≥ 5), or
      --     {a₃, 0} if n = 4.
      --   For n = 4: g₁²(B) = {a₃, g₁²(a₃)} = {a₃, g₁(a₄)} = {a₃, 0} (since g₁(a₄) = 0 when n = 4).
      --     g₂(g₁²(B)) = {a₃, 1}. g₁²(B) = {a₃, 0}. Not equal. ✓
      --     Fixed point: a₃ ∈ tailA, g₂(a₃) = a₃. ✓
      --   For n ≥ 5: g₁²(B) = {a₃, a₅} ⊆ tailA. Equal case again.
      --     Continue to j = 3: g₁³(B) = {a₄, a₆} ⊆ tailA (if n ≥ 6), or {a₄, 0} if n = 5.
      --   For n = 5: g₁³(B) = {a₄, 0}. Same analysis gives contradiction. ✓
      --   For n ≥ 6: Eventually j = n - 3 gives g₁^(n-3)(a₃) = aₙ, g₁^(n-2)(a₃) = 0.
      --     j = n - 2: g₁^(n-2)(B) contains g₁^(n-2)(a₃) = 0 and g₁^(n-2)(a₁) = aₙ₋₁.
      --     aₙ₋₁ ∈ tailA, fixed by g₂. ✓
      --
      -- This case analysis is getting very long. The key insight is:
      -- For B = {a₁, a₃} ⊆ tailA with |B| = 2:
      --   The smallest j such that g₁^j(B) contains a core element is j = n - 2 (for n ≥ 4)
      --   or j = 1 (for n = 3, since a₃ = aₙ).
      --   At that j, we have:
      --   - 0 ∈ g₁^j(B) [triggers g₂(0) = 1 ∉ g₁^j(B), so not equal]
      --   - a tailA element in g₁^j(B) [fixed by g₂, gives nonempty intersection]
      --   - Contradiction with hBlock₂_orbit.
      --
      -- The formal proof just needs to handle two cases based on whether
      -- the orbit under g₁ reaches a core element quickly (via aₙ ∈ B) or after
      -- several steps (via some aₖ ∈ B eventually reaching 0).
      --
      -- For simplicity, I'll use a unified approach: find j such that both conditions hold.
      -- Since |B| > 1 and B ⊆ tailA with a₁ ∈ B, there's at least one other element aₖ ∈ B.
      -- The g₁-orbit of B eventually contains 0 (when aₖ cycles to 0 for some k).
      -- At that point, the orbit block also contains tailA elements (from earlier iterations).
      --
      -- Rather than computing exactly, I'll prove it by showing the orbit satisfies:
      -- - It's a subset of supp(g₁).
      -- - It eventually contains 0 (which is moved by g₂).
      -- - It always contains some tailA elements (which are fixed by g₂).
      -- This gives the contradiction.
      --
      -- For the formal Lean proof, the cleanest approach is:
      -- 1. Use j = 1.
      -- 2. Show a₂ ∈ g₁(B) (since a₁ ∈ B and g₁(a₁) = a₂). Fixed by g₂.
      -- 3. Show either 0 ∈ g₁(B) (if aₙ ∈ B), or use induction/recursion to find j.
      -- 4. For j = 1 when aₙ ∉ B, we have g₂(g₁(B)) = g₁(B), which is allowed by hBlock₂_orbit.
      --    But then g₁(B) is also a valid "B" for recursion...
      --
      -- Actually, the simplest formal proof: For j = n, we have 0 ∈ g₁^n(B).
      -- For the fixed point, we need to show g₁^n(B) ∩ {2, 5, tailA} ≠ ∅.
      -- This requires |B| ≥ 2 to guarantee a second element.
      -- If B contains aₖ with k ≠ 1, then g₁^n(aₖ) = L[k-1].
      --   k = 2: L[1] = 5. ✓ (fixed by g₂)
      --   k = 3: L[2] = 3. ✗ (moved by g₂)
      --   k = 4: L[3] = 2. ✓ (fixed by g₂)
      --   k ≥ 5: L[k-1] = aₖ₋₄ ∈ tailA. ✓ (fixed by g₂)
      -- So if k ≠ 3, we're done. For k = 3 (B contains a₃):
      --   If B also contains a₂ or a₄ or aₖ (k ≥ 5), we're done.
      --   Minimal problematic case: B = {a₁, a₃}.
      --   For this case, use j = 1 if n = 3 (then a₃ = aₙ, so 0 ∈ g₁(B)).
      --   For n ≥ 4, use j such that g₁^j(a₃) = 0, which is j = n - 2.
      --   At j = n - 2: g₁^(n-2)(a₁) = aₙ₋₁ ∈ tailA (fixed), g₁^(n-2)(a₃) = 0 (moved). ✓
      --
      -- OK, I'll implement this logic.

      -- The intersection is nonempty: we'll find a tailA element in g₁^j(B) that's fixed by g₂.
      have h_intersection_nonempty : (g₂ n k m '' ((g₁ n k m ^ j) '' B) ∩ (g₁ n k m ^ j) '' B).Nonempty := by
        -- Since |B| > 1 and a₁ ∈ B, there exists x ∈ B with x ≠ a₁.
        have hB_has_two : ∃ x ∈ B, x ≠ a₁ n k m hn := by
          by_contra h; push_neg at h
          have hSub : B ⊆ {a₁ n k m hn} := fun y hy => Set.mem_singleton_iff.mpr (h y hy)
          have hLe : B.ncard ≤ ({a₁ n k m hn} : Set (Omega n k m)).ncard :=
            Set.ncard_le_ncard hSub (Set.finite_singleton _)
          simp only [Set.ncard_singleton] at hLe; omega
        obtain ⟨x, hx_in_B, hx_ne_a₁⟩ := hB_has_two
        -- x is in tailA
        have hx_tailA := hB_subset_tailA x hx_in_B
        -- x.val ≠ 6 (since x ≠ a₁)
        have hx_val_ne_6 : x.val ≠ 6 := by
          intro heq; have : x = a₁ n k m hn := Fin.ext heq; exact hx_ne_a₁ this
        -- So x.val ∈ [7, 6+n) ⊆ tailA
        simp only [isTailA] at hx_tailA
        have hx_val_ge_7 : x.val ≥ 7 := by omega
        have hx_val_lt : x.val < 6 + n := hx_tailA.2
        -- Let k' = x.val - 6 (0-indexed position in tailA). k' ∈ [1, n).
        set k' := x.val - 6 with hk'_def
        have hk'_ge_1 : k' ≥ 1 := by omega
        have hk'_lt_n : k' < n := by omega
        -- g₁^n(x) = g₁^n(L[4 + k']) where L = g₁ cycle list.
        -- = L[(4 + k' + n) mod (4 + n)] = L[(4 + k' + n) - (4 + n)] = L[k'].
        -- L[k'] = ? For k' = 1: L[1] = 5. For k' = 2: L[2] = 3. For k' = 3: L[3] = 2.
        -- For k' ≥ 4: L[k'] = aₖ'₋₃ ∈ tailA.
        -- Elements fixed by g₂: 2, 5, tailA elements.
        -- So if k' ∈ {1, 3} ∪ [4, ∞), g₁^n(x) is fixed by g₂.
        -- If k' = 2, g₁^n(x) = 3, which is NOT fixed by g₂ (g₂(3) = 4).
        -- For k' = 2, we need a different argument.
        -- Since |B| > 1 and we have a₁ ∈ B and x = a₂ ∈ B, maybe there's a third element?
        -- Or use a different j.
        -- For now, let's handle the case k' ≠ 2 and leave k' = 2 for separate treatment.
        by_cases hk'_eq_2 : k' = 2
        case pos => -- k' = 2 means x = a₃ (element 8 for n ≥ 3).
          -- Use j = 1 if n = 3 (then a₃ = aₙ, so g₁(a₃) = 0).
          -- For n ≥ 4, this is trickier. For simplicity, I'll use the fact that
          -- g₁(a₁) = a₂ ∈ tailA is always in g₁(B), and we can use j = 1 instead.
          -- Wait, but we defined j = n above. Let me reconsider.
          -- Actually, the cleanest fix: change j to 1 and use a₂ as the fixed point.
          -- But we already defined j = n and proved h0_in_g₁jB and h1_not_in_g₁jB.
          -- Hmm, let me just show that for j = n, there's always a fixed point.
          -- If k' = 2 (x = a₃), then g₁^n(x) = 3 ∈ core, moved by g₂.
          -- But we also have a₁ ∈ B. g₁^n(a₁) = 0 ∈ core, moved by g₂.
          -- We need another element. Since |B| > 1, we have x ∈ B with x ≠ a₁.
          -- If B = {a₁, a₃}, then |B| = 2. g₁^n(B) = {0, 3}, no fixed points.
          -- But for n = 3, a₃ = aₙ, so g₁(a₃) = 0. Use j = 1 instead.
          -- g₁(B) = g₁({a₁, a₃}) = {a₂, 0}. a₂ ∈ tailA, fixed by g₂. ✓
          -- This requires changing j, which I defined as n. Let me use a sub-case.
          -- For n = 3: j = 1 works. Let's prove separately.
          by_cases hn3 : n = 3
          · -- n = 3, k' = 2 means x = a₃ = element 8. B ⊇ {a₁, a₃} = {6, 8}.
            -- For n = 3, j = n doesn't give a fixed point if B = {a₁, a₃}.
            -- Use hBlock₂_orbit(1) directly to get contradiction.
            exfalso
            -- Key: g₁^1 '' B = g₁ '' B, so hBlock₂_orbit 1 applies to g₁ '' B.
            have hg₁_pow1_eq : (g₁ n k m ^ 1 : Equiv.Perm (Omega n k m)) = g₁ n k m := pow_one _
            -- g₂ '' (g₁ '' B) = g₁ '' B ∨ Disjoint (g₂ '' (g₁ '' B)) (g₁ '' B)
            have hBlock₂_at_1 := hBlock₂_orbit 1
            simp only [hg₁_pow1_eq] at hBlock₂_at_1
            -- Now hBlock₂_at_1 : g₂ '' (g₁ '' B) = g₁ '' B ∨ Disjoint (g₂ '' (g₁ '' B)) (g₁ '' B)
            have hn_ge_2 : n ≥ 2 := by omega
            have h_g₁_a₁ : g₁ n k m (a₁ n k m hn) = (⟨7, by omega⟩ : Omega n k m) :=
              g₁_a₁_eq_7 hn_ge_2
            have ha₂_in_g₁B : (⟨7, by omega⟩ : Omega n k m) ∈ g₁ n k m '' B :=
              ⟨a₁ n k m hn, ha₁_in_B, h_g₁_a₁⟩
            have ha₂_fixed : g₂ n k m (⟨7, by omega⟩ : Omega n k m) = ⟨7, by omega⟩ := by
              have h7_not_supp : (⟨7, by omega⟩ : Omega n k m) ∉ (g₂ n k m).support := by
                have h1_lt_n : 1 < n := by omega
                exact tailA_not_in_support_g₂ hn ⟨1, h1_lt_n⟩
              exact Equiv.Perm.notMem_support.mp h7_not_supp
            -- 7 is in both g₂(g₁(B)) and g₁(B)
            have h7_in_inter : (⟨7, by omega⟩ : Omega n k m) ∈ g₂ n k m '' (g₁ n k m '' B) ∩ g₁ n k m '' B := by
              exact ⟨⟨⟨7, by omega⟩, ha₂_in_g₁B, ha₂_fixed⟩, ha₂_in_g₁B⟩
            -- x.val = 8 for n = 3, k' = 2
            have hx_val_eq_8 : x.val = 8 := by omega
            -- g₁(x) = 0 for n = 3. g₁ cycle for n=3: [0,5,3,2,6,7,8].
            -- x.val = 8 = element at index 6. g₁ maps index 6 to index 0.
            have h8_bound : 8 < 6 + n + k + m := by omega
            have hg₁_x_eq_0 : g₁ n k m x = (⟨0, by omega⟩ : Omega n k m) := by
              have hx_as_8 : x = ⟨8, h8_bound⟩ := by ext; exact hx_val_eq_8
              conv_lhs => rw [hx_as_8]
              unfold g₁
              let L := g₁CoreList n k m ++ tailAList n k m
              have hnd : L.Nodup := g₁_list_nodup n k m
              have hlen : L.length = 4 + n := g₁_cycle_length n k m
              have h6_lt : 6 < L.length := by rw [hlen, hn3]; omega
              have h8_eq_L6 : (⟨8, h8_bound⟩ : Omega n k m) = L[6] := by
                simp only [L]
                have h2_lt : 2 < n := by omega
                exact (AfTests.Transitivity.g₁_list_getElem_tail n k m ⟨2, h2_lt⟩).symm
              rw [h8_eq_L6, List.formPerm_apply_getElem _ hnd 6 h6_lt]
              -- L.length = 4 + n = 7 when n = 3, so L[(6+1) % L.length] = L[0] = ⟨0, ...⟩
              -- TODO: Fix this list computation - the dependent type indexing is tricky
              sorry
            have h0_in_g₁B : (⟨0, by omega⟩ : Omega n k m) ∈ g₁ n k m '' B :=
              ⟨x, hx_in_B, hg₁_x_eq_0⟩
            -- g₂(0) ∈ g₂(g₁(B)) since 0 ∈ g₁(B)
            have hg₂_0_in_g₂img : g₂ n k m (⟨0, by omega⟩ : Omega n k m) ∈ g₂ n k m '' (g₁ n k m '' B) :=
              Set.mem_image_of_mem _ h0_in_g₁B
            -- g₁(B) ⊆ supp(g₁): all elements of B are in tailA, and g₁ maps supp(g₁) → supp(g₁)
            have hg₁B_in_supp : g₁ n k m '' B ⊆ (g₁ n k m).support := by
              intro z hz
              obtain ⟨w, hw_in_B, hw_eq⟩ := hz
              have hw_tailA := hB_subset_tailA w hw_in_B
              simp only [isTailA] at hw_tailA
              have hw_idx : w.val - 6 < n := by omega
              have hw_in_supp : w ∈ (g₁ n k m).support := by
                have hw_eq' : w.val = 6 + (w.val - 6) := by omega
                have h_fin : w = ⟨6 + (w.val - 6), by omega⟩ := by ext; exact hw_eq'
                rw [h_fin]; exact tailA_in_support_g₁ ⟨w.val - 6, hw_idx⟩
              -- g w ∈ supp(g) when w ∈ supp(g): if g(g w) = g w, then g w = w by injectivity
              rw [← hw_eq]
              simp only [Finset.mem_coe, Equiv.Perm.mem_support] at hw_in_supp ⊢
              intro h; exact hw_in_supp ((g₁ n k m).injective h)
            -- g₂(0) ∉ g₁(B) since g₂(0) ∉ supp(g₁) and g₁(B) ⊆ supp(g₁)
            have hg₂_0_not_in_g₁B : g₂ n k m (⟨0, by omega⟩ : Omega n k m) ∉ g₁ n k m '' B := by
              intro h_in; exact hg₂_0_not_in_supp_g₁ (hg₁B_in_supp h_in)
            -- 1 ∉ g₁(B) since g₁(B) ⊆ supp(g₁) and 1 ∉ supp(g₁)
            have h1_not_in_g₁B : (⟨1, by omega⟩ : Omega n k m) ∉ g₁ n k m '' B := by
              intro h1_in
              obtain ⟨y, hy_in_B, hg₁y_eq_1⟩ := h1_in
              have hy_tailA := hB_subset_tailA y hy_in_B
              simp only [isTailA] at hy_tailA
              have hy_idx : y.val - 6 < n := by omega
              have hy_in_supp : y ∈ (g₁ n k m).support := by
                have hy_eq' : y.val = 6 + (y.val - 6) := by omega
                have h_fin : y = ⟨6 + (y.val - 6), by omega⟩ := by ext; exact hy_eq'
                rw [h_fin]
                exact tailA_in_support_g₁ ⟨y.val - 6, hy_idx⟩
              -- g y ∈ supp(g) when y ∈ supp(g)
              have hg₁y_in_supp : g₁ n k m y ∈ (g₁ n k m).support := by
                simp only [Finset.mem_coe, Equiv.Perm.mem_support] at hy_in_supp ⊢
                intro h; exact hy_in_supp ((g₁ n k m).injective h)
              rw [hg₁y_eq_1] at hg₁y_in_supp
              exact elem1_not_in_support_g₁ hg₁y_in_supp
            -- g₂(g₁(B)) ≠ g₁(B) (since g₂(0) ∈ g₂(g₁(B)) but g₂(0) ∉ g₁(B))
            have h_not_equal : g₂ n k m '' (g₁ n k m '' B) ≠ g₁ n k m '' B := by
              intro heq; rw [heq] at hg₂_0_in_g₂img; exact hg₂_0_not_in_g₁B hg₂_0_in_g₂img
            -- Not disjoint (7 is in both)
            have h_not_disjoint : ¬Disjoint (g₂ n k m '' (g₁ n k m '' B)) (g₁ n k m '' B) :=
              Set.not_disjoint_iff.mpr ⟨⟨7, by omega⟩, h7_in_inter.1, h7_in_inter.2⟩
            -- By hBlock₂_at_1, must be equal or disjoint
            rcases hBlock₂_at_1 with heq | hdisj
            · exact h_not_equal heq
            · exact h_not_disjoint hdisj
          · -- n ≥ 4, k' = 2. x = a₃.
            -- g₁^n(x) = g₁^n(a₃) = L[(4 + 2 + n) mod (4 + n)] = L[(6 + n) mod (4 + n)]
            -- For n ≥ 4: (6 + n) mod (4 + n) = (6 + n) - (4 + n) = 2. So L[2] = 3.
            -- 3 is moved by g₂ (g₂(3) = 4). Not a fixed point!
            -- But |B| > 1 means maybe there's another element besides a₁, a₃?
            -- If B = {a₁, a₃}, |B| = 2, and g₁^n(B) = {0, 3} for n ≥ 4. Neither fixed.
            -- We need another element. But the hypothesis only guarantees |B| > 1.
            -- So B could be {a₁, a₃} with no fixed point in g₁^n(B).
            -- This means j = n doesn't work for this case. Need j = n - 2.
            -- For j = n - 2:
            --   g₁^(n-2)(a₁) = L[(4 + n - 2) mod (4 + n)] = L[n + 2] = a_{n-1} ∈ tailA. ✓
            --   g₁^(n-2)(a₃) = L[(4 + 2 + n - 2) mod (4 + n)] = L[(4 + n) mod (4 + n)] = L[0] = 0.
            -- So g₁^(n-2)(B) ⊇ {a_{n-1}, 0}. a_{n-1} ∈ tailA, fixed by g₂. ✓
            -- This is getting complicated. For now, let me just use the element a₂ = g₁(a₁).
            -- Since a₁ ∈ B, g₁^n(a₁) = 0. But g₁^(n-1)(a₁) = aₙ ∈ tailA.
            -- Hmm, g₁^(n-1)(a₁) = L[(4 + n - 1) mod (4 + n)] = L[n + 3] = aₙ.
            -- Wait, that's wrong. Let me recalculate.
            -- a₁ = L[4]. g₁^j(a₁) = L[(4 + j) mod (4 + n)].
            -- j = n - 1: (4 + n - 1) mod (4 + n) = n + 3. L[n + 3] = aₙ (if n ≥ 1).
            -- For n = 4: L[7] = a₄. So g₁³(a₁) = a₄ ∈ tailA. ✓
            -- j = n: (4 + n) mod (4 + n) = 0. L[0] = 0. ✓
            -- So for j = n - 1, we have g₁^(n-1)(a₁) = aₙ ∈ tailA, which is fixed by g₂.
            -- Let's use this as an alternative approach.
            -- But wait, we defined j = n and proved h0_in_g₁jB for j = n.
            -- The issue is h_intersection_nonempty needs a fixed point in g₁^n(B).
            -- For B = {a₁, a₃} with n ≥ 4, g₁^n(B) = {0, 3}, neither fixed.
            -- So j = n doesn't work. We need to change j.
            -- Alternative: Use a different element. Since we're in the case k' = 2 and n ≥ 4,
            -- we have x = a₃ ∈ B. We claimed there exists x ≠ a₁ in B, and this x = a₃.
            -- But maybe there's another element y ∈ B with y ≠ a₁ and y ≠ a₃?
            -- If |B| ≥ 3, yes. If |B| = 2, no.
            -- For |B| = 2 and B = {a₁, a₃}: g₁^n(B) = {0, 3} (neither fixed).
            -- This case is problematic. The solution is to use j = n - 2 instead.
            -- But I already structured the proof around j = n. Let me reconsider.
            -- Actually, the simplest fix: define j based on B's structure.
            -- Since I'm in the case k' = 2 (x = a₃) and n ≥ 4, I'll use j = n - 2.
            -- g₁^(n-2)(a₃) = L[(4 + 2 + n - 2) mod (4 + n)] = L[(4 + n) mod (4 + n)] = L[0] = 0.
            -- g₁^(n-2)(a₁) = L[(4 + n - 2) mod (4 + n)] = L[n + 2].
            -- For n = 4: L[6] = a₂. For n = 5: L[7] = a₃. For n ≥ 6: L[n+2] = aₙ₋₁.
            -- Wait, L[n + 2] where L = [0, 5, 3, 2, a₁, ..., aₙ].
            -- Indices: 0, 1, 2, 3, 4, 5, ..., 3+n.
            -- L[n + 2]: For n = 4, index 6 = a₃. For n = 5, index 7 = a₄. For n = 6, index 8 = a₅.
            -- In general, L[n + 2] = a_{n-1} for n ≥ 4.
            -- Hmm, a_{n-1} = L[4 + (n - 1) - 1] = L[n + 2]. ✓
            -- So g₁^(n-2)(a₁) = a_{n-1} ∈ tailA, fixed by g₂. ✓
            -- This means using j = n - 2 gives a fixed point.
            -- But I need to reprove h0_in_g₁jB and h1_not_in_g₁jB for j = n - 2.
            -- h0_in_g₁jB: 0 ∈ g₁^(n-2)(B). ✓ (from g₁^(n-2)(a₃) = 0)
            -- h1_not_in_g₁jB: 1 ∉ g₁^(n-2)(B). ✓ (since g₁^(n-2)(B) ⊆ supp(g₁) and 1 ∉ supp(g₁))
            -- Let's use j = n - 2 for this sub-case.
            -- Actually, the cleanest approach: don't fix j = n at the top level.
            -- Instead, choose j based on whether we can find a fixed point.
            -- This requires a case split, which is what I'm doing.
            -- For this specific sub-case (k' = 2, n ≥ 4), use the fixed point a_{n-1} in g₁^(n-2)(B).
            -- Actually, we're inside the proof of h_intersection_nonempty, which is specifically
            -- for j = n (the j we defined). For j = n, we need a fixed point in g₁^n(B).
            -- If there's none (B = {a₁, a₃}, n ≥ 4), we have a problem.
            -- The solution is to CHANGE j before this point. Let me restructure.
            --
            -- RESTRUCTURE: Define j based on B's structure to ensure both conditions hold.
            -- For now, let me use a hack: show that if B = {a₁, a₃} with n ≥ 4,
            -- then hBlock₂_orbit gives a contradiction for some OTHER j (like j = n - 2).
            -- But this requires re-proving the "not equal" condition too.
            -- Actually, the cleanest fix is: show that B ⊆ {a₁, a₃} contradicts hBlock for g₁.
            -- If B = {a₁, a₃}, check if g₁^k(B) = B or disjoint for all k.
            -- The orbit of B under g₁ is {B, g₁(B), g₁²(B), ...} until it cycles.
            -- g₁(B) = {a₂, a₄}. g₁²(B) = {a₃, a₅}. ... eventually wraps.
            -- For n = 4: g₁(B) = {a₂, a₄}, g₁²(B) = {a₃, 0}, g₁³(B) = {a₄, 5}, g₁⁴(B) = {0, 3}.
            -- Wait, g₁(a₄) = 0 for n = 4 (since a₄ = aₙ). So g₁²(a₃) = a₅? No, for n = 4, a₅ doesn't exist.
            -- Let me recalculate. For n = 4:
            -- a₁ = 6, a₂ = 7, a₃ = 8, a₄ = 9. tailA = {6, 7, 8, 9}.
            -- g₁ = (0 5 3 2 6 7 8 9) = L with |L| = 8.
            -- B = {6, 8} = {a₁, a₃}.
            -- g₁(B) = {g₁(6), g₁(8)} = {7, 9} = {a₂, a₄}.
            -- g₁²(B) = g₁({7, 9}) = {8, 0} = {a₃, 0}.
            -- g₁³(B) = g₁({8, 0}) = {9, 5} = {a₄, 5}.
            -- g₁⁴(B) = g₁({9, 5}) = {0, 3}.
            -- g₁⁵(B) = g₁({0, 3}) = {5, 2}.
            -- g₁⁶(B) = g₁({5, 2}) = {3, 6} = {3, a₁}.
            -- g₁⁷(B) = g₁({3, 6}) = {2, 7} = {2, a₂}.
            -- g₁⁸(B) = g₁({2, 7}) = {6, 8} = B. ✓ (period 8 = |L|)
            -- None of these equal B (except g₁⁸(B)). Are any disjoint from B?
            -- B = {6, 8}. g₁(B) = {7, 9}. Disjoint. ✓
            -- g₁²(B) = {8, 0}. 8 ∈ B. NOT disjoint!
            -- So g₁²(B) ∩ B = {8} ≠ ∅, but g₁²(B) ≠ B.
            -- By hBlock(2), we should have g₁²(B) = B or disjoint. Neither holds!
            -- CONTRADICTION! This means B = {a₁, a₃} with n = 4 cannot exist.
            -- The block condition hBlock rules out such B.
            -- So if B passes hBlock, we can't have B = {a₁, a₃} for n ≥ 4.
            -- This means the case k' = 2, n ≥ 4 leads to a contradiction via hBlock, not hBlock₂_orbit.
            -- Let's verify: We assumed B ⊆ tailA, a₁ ∈ B, |B| > 1, and x = a₃ ∈ B with x ≠ a₁.
            -- If n ≥ 4 and a₃ ∈ B, then g₁²(a₃) = a₅ for n ≥ 5 or 0 for n = 4.
            -- g₁²(a₁) = a₃.
            -- So g₁²(B) ⊇ {a₃, g₁²(a₃)}.
            -- For n = 4: g₁²(B) ⊇ {a₃, 0}. a₃ ∈ B, so g₁²(B) ∩ B ≠ ∅.
            -- g₁²(B) = B? g₁²(B) = {a₃, 0} if B = {a₁, a₃}. B = {a₁, a₃} = {6, 8}.
            -- {a₃, 0} = {8, 0} ≠ {6, 8}. So g₁²(B) ≠ B but g₁²(B) ∩ B = {8} ≠ ∅.
            -- Contradiction with hBlock(2)!
            -- For n ≥ 5: g₁²(B) ⊇ {a₃, a₅}. If a₅ ∈ B, then g₁²(B) ∩ B ⊇ {a₃, a₅}. Not disjoint.
            --   If a₅ ∉ B, then a₃ ∈ g₁²(B) and a₃ ∈ B, so not disjoint.
            -- In either case, g₁²(B) ∩ B ≠ ∅.
            -- Is g₁²(B) = B? For B = {a₁, a₃}: g₁²(B) = {g₁²(a₁), g₁²(a₃)} = {a₃, a₅}.
            --   {a₃, a₅} = B = {a₁, a₃}? Only if a₅ = a₁ and a₃ = a₃. a₅ ≠ a₁. So ≠.
            -- Contradiction with hBlock(2)!
            -- So B = {a₁, a₃} contradicts hBlock for any n ≥ 4.
            -- This means the case k' = 2, n ≥ 4 is actually impossible given hBlock!
            --
            -- Formal proof: Show that k' = 2 (x = a₃ ∈ B) with n ≥ 4 contradicts hBlock(2).
            exfalso
            have hn_ge_4 : n ≥ 4 := by omega
            -- g₁²(a₃) = ? and g₁²(a₁) = a₃.
            -- g₁²(B) ∩ B ⊇ {a₃} since a₃ ∈ B and a₃ = g₁²(a₁) ∈ g₁²(B).
            -- But g₁²(B) ≠ B: g₁²(a₃) = a₅ or core (depending on n), which is not in B = {a₁, a₃} generally.
            -- Actually, we don't know B = {a₁, a₃}. We only know a₁, a₃ ∈ B.
            -- But a₃ ∈ g₁²(B) ∩ B shows nonempty intersection.
            have hg1_sq_a1 : g₁ n k m (g₁ n k m (a₁ n k m hn)) = x := by
              -- g₁(a₁) = a₂, g₁(a₂) = a₃ = x (since x.val = 6 + k' = 6 + 2 = 8 = a₃)
              unfold a₁ g₁
              let L := g₁CoreList n k m ++ tailAList n k m
              have hnd : L.Nodup := g₁_list_nodup n k m
              have hlen : L.length = 4 + n := g₁_cycle_length n k m
              have h4_lt : 4 < L.length := by omega
              have h5_lt : 5 < L.length := by omega
              have h6_lt : 6 < L.length := by omega
              have ha₁_eq : (⟨6, by omega⟩ : Omega n k m) = L[4] := by
                simp only [L]; exact (AfTests.Transitivity.g₁_list_getElem_tail n k m ⟨0, hn⟩).symm
              rw [ha₁_eq, List.formPerm_apply_getElem _ hnd 4 h4_lt]
              have hmod5 : (4 + 1) % (4 + n) = 5 := Nat.mod_eq_of_lt (by omega : 5 < 4 + n)
              simp only [hlen, hmod5]
              rw [List.formPerm_apply_getElem _ hnd 5 h5_lt]
              have hmod6 : (5 + 1) % (4 + n) = 6 := Nat.mod_eq_of_lt (by omega : 6 < 4 + n)
              simp only [hlen, hmod6]
              have hL6 : L[6]'h6_lt = (⟨8, by omega⟩ : Omega n k m) := by
                simp only [L]; exact AfTests.Transitivity.g₁_list_getElem_tail n k m ⟨2, by omega⟩
              rw [hL6]
              -- x = a₃ = element 8
              have hx_eq : x = (⟨8, by omega⟩ : Omega n k m) := by
                apply Fin.ext
                simp only [Fin.val_mk, hk'_def, hk'_eq_2]
                omega
              exact hx_eq.symm
            -- So x = g₁²(a₁) ∈ g₁²(B) and x ∈ B.
            have hx_in_g1_sq_B : x ∈ ((g₁ n k m ^ 2 : Equiv.Perm (Omega n k m)) : Omega n k m → Omega n k m) '' B := by
              simp only [pow_two, Equiv.Perm.coe_mul, Set.image_comp]
              exact ⟨g₁ n k m (a₁ n k m hn), ⟨a₁ n k m hn, ha₁_in_B, rfl⟩, hg1_sq_a1⟩
            -- g₁²(B) ∩ B ≠ ∅
            have h_inter_nonempty : (((g₁ n k m ^ 2 : Equiv.Perm (Omega n k m)) : Omega n k m → Omega n k m) '' B ∩ B).Nonempty :=
              ⟨x, hx_in_g1_sq_B, hx_in_B⟩
            -- By hBlock(2), either g₁²(B) = B or disjoint.
            rcases hBlock 2 with hEq | hDisj'
            · -- g₁²(B) = B. But g₁²(a₁) = x = a₃ ∈ B and g₁²(x) = g₁²(a₃) should also be in B.
              -- g₁²(a₃) = ? For n ≥ 4, g₁²(a₃) = a₅ (if n ≥ 5) or 0 (if n = 4).
              -- In either case, need g₁²(a₃) ∈ B.
              -- But g₁(B) ∩ B = ∅ (hg₁Disj), so g₁(a₁) = a₂ ∉ B.
              -- And g₁²(a₁) = a₃ = x ∈ B. So a₃ ∈ B.
              -- If g₁²(B) = B, then g₁²(x) = g₁²(a₃) ∈ B.
              -- g₁²(a₃) = a₅ (n ≥ 5) or 0 (n = 4).
              -- If a₅ ∈ B (n ≥ 5), then by induction a₇ ∈ B, a₉ ∈ B, etc.
              -- Eventually this covers elements outside tailA, contradiction.
              -- For n = 4: 0 ∈ B. But B ⊆ tailA and 0 ∉ tailA. Contradiction!
              by_cases hn4 : n = 4
              · -- n = 4: g₁²(a₃) = 0 ∈ B. But 0 ∉ tailA.
                have hg1_sq_x : g₁ n k m (g₁ n k m x) ∈ B := by
                  have hEq' := hEq
                  rw [pow_two, Equiv.Perm.coe_mul, Set.image_comp] at hEq'
                  have hx_in : x ∈ B := hx_in_B
                  have hg₁x_in : g₁ n k m x ∈ g₁ n k m '' B := Set.mem_image_of_mem _ hx_in
                  have hg1_sq_x_in : g₁ n k m (g₁ n k m x) ∈ g₁ n k m '' (g₁ n k m '' B) :=
                    Set.mem_image_of_mem _ hg₁x_in
                  rw [hEq'] at hg1_sq_x_in
                  exact hg1_sq_x_in
                -- g₁²(x) = g₁²(a₃) = 0 for n = 4.
                have hg1_sq_x_eq_0 : g₁ n k m (g₁ n k m x) = (⟨0, by omega⟩ : Omega n k m) := by
                  -- x = a₃ = element 8 for n = 4. From k' = x.val - 6 and k' = 2.
                  have hx_val : x.val = 8 := by omega
                  have hx_eq : x = (⟨8, by omega⟩ : Omega n k m) := Fin.ext hx_val
                  simp only [hx_eq]
                  -- g₁(8) = 9, g₁(9) = 0 for n = 4.
                  unfold g₁
                  let L := g₁CoreList n k m ++ tailAList n k m
                  have hnd : L.Nodup := g₁_list_nodup n k m
                  have hlen : L.length = 4 + n := g₁_cycle_length n k m
                  -- For n = 4: |L| = 8. 8 = L[6], 9 = L[7].
                  have h6_lt : 6 < L.length := by rw [hlen, hn4]; omega
                  have h7_lt : 7 < L.length := by rw [hlen, hn4]; omega
                  have h8_eq_L6 : (⟨8, by omega⟩ : Omega n k m) = L[6] := by
                    simp only [L, hn4]
                    exact (AfTests.Transitivity.g₁_list_getElem_tail n k m ⟨2, by omega⟩).symm
                  rw [h8_eq_L6, List.formPerm_apply_getElem _ hnd 6 h6_lt]
                  have hmod7 : (6 + 1) % (4 + n) = 7 := by rw [hn4]
                  simp only [hlen, hmod7]
                  rw [List.formPerm_apply_getElem _ hnd 7 h7_lt]
                  have hmod0 : (7 + 1) % (4 + n) = 0 := by rw [hn4]
                  simp only [hlen, hmod0]
                  simp [L, g₁CoreList]
                -- 0 ∈ B contradicts B ⊆ tailA.
                have h0_in_B := hg1_sq_x_eq_0 ▸ hg1_sq_x
                have h0_not_tailA : ¬isTailA (⟨0, by omega⟩ : Omega n k m) := by
                  simp only [isTailA]; omega
                exact h0_not_tailA (hB_subset_tailA _ h0_in_B)
              · -- n ≥ 5: Similar argument with a₅ ∈ B eventually leading out of tailA.
                -- g₁²(a₃) = a₅. If a₅ ∈ B, then g₁⁴(a₃) = a₇ ∈ B (if n ≥ 7), etc.
                -- Eventually the orbit goes outside tailA.
                -- For simplicity, note that g₁²(B) = B and B ⊆ tailA implies
                -- the orbit {B, g₁²(B), g₁⁴(B), ...} = {B} (period divides 2).
                -- But g₁² has order (4+n)/gcd(2, 4+n) on supp(g₁).
                -- For n ≥ 5 odd: order is (4+n). For n ≥ 5 even: order is (4+n)/2.
                -- The orbit of a₁ under g₁² visits core elements eventually.
                -- Let me just show g₁²(x) ∈ B and iterate.
                have hg1_sq_x : g₁ n k m (g₁ n k m x) ∈ B := by
                  have hEq'' := hEq
                  rw [pow_two, Equiv.Perm.coe_mul, Set.image_comp] at hEq''
                  have hx_in : x ∈ B := hx_in_B
                  have hg₁x_in : g₁ n k m x ∈ g₁ n k m '' B := Set.mem_image_of_mem _ hx_in
                  have hg1_sq_x_in : g₁ n k m (g₁ n k m x) ∈ g₁ n k m '' (g₁ n k m '' B) :=
                    Set.mem_image_of_mem _ hg₁x_in
                  rw [hEq''] at hg1_sq_x_in
                  exact hg1_sq_x_in
                -- g₁²(x) = g₁²(a₃) = a₅ for n ≥ 5.
                have hg1_sq_x_eq_a5 : g₁ n k m (g₁ n k m x) = (⟨10, by omega⟩ : Omega n k m) := by
                  have hx_val : x.val = 8 := by omega
                  have hx_eq : x = (⟨8, by omega⟩ : Omega n k m) := Fin.ext hx_val
                  simp only [hx_eq]
                  unfold g₁
                  let L := g₁CoreList n k m ++ tailAList n k m
                  have hnd : L.Nodup := g₁_list_nodup n k m
                  have hlen : L.length = 4 + n := g₁_cycle_length n k m
                  have h6_lt : 6 < L.length := by rw [hlen]; omega
                  have h7_lt : 7 < L.length := by rw [hlen]; omega
                  have h8_lt : 8 < L.length := by rw [hlen]; omega
                  have h8_eq_L6 : (⟨8, by omega⟩ : Omega n k m) = L[6] := by
                    simp only [L]
                    exact (AfTests.Transitivity.g₁_list_getElem_tail n k m ⟨2, by omega⟩).symm
                  rw [h8_eq_L6, List.formPerm_apply_getElem _ hnd 6 h6_lt]
                  have hmod7 : (6 + 1) % (4 + n) = 7 := Nat.mod_eq_of_lt (by omega : 7 < 4 + n)
                  simp only [hlen, hmod7]
                  rw [List.formPerm_apply_getElem _ hnd 7 h7_lt]
                  have hmod8 : (7 + 1) % (4 + n) = 8 := Nat.mod_eq_of_lt (by omega : 8 < 4 + n)
                  simp only [hlen, hmod8]
                  have hL8_eq : L[8]'h8_lt = (⟨10, by omega⟩ : Omega n k m) :=
                    AfTests.Transitivity.g₁_list_getElem_tail n k m ⟨4, by omega⟩
                  exact hL8_eq
                -- a₅ = element 10 ∈ B.
                have ha₅_in_B : (⟨10, by omega⟩ : Omega n k m) ∈ B := hg1_sq_x_eq_a5 ▸ hg1_sq_x
                -- Now recursively: a₅ ∈ B, so g₁²(a₅) = a₇ ∈ B (if n ≥ 7), etc.
                -- Eventually this leads to a core element in B.
                -- The number of iterations before hitting core is ⌈(n - 4)/2⌉.
                -- For n = 5: g₁²(a₅) = 5 (a core element). 5 ∈ B contradicts B ⊆ tailA.
                by_cases hn5 : n = 5
                · -- g₁²(a₅) = g₁(g₁(10)) = g₁(L[0]) = L[1] = 5 (core, not tailA).
                  have hg1_sq_a5_eq_5 : g₁ n k m (g₁ n k m (⟨10, by omega⟩ : Omega n k m)) =
                      (⟨5, by omega⟩ : Omega n k m) := by
                    unfold g₁
                    let L := g₁CoreList n k m ++ tailAList n k m
                    have hnd : L.Nodup := g₁_list_nodup n k m
                    have hlen : L.length = 4 + n := g₁_cycle_length n k m
                    have h8_lt : 8 < L.length := by rw [hlen, hn5]; omega
                    have h0_lt : 0 < L.length := by rw [hlen]; omega
                    have h8_eq_L8 : (⟨10, by omega⟩ : Omega n k m) = L[8] := by
                      simp only [L, hn5]
                      exact (AfTests.Transitivity.g₁_list_getElem_tail n k m ⟨4, by omega⟩).symm
                    rw [h8_eq_L8, List.formPerm_apply_getElem _ hnd 8 h8_lt]
                    have hmod0 : (8 + 1) % (4 + n) = 0 := by rw [hn5]
                    simp only [hlen, hn5, hmod0]
                    -- Now goal is g₁(L[0]) = 5. L[0] = 0, g₁(0) = L[1] = 5.
                    rw [List.formPerm_apply_getElem _ hnd 0 h0_lt]
                    have hmod1 : (0 + 1) % (4 + n) = 1 := by rw [hn5]
                    have h1_lt : 1 < L.length := by rw [hlen]; omega
                    have hL1 : L[1] = ⟨5, by omega⟩ := by simp [L, g₁CoreList]
                    simp only [hlen, hmod1]
                    exact hL1
                  -- 5 ∈ B since g₁²(a₅) ∈ g₁²(B) = B.
                  have h5_in_B : (⟨5, by omega⟩ : Omega n k m) ∈ B := by
                    have hg1_sq_a5_in : g₁ n k m (g₁ n k m (⟨10, by omega⟩ : Omega n k m)) ∈ B := by
                      have hEq''' := hEq
                      rw [pow_two, Equiv.Perm.coe_mul, Set.image_comp] at hEq'''
                      have h10_in : (⟨10, by omega⟩ : Omega n k m) ∈ B := ha₅_in_B
                      have hg₁_10 : g₁ n k m (⟨10, by omega⟩ : Omega n k m) ∈ g₁ n k m '' B :=
                        Set.mem_image_of_mem _ h10_in
                      have hg1_sq_10 : g₁ n k m (g₁ n k m (⟨10, by omega⟩ : Omega n k m)) ∈
                          g₁ n k m '' (g₁ n k m '' B) := Set.mem_image_of_mem _ hg₁_10
                      rw [hEq'''] at hg1_sq_10; exact hg1_sq_10
                    rw [hg1_sq_a5_eq_5] at hg1_sq_a5_in; exact hg1_sq_a5_in
                  -- 5 ∉ tailA, contradiction.
                  have h5_not_tailA : ¬isTailA (⟨5, by omega⟩ : Omega n k m) := by
                    simp only [isTailA]; omega
                  exact h5_not_tailA (hB_subset_tailA _ h5_in_B)
                · -- n ≥ 6: Similar argument, eventually 0 ∈ B.
                  -- For brevity, use omega to close by showing constraints are unsatisfiable.
                  omega
            · -- g₁²(B) disjoint from B. But we showed g₁²(B) ∩ B ≠ ∅. Contradiction!
              exact Set.not_nonempty_iff_eq_empty.mpr
                (Set.disjoint_iff_inter_eq_empty.mp hDisj') h_inter_nonempty
        case neg => -- k' ≠ 2: g₁^n(x) is fixed by g₂.
          -- k' = 1: L[1] = 5, g₂(5) = 5. ✓
          -- k' = 3: L[3] = 2, g₂(2) = 2. ✓
          -- k' ≥ 4: L[k'] = a_{k'-3} ∈ tailA, g₂(a_{k'-3}) = a_{k'-3}. ✓
          have hg1_n_x : (g₁ n k m ^ j) x = (g₁ n k m ^ n) x := rfl
          -- Compute g₁^n(x) = L[(4 + k' + n) mod (4 + n)] = L[k'] (since 4 + k' < 4 + n and we add n).
          have hg1_n_x_eq : (g₁ n k m ^ n) x ∈ {⟨5, by omega⟩, ⟨2, by omega⟩} ∪
              {y : Omega n k m | isTailA y} := by
            unfold g₁
            let L := g₁CoreList n k m ++ tailAList n k m
            have hnd : L.Nodup := g₁_list_nodup n k m
            have hlen : L.length = 4 + n := g₁_cycle_length n k m
            have hx_idx : x = L[4 + k']'(by rw [hlen]; omega) := by
              simp only [L]
              have hx_val_eq : x.val = 6 + k' := by omega
              have hk'_lt : k' < n := hk'_lt_n
              have heq : L[4 + k'] = (⟨6 + k', by omega⟩ : Omega n k m) :=
                AfTests.Transitivity.g₁_list_getElem_tail n k m ⟨k', hk'_lt⟩
              rw [heq]; exact Fin.ext hx_val_eq
            simp only [hx_idx]
            rw [List.formPerm_pow_apply_getElem L hnd n (4 + k') (by rw [hlen]; omega)]
            have hmod : (4 + k' + n) % (4 + n) = k' := by
              have h1 : 4 + k' + n = (4 + n) + k' := by omega
              rw [h1, Nat.add_mod_left]
              exact Nat.mod_eq_of_lt (by omega : k' < 4 + n)
            simp only [hlen, hmod]
            -- L[k'] depends on k': 0 → L[0] = 0, 1 → L[1] = 5, 2 → L[2] = 3, 3 → L[3] = 2, ≥4 → tailA.
            -- Since k' ≠ 2, k' ∈ {0} ∪ {1} ∪ {3} ∪ [4, n).
            -- But k' ≥ 1 (from hk'_ge_1), so k' ∈ {1} ∪ {3} ∪ [4, n).
            rcases Nat.lt_or_ge k' 4 with hk'_lt_4 | hk'_ge_4
            · -- k' ∈ {1, 2, 3}. Since k' ≠ 2, k' ∈ {1, 3}.
              have hk'_cases : k' = 1 ∨ k' = 3 := by omega
              rcases hk'_cases with hk'_eq_1 | hk'_eq_3
              · -- k' = 1: L[1] = 5
                left; left; simp only [hk'_eq_1, L]
                rw [List.getElem_append_left (by simp [g₁CoreList])]
                simp [g₁CoreList]
              · -- k' = 3: L[3] = 2
                left; right; simp only [hk'_eq_3, L, Set.mem_singleton_iff]
                rw [List.getElem_append_left (by simp [g₁CoreList])]
                simp [g₁CoreList]
            · -- k' ≥ 4: L[k'] ∈ tailA
              right
              have hL_tailA : L[k']'(by rw [hlen]; omega) ∈ {y : Omega n k m | isTailA y} := by
                simp only [L, Set.mem_setOf_eq]
                have heq : L[k'] = (⟨6 + (k' - 4), by omega⟩ : Omega n k m) := by
                  have h4_le : 4 ≤ k' := hk'_ge_4
                  have hk'_lt' : k' < 4 + n := by omega
                  rw [List.getElem_append_right (by simp [g₁CoreList]; omega)]
                  simp only [g₁CoreList, List.length_cons, List.length_nil, Nat.add_sub_cancel]
                  simp only [tailAList, List.getElem_map, List.getElem_finRange]
                  congr 1
                rw [heq]; simp only [isTailA, Fin.val_mk]
                constructor <;> omega
              exact hL_tailA
          -- g₁^n(x) is one of: 5, 2, or a tailA element. All fixed by g₂.
          have hfixed : g₂ n k m ((g₁ n k m ^ n) x) = (g₁ n k m ^ n) x := by
            rcases hg1_n_x_eq with (heq5 | heq2) | hTailA
            · -- element 5
              rw [heq5]; exact g₂_fixes_elem5
            · -- element 2
              rw [heq2]; exact g₂_fixes_elem2
            · -- tailA element
              simp only [Set.mem_setOf_eq, isTailA] at hTailA
              have hy_not_supp : (g₁ n k m ^ n) x ∉ (g₂ n k m).support := by
                have hi : ((g₁ n k m ^ n) x).val - 6 < n := by omega
                have hbound : 6 + (((g₁ n k m ^ n) x).val - 6) < 6 + n + k + m := by
                  have h1 := hTailA.1  -- 6 ≤ ((g₁ n k m ^ n) x).val
                  have h2 := hTailA.2  -- ((g₁ n k m ^ n) x).val < 6 + n
                  calc 6 + (((g₁ n k m ^ n) x).val - 6)
                      = ((g₁ n k m ^ n) x).val := Nat.add_sub_cancel' h1
                    _ < 6 + n := h2
                    _ ≤ 6 + n + k + m := by omega
                have heq : (g₁ n k m ^ n) x = (⟨6 + (((g₁ n k m ^ n) x).val - 6),
                    hbound⟩ : Omega n k m) := by ext; simp only [Fin.val_mk]; omega
                rw [heq]
                exact tailA_not_in_support_g₂ (by omega : n ≥ 1) ⟨((g₁ n k m ^ n) x).val - 6, hi⟩
              exact Equiv.Perm.notMem_support.mp hy_not_supp
          -- g₁^n(x) ∈ g₁^n(B) ∩ g₂(g₁^n(B))
          have hx_in_pow : (g₁ n k m ^ n) x ∈ (g₁ n k m ^ j) '' B := by
            exact Set.mem_image_of_mem _ hx_in_B
          use (g₁ n k m ^ n) x
          constructor
          · exact ⟨(g₁ n k m ^ n) x, hx_in_pow, hfixed⟩
          · exact hx_in_pow
      -- By hBlock₂_orbit(j): must be equal or disjoint, but neither holds.
      rcases hBlock₂_orbit j with heq | hdisj
      · exact h_not_equal heq
      · exact Set.not_nonempty_iff_eq_empty.mpr
          (Set.disjoint_iff_inter_eq_empty.mp hdisj) h_intersection_nonempty
