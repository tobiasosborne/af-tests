/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Core
import AfTests.Primitivity.Lemma11_2
import AfTests.Primitivity.Lemma11_3
import AfTests.Primitivity.Lemma11_4

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
-- SECTION 2: FIXED POINT LEMMAS
-- ============================================

/-- Elements outside supp(σ) are fixed by σ -/
theorem fixed_outside_support {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) (x : α) (hx : x ∉ σ.support) : σ x = x := by
  simp only [Finset.mem_coe, mem_support, ne_eq, not_not] at hx
  exact hx

/-- Tail A elements are not in the g₂ cycle list -/
theorem tailA_not_in_g₂_list (i : Fin n) :
    (⟨6 + i.val, by omega⟩ : Omega n k m) ∉ g₂CoreList n k m ++ tailBList n k m := by
  intro h
  simp only [List.mem_append, g₂CoreList, tailBList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · -- In core list [1, 3, 4, 0]
    rcases h with h | h | h | h
    all_goals simp only [Fin.ext_iff] at h; omega
  · -- In tailBList (which starts at 6+n, but i < n so 6+i < 6+n)
    obtain ⟨j, _, hj⟩ := h
    simp only [Fin.ext_iff] at hj
    have := i.isLt  -- i < n
    omega

/-- Tail A elements are not in supp(g₂) -/
theorem tailA_not_in_support_g₂ (hn : n ≥ 1) (i : Fin n) :
    (⟨6 + i.val, by omega⟩ : Omega n k m) ∉ (g₂ n k m).support := by
  simp only [g₂, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_not_mem
  exact tailA_not_in_g₂_list i

/-- Tail A elements are not in the g₃ cycle list -/
theorem tailA_not_in_g₃_list (i : Fin n) :
    (⟨6 + i.val, by omega⟩ : Omega n k m) ∉ g₃CoreList n k m ++ tailCList n k m := by
  intro h
  simp only [List.mem_append, g₃CoreList, tailCList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · -- In core list [2, 4, 5, 1]
    rcases h with h | h | h | h
    all_goals simp only [Fin.ext_iff] at h; omega
  · -- In tailCList (which starts at 6+n+k, but i < n so 6+i < 6+n+k)
    obtain ⟨j, _, hj⟩ := h
    simp only [Fin.ext_iff] at hj
    have := i.isLt  -- i < n
    omega

/-- Tail A elements are not in supp(g₃) -/
theorem tailA_not_in_support_g₃ (hn : n ≥ 1) (i : Fin n) :
    (⟨6 + i.val, by omega⟩ : Omega n k m) ∉ (g₃ n k m).support := by
  simp only [g₃, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_not_mem
  exact tailA_not_in_g₃_list i

/-- g₂ fixes tail A elements -/
theorem g₂_fixes_tailA (hn : n ≥ 1) (i : Fin n) :
    g₂ n k m ⟨6 + i.val, by omega⟩ = ⟨6 + i.val, by omega⟩ := by
  exact fixed_outside_support _ _ (tailA_not_in_support_g₂ hn i)

/-- Element 2 is not in the g₂ cycle list -/
theorem elem2_not_in_g₂_list :
    (⟨2, by omega⟩ : Omega n k m) ∉ g₂CoreList n k m ++ tailBList n k m := by
  intro h
  simp only [List.mem_append, g₂CoreList, tailBList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h
    all_goals simp only [Fin.ext_iff] at h; omega
  · obtain ⟨j, _, hj⟩ := h
    simp only [Fin.ext_iff] at hj
    omega

/-- Element 2 is not in supp(g₂) -/
theorem elem2_not_in_support_g₂ :
    (⟨2, by omega⟩ : Omega n k m) ∉ (g₂ n k m).support := by
  simp only [g₂, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_not_mem
  exact elem2_not_in_g₂_list

/-- g₂ fixes element 2 -/
theorem g₂_fixes_elem2 :
    g₂ n k m (⟨2, by omega⟩ : Omega n k m) = ⟨2, by omega⟩ := by
  exact fixed_outside_support _ _ elem2_not_in_support_g₂

/-- Element 2 is in supp(g₁) (since it's in g₁CoreList [0, 5, 3, 2]) -/
theorem elem2_in_support_g₁ (hn : n ≥ 1) :
    (⟨2, by omega⟩ : Omega n k m) ∈ (g₁ n k m).support := by
  have hNodup := g₁_list_nodup n k m
  have hNotSingleton : ∀ x, g₁CoreList n k m ++ tailAList n k m ≠ [x] := by
    intro x h
    have : (g₁CoreList n k m ++ tailAList n k m).length = 1 := by rw [h]; simp
    have := g₁_cycle_length n k m
    omega
  rw [g₁, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₁CoreList, List.mem_cons]
  tauto

/-- g₃ fixes tail A elements -/
theorem g₃_fixes_tailA (hn : n ≥ 1) (i : Fin n) :
    g₃ n k m ⟨6 + i.val, by omega⟩ = ⟨6 + i.val, by omega⟩ := by
  exact fixed_outside_support _ _ (tailA_not_in_support_g₃ hn i)

-- ============================================
-- SECTION 3: CASE ANALYSIS HELPERS
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
-- SECTION 4: MAIN THEOREM
-- ============================================

/-- **Lemma 11.5: No Non-trivial Blocks**

    If n + k + m ≥ 1, then H admits no non-trivial H-invariant block system on Ω.

    The proof proceeds by case analysis on which generators stabilize the block
    containing a₁ (WLOG n ≥ 1), using fixed-point arguments to derive contradictions. -/
theorem lemma11_5_no_nontrivial_blocks (h : n + k + m ≥ 1) :
    ∀ BS : BlockSystemOn n k m, IsHInvariant BS → ¬IsNontrivial BS := by
  intro BS hInv hNT
  -- WLOG n ≥ 1 (by symmetry, can relabel generators)
  -- Let B be the block containing a₁
  -- Case analysis on g₁(B) = B vs g₁(B) ≠ B leads to contradictions
  sorry
