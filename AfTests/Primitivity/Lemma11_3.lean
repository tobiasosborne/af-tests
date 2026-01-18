/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Core
import AfTests.Primitivity.Lemma11_2

/-!
# Lemma 11.3: Tail in Block

If n ≥ 1 and g₁(B) = B for a block B containing a₁, then supp(g₁) ⊆ B.

## Main Results

* `lemma11_3_tail_in_block`: If g₁ preserves a block B containing a₁, then supp(g₁) ⊆ B

## Proof Outline

1. By assumption, n ≥ 1 so a₁ exists (element at index 6 in 0-indexed)
2. Let B be any block containing a₁
3. Assume g₁(B) = B
4. Since g₁ is a cycle and a₁ ∈ supp(g₁) ∩ B, apply Lemma 11.2
5. Therefore supp(g₁) ⊆ B

## Reference

See `examples/lemmas/lemma11_3_tail_in_block.md` for the natural language proof.
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

-- ============================================
-- SECTION 1: FIRST TAIL ELEMENT
-- ============================================

/-- The first A-tail element a₁ (index 6 in 0-indexed, representing element 7 in 1-indexed).
    Only exists when n ≥ 1. -/
def a₁ (n k m : ℕ) (hn : n ≥ 1) : Omega n k m :=
  ⟨6, by omega⟩

/-- a₁ is in the support of g₁ (it's moved by the cycle) -/
theorem a₁_mem_support_g₁ (hn : n ≥ 1) :
    a₁ n k m hn ∈ (g₁ n k m).support := by
  sorry

/-- The g₁ cycle is indeed a cycle -/
theorem g₁_isCycle (n k m : ℕ) (hn : n + 4 ≥ 2) : (g₁ n k m).IsCycle := by
  sorry

-- ============================================
-- SECTION 2: BLOCK CONTAINING a₁
-- ============================================

/-- A set contains a₁ -/
def containsA₁ (B : Set (Omega n k m)) (hn : n ≥ 1) : Prop :=
  a₁ n k m hn ∈ B

/-- If B contains a₁ and g₁(B) = B, then supp(g₁) ∩ B is nonempty -/
theorem g₁_support_meets_block (hn : n ≥ 1) (B : Set (Omega n k m))
    (hA : containsA₁ B hn) : ((g₁ n k m).support : Set (Omega n k m)) ∩ B ≠ ∅ := by
  rw [Set.nonempty_iff_ne_empty.symm]
  use a₁ n k m hn
  exact ⟨a₁_mem_support_g₁ hn, hA⟩

-- ============================================
-- SECTION 3: MAIN LEMMA
-- ============================================

/-- **Lemma 11.3: Tail in Block**

    If n ≥ 1 (so a₁ exists), B is a block containing a₁, and g₁(B) = B,
    then the entire support of g₁ is contained in B.

    Proof: This is a direct application of Lemma 11.2 (cycle_support_subset_or_disjoint).
    Since g₁ is a cycle and a₁ ∈ supp(g₁) ∩ B, the "disjoint" case is ruled out,
    so we must have supp(g₁) ⊆ B. -/
theorem lemma11_3_tail_in_block (hn : n ≥ 1) (B : Set (Omega n k m))
    (hA : containsA₁ B hn) (hB : PreservesSet (g₁ n k m) B) :
    ((g₁ n k m).support : Set (Omega n k m)) ⊆ B := by
  -- g₁ is a cycle (for n ≥ 1, cycle length is at least 5)
  have hCycle : (g₁ n k m).IsCycle := g₁_isCycle n k m (by omega)
  -- Apply Lemma 11.2
  have := cycle_support_subset_or_disjoint hCycle hB
  rcases this with hSub | hDisj
  · exact hSub
  · -- The disjoint case leads to contradiction
    exfalso
    have hMeets := g₁_support_meets_block hn B hA
    rw [Set.disjoint_iff_inter_eq_empty] at hDisj
    exact hMeets hDisj

-- ============================================
-- SECTION 4: COROLLARIES
-- ============================================

/-- All core points of g₁ are in B if g₁ preserves B containing a₁ -/
theorem g₁_core_in_block (hn : n ≥ 1) (B : Set (Omega n k m))
    (hA : containsA₁ B hn) (hB : PreservesSet (g₁ n k m) B) :
    (⟨0, by omega⟩ : Omega n k m) ∈ B ∧
    (⟨5, by omega⟩ : Omega n k m) ∈ B ∧
    (⟨3, by omega⟩ : Omega n k m) ∈ B ∧
    (⟨2, by omega⟩ : Omega n k m) ∈ B := by
  have hSub := lemma11_3_tail_in_block hn B hA hB
  -- Each core point is in the support of g₁
  sorry

/-- All tail A elements are in B if g₁ preserves B containing a₁ -/
theorem g₁_tail_in_block (hn : n ≥ 1) (B : Set (Omega n k m))
    (hA : containsA₁ B hn) (hB : PreservesSet (g₁ n k m) B)
    (i : Fin n) : (⟨6 + i.val, by have := i.isLt; omega⟩ : Omega n k m) ∈ B := by
  have hSub := lemma11_3_tail_in_block hn B hA hB
  -- Each tail element is in the support of g₁
  sorry
