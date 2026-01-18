/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Support

/-!
# Lemma 11.2: Cycle Fixing Block

If σ is a cycle and B is a set with σ(B) = B, then either:
- supp(σ) ⊆ B, or
- supp(σ) ∩ B = ∅

## Main Results

* `cycle_support_subset_or_disjoint`: Main lemma about cycles and block preservation

## Proof Outline

If any element of the cycle support is in B, then by applying σ repeatedly
(using σ(B) = B), all cycle elements must be in B.

## Reference

See `examples/lemmas/lemma11_2_cycle_fixing_block.md` for the natural language proof.
-/

open Equiv Equiv.Perm Set

variable {α : Type*} [DecidableEq α] [Fintype α]

-- ============================================
-- SECTION 1: SET PRESERVATION DEFINITIONS
-- ============================================

/-- A permutation σ preserves a set B if σ(B) = B -/
def PreservesSet (σ : Perm α) (B : Set α) : Prop :=
  σ '' B = B

/-- Equivalent formulation: x ∈ B ↔ σ(x) ∈ B -/
theorem preservesSet_iff_mem (σ : Perm α) (B : Set α) :
    PreservesSet σ B ↔ ∀ x, x ∈ B ↔ σ x ∈ B := by
  sorry

/-- If σ preserves B and x ∈ B, then σ(x) ∈ B -/
theorem preservesSet_apply {σ : Perm α} {B : Set α} (h : PreservesSet σ B)
    {x : α} (hx : x ∈ B) : σ x ∈ B := by
  rw [preservesSet_iff_mem] at h
  exact (h x).mp hx

-- ============================================
-- SECTION 2: CYCLE SUPPORT PROPERTIES
-- ============================================

/-- If σ is a cycle and x is in the support, then σ^k(x) is in the support -/
theorem IsCycle.zpow_apply_mem_support {σ : Perm α} (hσ : σ.IsCycle) {x : α}
    (hx : x ∈ σ.support) (k : ℤ) : (σ ^ k) x ∈ σ.support := by
  sorry

/-- The support of a cycle is closed under σ -/
theorem IsCycle.support_closed {σ : Perm α} (hσ : σ.IsCycle) {x : α}
    (hx : x ∈ σ.support) : σ x ∈ σ.support := by
  -- If σ(σ(x)) = σ(x), then σ(x) is a fixed point, but cycles have no
  -- interior fixed points, so σ(x) ≠ x implies σ(σ(x)) ≠ σ(x)
  sorry

/-- All elements in a cycle's support are related by SameCycle -/
theorem IsCycle.support_sameCycle {σ : Perm α} (hσ : σ.IsCycle) {x y : α}
    (hx : x ∈ σ.support) (hy : y ∈ σ.support) : σ.SameCycle x y := by
  rw [mem_support] at hx hy
  exact hσ.sameCycle hx hy

-- ============================================
-- SECTION 3: MAIN LEMMA
-- ============================================

/-- If any support element is in B, then all support elements are in B -/
theorem cycle_support_in_B_of_one_in_B {σ : Perm α} (hσ : σ.IsCycle) {B : Set α}
    (hB : PreservesSet σ B) {x : α} (hxS : x ∈ σ.support) (hxB : x ∈ B) :
    ∀ y ∈ σ.support, y ∈ B := by
  -- All support elements are σ^k(x) for some k
  -- Since σ(B) = B, we have σ^k(B) = B, so σ^k(x) ∈ B
  sorry

/-- **Lemma 11.2: Cycle Fixing Block**

    Let σ be a cycle and B a set with σ(B) = B.
    Then either supp(σ) ⊆ B or supp(σ) ∩ B = ∅.

    Proof: If supp(σ) ∩ B ≠ ∅, pick x in the intersection.
    Since σ(B) = B, applying σ repeatedly keeps us in B.
    Since σ is a cycle, we eventually reach all support elements.
    Hence supp(σ) ⊆ B. -/
theorem cycle_support_subset_or_disjoint {σ : Perm α} (hσ : σ.IsCycle) {B : Set α}
    (hB : PreservesSet σ B) :
    (σ.support : Set α) ⊆ B ∨ Disjoint (σ.support : Set α) B := by
  by_cases h : ((σ.support : Set α) ∩ B).Nonempty
  · -- Case: intersection is nonempty
    left
    obtain ⟨x, hxS, hxB⟩ := h
    intro y hy
    exact cycle_support_in_B_of_one_in_B hσ hB hxS hxB y hy
  · -- Case: intersection is empty
    right
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [Set.disjoint_iff_inter_eq_empty]
    exact h

-- ============================================
-- SECTION 4: COROLLARIES
-- ============================================

/-- Contrapositive: if support meets B but isn't contained, then σ doesn't preserve B -/
theorem cycle_not_preserves_of_partial_intersection {σ : Perm α} (hσ : σ.IsCycle) {B : Set α}
    (hMeet : ((σ.support : Set α) ∩ B).Nonempty)
    (hNotContained : ¬((σ.support : Set α) ⊆ B)) :
    ¬PreservesSet σ B := by
  intro hB
  have := cycle_support_subset_or_disjoint hσ hB
  rcases this with hSub | hDisj
  · exact hNotContained hSub
  · obtain ⟨x, hx⟩ := hMeet
    exact Set.disjoint_iff.mp hDisj hx

/-- For finite types: support is disjoint from B iff no support element is in B -/
theorem cycle_support_disjoint_iff {σ : Perm α} {B : Set α} :
    Disjoint (σ.support : Set α) B ↔ ∀ x ∈ σ.support, x ∉ B := by
  rw [Set.disjoint_iff]
  constructor
  · intro h x hxS hxB
    exact h ⟨hxS, hxB⟩
  · intro h x ⟨hxS, hxB⟩
    exact h x hxS hxB
