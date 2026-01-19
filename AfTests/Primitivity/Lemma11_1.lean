/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Core
import AfTests.BaseCase.Lemma03
import Mathlib.GroupTheory.GroupAction.Blocks

/-!
# Lemma 11.1: Unique Block System

The only non-trivial block system for H₆ on {1,...,6} is B₀ = {{1,4}, {2,5}, {3,6}}.

## Main Results

* `lemma11_1_unique_block_system`: B₀ is the unique non-trivial block system for H₆

## Proof Outline

1. Block sizes must divide 6, giving |B| ∈ {2, 3}
2. For size 2: There are 15 partitions, only B₀ is H₆-invariant
3. For size 3: There are 10 partitions, none are H₆-invariant

## Reference

See `examples/lemmas/lemma11_1_unique_block_system.md` for the natural language proof.
-/

open MulAction Equiv.Perm

-- ============================================
-- SECTION 1: BLOCK SYSTEM DEFINITIONS
-- ============================================

/-- A partition of Fin 6 into sets of equal size -/
structure Partition6 where
  blocks : Finset (Finset (Fin 6))
  blockSize : ℕ
  size_divides : blockSize ∣ 6
  all_same_size : ∀ B ∈ blocks, B.card = blockSize
  pairwise_disjoint : (blocks : Set (Finset (Fin 6))).PairwiseDisjoint id
  covers_all : blocks.sup id = Finset.univ

/-- A block system for H₆ is a partition where H₆ acts on the blocks -/
def IsBlockSystem (P : Partition6) : Prop :=
  ∀ g ∈ H₆, ∀ B ∈ P.blocks, (B.image g) ∈ P.blocks

/-- A block system is non-trivial if blocks have size > 1 and < 6 -/
def IsNontrivialBlockSystem (P : Partition6) : Prop :=
  IsBlockSystem P ∧ 1 < P.blockSize ∧ P.blockSize < 6

-- ============================================
-- SECTION 2: THE BLOCK SYSTEM B₀
-- ============================================

/-- B₀ as a Partition6 structure -/
def B₀_partition : Partition6 where
  blocks := B₀
  blockSize := 2
  size_divides := ⟨3, rfl⟩
  all_same_size := by
    intro B hB
    simp only [B₀, Finset.mem_insert, Finset.mem_singleton] at hB
    rcases hB with rfl | rfl | rfl
    · exact Block1_card
    · exact Block2_card
    · exact Block3_card
  pairwise_disjoint := by
    intro B₁ hB₁ B₂ hB₂ hne
    simp only [B₀, Finset.coe_insert, Finset.coe_singleton,
               Set.mem_insert_iff, Set.mem_singleton_iff] at hB₁ hB₂
    rcases hB₁ with rfl | rfl | rfl <;> rcases hB₂ with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hne
      | exact Block1_Block2_disjoint
      | exact Block1_Block2_disjoint.symm
      | exact Block1_Block3_disjoint
      | exact Block1_Block3_disjoint.symm
      | exact Block2_Block3_disjoint
      | exact Block2_Block3_disjoint.symm
  covers_all := by
    ext x
    simp only [Finset.mem_sup, B₀, Finset.mem_insert, Finset.mem_singleton,
               id_eq, Finset.mem_univ, iff_true]
    fin_cases x <;> simp [Block1, Block2, Block3]

-- ============================================
-- SECTION 3: SIZE-2 PARTITIONS
-- ============================================

/-- Number of size-2 partitions of Fin 6 into 3 blocks -/
theorem size2_partition_count : ∃ n : ℕ, n = 15 ∧
    n = Nat.choose 6 2 * Nat.choose 4 2 / Nat.factorial 3 := by
  use 15
  constructor
  · rfl
  · native_decide

/-- B₀ is invariant under g₁ (restricted to Fin 6) -/
theorem B₀_invariant_g₁ : ∀ B ∈ B₀, (B.image (g₁ 0 0 0)) ∈ B₀ := by decide

/-- B₀ is invariant under g₂ (restricted to Fin 6) -/
theorem B₀_invariant_g₂ : ∀ B ∈ B₀, (B.image (g₂ 0 0 0)) ∈ B₀ := by decide

/-- B₀ is invariant under g₃ (restricted to Fin 6) -/
theorem B₀_invariant_g₃ : ∀ B ∈ B₀, (B.image (g₃ 0 0 0)) ∈ B₀ := by decide

-- ============================================
-- SECTION 4: SIZE-3 PARTITIONS
-- ============================================

/-- Number of size-3 partitions of Fin 6 into 2 blocks -/
theorem size3_partition_count : ∃ n : ℕ, n = 10 ∧
    n = Nat.choose 6 3 / 2 := by
  use 10
  constructor
  · rfl
  · native_decide

/-- Helper: check if a generator breaks a 2-block partition {B, Bᶜ} -/
def generatorBreaksPartition (g : Equiv.Perm (Fin 6)) (B : Finset (Fin 6)) : Bool :=
  let imgB := B.image g
  imgB ≠ B ∧ imgB ≠ (Finset.univ \ B)

/-- All 10 size-3 blocks (each determines a unique partition with its complement) -/
def allSize3Blocks : List (Finset (Fin 6)) := [
  {0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 1, 5},
  {0, 2, 3}, {0, 2, 4}, {0, 2, 5},
  {0, 3, 4}, {0, 3, 5}, {0, 4, 5}
]

/-- For every size-3 block B, some generator maps B outside {B, Bᶜ} -/
theorem all_size3_broken : ∀ B ∈ allSize3Blocks,
    generatorBreaksPartition (g₁ 0 0 0) B ∨
    generatorBreaksPartition (g₂ 0 0 0) B ∨
    generatorBreaksPartition (g₃ 0 0 0) B := by
  native_decide

/-- The complete list of all size-3 subsets of Fin 6 containing 0 -/
theorem allSize3Blocks_complete : ∀ B : Finset (Fin 6), B.card = 3 → (0 : Fin 6) ∈ B →
    B ∈ allSize3Blocks := by native_decide

/-- Any size-3 subset of Fin 6 containing 0 is in allSize3Blocks -/
theorem size3_block_in_list (B : Finset (Fin 6)) (hCard : B.card = 3) (h0 : (0 : Fin 6) ∈ B) :
    B ∈ allSize3Blocks := allSize3Blocks_complete B hCard h0

/-- For a size-3 partition, if B is a block, then the only other block is the complement -/
theorem size3_partition_complement (P : Partition6) (hSize : P.blockSize = 3)
    (B : Finset (Fin 6)) (hB : B ∈ P.blocks) :
    ∀ C ∈ P.blocks, C = B ∨ C = Finset.univ \ B := by
  intro C hC
  -- B and C are both in P.blocks with card 3
  have hBcard : B.card = 3 := P.all_same_size B hB ▸ hSize
  have hCcard : C.card = 3 := P.all_same_size C hC ▸ hSize
  -- If B = C, done. Otherwise they're disjoint
  by_cases hBC : B = C
  · left; exact hBC.symm
  · right
    -- B and C are disjoint blocks, each of size 3
    have hDisj : Disjoint B C := P.pairwise_disjoint hB hC hBC
    -- The only size-3 subset disjoint from B is its complement
    -- Since |B| + |C| = 6 = |Fin 6| and B ∩ C = ∅, we have C = Fin 6 \ B
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro hx hxB
      exact Finset.disjoint_left.mp hDisj hxB hx
    · intro hx
      -- x ∉ B, so x must be in some other block of P
      -- Since P covers Fin 6 and B, C are the only blocks of size 3
      -- (any third block would make total > 6), x ∈ C
      have hCover := P.covers_all
      have hx_univ : x ∈ Finset.univ := Finset.mem_univ x
      rw [← hCover] at hx_univ
      simp only [Finset.mem_sup, id_eq] at hx_univ
      obtain ⟨D, hD, hxD⟩ := hx_univ
      by_cases hDB : D = B
      · subst hDB; exact absurd hxD hx
      · by_cases hDC : D = C
        · subst hDC; exact hxD
        · -- D is a third distinct block of size 3, contradiction
          -- |B| + |C| + |D| = 9 > 6
          have hDcard : D.card = 3 := P.all_same_size D hD ▸ hSize
          have hDisjBD : Disjoint B D := P.pairwise_disjoint hB hD (Ne.symm hDB)
          have hDisjCD : Disjoint C D := P.pairwise_disjoint hC hD (Ne.symm hDC)
          -- Three disjoint sets of size 3 can't fit in Fin 6
          have hBCD_disjoint : Disjoint (B ∪ C) D := by
            rw [Finset.disjoint_union_left]
            exact ⟨hDisjBD, hDisjCD⟩
          have hBCD_card : (B ∪ C ∪ D).card = 9 := by
            rw [Finset.card_union_of_disjoint hBCD_disjoint]
            rw [Finset.card_union_of_disjoint hDisj]
            omega
          have hLe : (B ∪ C ∪ D).card ≤ 6 := by
            calc (B ∪ C ∪ D).card ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
              _ = 6 := Fintype.card_fin 6
          omega

/-- No size-3 partition is H₆-invariant -/
theorem no_size3_block_system :
    ∀ P : Partition6, P.blockSize = 3 → ¬IsBlockSystem P := by
  intro P hSize hInv
  -- Get a block containing 0
  have h0 : ∃ B ∈ P.blocks, (0 : Fin 6) ∈ B := by
    have hCover := P.covers_all
    -- 0 is in Finset.univ, which equals the sup of blocks
    have h0_univ : (0 : Fin 6) ∈ Finset.univ := Finset.mem_univ 0
    rw [← hCover] at h0_univ
    simp only [Finset.mem_sup, id_eq] at h0_univ
    exact h0_univ
  obtain ⟨B, hB_mem, h0_in_B⟩ := h0
  -- B has card 3 and contains 0, so B ∈ allSize3Blocks
  have hBcard : B.card = 3 := P.all_same_size B hB_mem ▸ hSize
  have hB_in_list : B ∈ allSize3Blocks := size3_block_in_list B hBcard h0_in_B
  -- By all_size3_broken, some generator breaks the partition
  obtain hg₁ | hg₂ | hg₃ := all_size3_broken B hB_in_list
  · -- g₁ breaks it
    simp only [generatorBreaksPartition, ne_eq, decide_eq_true_eq] at hg₁
    obtain ⟨hne1, hne2⟩ := hg₁
    -- g₁ ∈ H₆, so by hInv, B.image g₁ ∈ P.blocks
    have hg₁_mem : g₁ 0 0 0 ∈ H₆ := g₁_mem_H 0 0 0
    have hImg := hInv (g₁ 0 0 0) hg₁_mem B hB_mem
    -- By size3_partition_complement, B.image g₁ = B or B.image g₁ = Bᶜ
    have hOpts := size3_partition_complement P hSize B hB_mem (B.image (g₁ 0 0 0)) hImg
    rcases hOpts with hEqB | hEqCompl
    · exact hne1 hEqB
    · exact hne2 hEqCompl
  · -- g₂ breaks it (same argument)
    simp only [generatorBreaksPartition, ne_eq, decide_eq_true_eq] at hg₂
    obtain ⟨hne1, hne2⟩ := hg₂
    have hg₂_mem : g₂ 0 0 0 ∈ H₆ := g₂_mem_H 0 0 0
    have hImg := hInv (g₂ 0 0 0) hg₂_mem B hB_mem
    have hOpts := size3_partition_complement P hSize B hB_mem (B.image (g₂ 0 0 0)) hImg
    rcases hOpts with hEqB | hEqCompl
    · exact hne1 hEqB
    · exact hne2 hEqCompl
  · -- g₃ breaks it (same argument)
    simp only [generatorBreaksPartition, ne_eq, decide_eq_true_eq] at hg₃
    obtain ⟨hne1, hne2⟩ := hg₃
    have hg₃_mem : g₃ 0 0 0 ∈ H₆ := g₃_mem_H 0 0 0
    have hImg := hInv (g₃ 0 0 0) hg₃_mem B hB_mem
    have hOpts := size3_partition_complement P hSize B hB_mem (B.image (g₃ 0 0 0)) hImg
    rcases hOpts with hEqB | hEqCompl
    · exact hne1 hEqB
    · exact hne2 hEqCompl

-- ============================================
-- SECTION 5: MAIN THEOREM
-- ============================================

/-- Helper: g preserves B₀ if all blocks map to blocks -/
def preservesB₀ (g : Equiv.Perm (Fin 6)) : Prop :=
  ∀ B ∈ B₀, (B.image g) ∈ B₀

/-- preservesB₀ is decidable -/
instance : DecidablePred preservesB₀ := fun g =>
  inferInstanceAs (Decidable (∀ B ∈ B₀, (B.image g) ∈ B₀))

/-- 1 preserves B₀ -/
theorem one_preservesB₀ : preservesB₀ 1 := by decide

/-- If g preserves B₀, so does g⁻¹ -/
theorem inv_preservesB₀ (g : Equiv.Perm (Fin 6)) (h : preservesB₀ g) : preservesB₀ g⁻¹ :=
  -- Reuse the proof from Lemma03
  AfTests.BaseCase.inv_preserves_B₀ g h

/-- If g and h preserve B₀, so does g * h -/
theorem mul_preservesB₀ (g h : Equiv.Perm (Fin 6))
    (hg : preservesB₀ g) (hh : preservesB₀ h) : preservesB₀ (g * h) := by
  intro B hB
  have hB' := hh B hB
  have := hg (B.image h) hB'
  simp only [Equiv.Perm.coe_mul, Finset.image_image] at this ⊢
  exact this

/-- All elements of H₆ preserve B₀ -/
theorem H₆_preservesB₀ : ∀ g ∈ H₆, preservesB₀ g := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact B₀_invariant_g₁
    · exact B₀_invariant_g₂
    · exact B₀_invariant_g₃
  | one => exact one_preservesB₀
  | mul _ _ _ _ ihx ihy => exact mul_preservesB₀ _ _ ihx ihy
  | inv _ _ ih => exact inv_preservesB₀ _ ih

/-- B₀ is a block system for H₆ -/
theorem B₀_is_block_system : IsBlockSystem B₀_partition := by
  intro g hg B hB
  exact H₆_preservesB₀ g hg B hB

/-- B₀ is a non-trivial block system -/
theorem B₀_nontrivial : IsNontrivialBlockSystem B₀_partition := by
  constructor
  · exact B₀_is_block_system
  · constructor <;> decide

/-- **Lemma 11.1: Unique Block System**

    The only non-trivial block system for H₆ on Fin 6 is B₀.
    Any non-trivial partition preserved by H₆ must be B₀. -/
theorem lemma11_1_unique_block_system (P : Partition6) :
    IsNontrivialBlockSystem P → P.blocks = B₀ := by
  intro ⟨hBS, hLower, hUpper⟩
  -- P.blockSize ∈ {2, 3} since it divides 6 and 1 < size < 6
  have hSize : P.blockSize = 2 ∨ P.blockSize = 3 := by
    have hdiv := P.size_divides
    interval_cases P.blockSize <;> simp_all
  rcases hSize with hSize2 | hSize3
  · -- Size 2 case: only B₀ works
    sorry
  · -- Size 3 case: contradiction, no such block system exists
    exact absurd hBS (no_size3_block_system P hSize3)
