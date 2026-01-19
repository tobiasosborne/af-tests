/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Primitivity.Lemma11_2
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Lemma 11.4: Block Orbit

For an ℓ-cycle σ and a σ-invariant block system, the orbit size r of any block
meeting supp(σ) divides ℓ, and each such block contains exactly ℓ/r support elements.

## Main Results

* `block_orbit_divides_cycle_length`: r divides ℓ
* `block_support_intersection_card`: |B ∩ supp(σ)| = ℓ/r

## Proof Outline

1. σ-invariance means σ induces a permutation on the blocks
2. By Orbit-Stabilizer on ⟨σ⟩ acting on blocks, r divides |⟨σ⟩| = ℓ
3. The r orbit blocks partition supp(σ) (size ℓ)
4. By symmetry (σ cycles both blocks and support), each block gets ℓ/r elements

## Reference

See `examples/lemmas/lemma11_4_block_orbit.md` for the natural language proof.
-/

open Equiv Equiv.Perm Set MulAction

variable {α : Type*} [DecidableEq α] [Fintype α]

-- ============================================
-- SECTION 1: BLOCK SYSTEM INVARIANCE
-- ============================================

/-- A block system (as a set of sets) is σ-invariant if σ permutes the blocks -/
def BlockSystemInvariant (σ : Perm α) (B : Set (Set α)) : Prop :=
  ∀ b ∈ B, σ '' b ∈ B

/-- σ induces a permutation on an invariant block system -/
theorem induced_block_perm {σ : Perm α} {B : Set (Set α)} (hInv : BlockSystemInvariant σ B) :
    ∀ b ∈ B, σ '' b ∈ B := hInv

-- ============================================
-- SECTION 2: ORBIT OF A BLOCK
-- ============================================

/-- The orbit of a block B under ⟨σ⟩ acting on blocks -/
def blockOrbit (σ : Perm α) (B : Set α) : Set (Set α) :=
  { C | ∃ k : ℤ, C = (σ ^ k) '' B }

/-- The orbit size (number of distinct blocks in the orbit) -/
noncomputable def blockOrbitSize (σ : Perm α) (B : Set α) : ℕ :=
  (blockOrbit σ B).ncard

/-- Orbit is closed under σ -/
theorem blockOrbit_closed {σ : Perm α} {B : Set α} {C : Set α}
    (hC : C ∈ blockOrbit σ B) : σ '' C ∈ blockOrbit σ B := by
  obtain ⟨k, rfl⟩ := hC
  use k + 1
  -- σ '' (σ^k '' B) = σ^(k+1) '' B
  -- Rewrite: k+1 = 1+k, then zpow_add, then image_image
  rw [show k + 1 = 1 + k from add_comm k 1, zpow_add, zpow_one, ← Set.image_comp]
  rfl

-- ============================================
-- SECTION 3: CYCLE LENGTH AND ORBIT DIVISIBILITY
-- ============================================

/-- The cycle length of an ℓ-cycle -/
noncomputable def cycleLength (σ : Perm α) : ℕ := σ.support.card

/-- For a cycle, the cyclic subgroup has order equal to the cycle length -/
theorem zpowers_card_eq_cycle_length {σ : Perm α} (hσ : σ.IsCycle) :
    Nat.card (Subgroup.zpowers σ) = cycleLength σ := by
  -- Use mathlib's result that orderOf σ = #σ.support for cycles
  simp only [cycleLength, Nat.card_eq_fintype_card, Fintype.card_zpowers]
  exact hσ.orderOf

/-- **Block orbit divides cycle length**

    If σ is a cycle and B is a block with B ∩ supp(σ) ≠ ∅ in a σ-invariant
    block system, then the orbit size r divides the cycle length ℓ. -/
theorem block_orbit_divides_cycle_length {σ : Perm α} (hσ : σ.IsCycle)
    {B : Set α} {Blocks : Set (Set α)} (hInv : BlockSystemInvariant σ Blocks)
    (hB : B ∈ Blocks) (hMeet : (B ∩ (σ.support : Set α)).Nonempty) :
    blockOrbitSize σ B ∣ cycleLength σ := by
  -- By Orbit-Stabilizer theorem
  sorry

-- ============================================
-- SECTION 4: SUPPORT DISTRIBUTION
-- ============================================

/-- Blocks in the orbit are exactly those meeting the support -/
theorem orbit_blocks_meet_support {σ : Perm α} (hσ : σ.IsCycle)
    {B : Set α} (hMeet : (B ∩ (σ.support : Set α)).Nonempty)
    {C : Set α} (hC : C ∈ blockOrbit σ B) :
    (C ∩ (σ.support : Set α)).Nonempty := by
  -- σ permutes supp(σ), so σⁱ(B) ∩ supp(σ) ≠ ∅
  obtain ⟨x, hxB, hxSupp⟩ := hMeet
  obtain ⟨k, rfl⟩ := hC
  -- (σ^k) x is in C = (σ^k) '' B
  refine ⟨(σ ^ k) x, mem_image_of_mem _ hxB, ?_⟩
  -- (σ^k) x is in support since x is in support and σ permutes its support
  exact zpow_apply_mem_support.mpr hxSupp

/-- The orbit blocks partition the support -/
theorem orbit_blocks_partition_support {σ : Perm α} (hσ : σ.IsCycle)
    {B : Set α} {Blocks : Set (Set α)} (hInv : BlockSystemInvariant σ Blocks)
    (hB : B ∈ Blocks) (hMeet : (B ∩ (σ.support : Set α)).Nonempty)
    (hDisj : Blocks.PairwiseDisjoint id) :
    (σ.support : Set α) = ⋃ C ∈ blockOrbit σ B, (C ∩ (σ.support : Set α)) := by
  sorry

/-- **Support intersection cardinality**

    Each block in the orbit contains exactly ℓ/r elements of supp(σ),
    where ℓ is the cycle length and r is the orbit size. -/
theorem block_support_intersection_card {σ : Perm α} (hσ : σ.IsCycle)
    {B : Set α} {Blocks : Set (Set α)} (hInv : BlockSystemInvariant σ Blocks)
    (hB : B ∈ Blocks) (hMeet : (B ∩ (σ.support : Set α)).Nonempty)
    (hDisj : Blocks.PairwiseDisjoint id) :
    (B ∩ (σ.support : Set α)).ncard = cycleLength σ / blockOrbitSize σ B := by
  -- By symmetry: σ cycles both blocks and support elements
  sorry

-- ============================================
-- SECTION 5: MAIN LEMMA
-- ============================================

/-- **Lemma 11.4: Block Orbit**

    Let σ be an ℓ-cycle and B a σ-invariant block system.
    Let B ∈ B with B ∩ supp(σ) ≠ ∅, and let r be the orbit size of B.
    Then:
    1. r divides ℓ
    2. |B ∩ supp(σ)| = ℓ/r -/
theorem lemma11_4_block_orbit {σ : Perm α} (hσ : σ.IsCycle)
    {B : Set α} {Blocks : Set (Set α)} (hInv : BlockSystemInvariant σ Blocks)
    (hB : B ∈ Blocks) (hMeet : (B ∩ (σ.support : Set α)).Nonempty)
    (hDisj : Blocks.PairwiseDisjoint id) :
    blockOrbitSize σ B ∣ cycleLength σ ∧
    (B ∩ (σ.support : Set α)).ncard = cycleLength σ / blockOrbitSize σ B := by
  constructor
  · exact block_orbit_divides_cycle_length hσ hInv hB hMeet
  · exact block_support_intersection_card hσ hInv hB hMeet hDisj
