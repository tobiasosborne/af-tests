/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Primitivity.Lemma11_2
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Period
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Data.ZMod.QuotientGroup

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
open scoped Pointwise

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

/-- The pointwise action: σ • B = σ '' B for permutations acting on sets -/
theorem perm_smul_set_eq_image (σ : Perm α) (B : Set α) : σ • B = σ '' B := by
  ext x
  simp only [Set.mem_smul_set, Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, Perm.smul_def σ y⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (Perm.smul_def σ y).symm⟩

/-- The orbit under zpowers is exactly the block orbit -/
theorem blockOrbit_eq_orbit (σ : Perm α) (B : Set α) :
    blockOrbit σ B = { C | ∃ k : ℤ, C = σ ^ k • B } := by
  ext C
  simp only [blockOrbit, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, rfl⟩
    use k
    rw [perm_smul_set_eq_image]
  · rintro ⟨k, rfl⟩
    use k
    rw [perm_smul_set_eq_image]

/-- The period of σ acting on a set B (via pointwise action) -/
noncomputable def setPeriod (σ : Perm α) (B : Set α) : ℕ := MulAction.period σ B

/-- Period divides orderOf for permutation action on sets -/
theorem setPeriod_dvd_orderOf (σ : Perm α) (B : Set α) : setPeriod σ B ∣ orderOf σ :=
  MulAction.period_dvd_orderOf σ B

/-- blockOrbit equals the MulAction orbit under zpowers -/
theorem blockOrbit_eq_MulAction_orbit (σ : Perm α) (B : Set α) :
    blockOrbit σ B = (MulAction.orbit (Subgroup.zpowers σ) B : Set (Set α)) := by
  ext C
  rw [blockOrbit_eq_orbit]
  simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨⟨σ ^ k, ⟨k, rfl⟩⟩, rfl⟩
  · rintro ⟨⟨_, ⟨k, rfl⟩⟩, rfl⟩
    exact ⟨k, rfl⟩

/-- Orbit ncard equals period via minimalPeriod relationship -/
theorem orbit_ncard_eq_period (σ : Perm α) (B : Set α) :
    (MulAction.orbit (Subgroup.zpowers σ) B : Set (Set α)).ncard = MulAction.period σ B := by
  rw [MulAction.period_eq_minimalPeriod]
  -- The orbit is finite since Set α is finite (Fintype α implies Fintype (Set α))
  haveI : Fintype (Set α) := Set.fintype
  haveI : Fintype ↑(MulAction.orbit (↥(Subgroup.zpowers σ)) B) := Fintype.ofFinite _
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, MulAction.minimalPeriod_eq_card]

/-- The orbit size equals the period -/
theorem blockOrbitSize_eq_setPeriod {σ : Perm α} (hσ : σ.IsCycle) (B : Set α) :
    blockOrbitSize σ B = setPeriod σ B := by
  unfold blockOrbitSize setPeriod
  rw [blockOrbit_eq_MulAction_orbit, orbit_ncard_eq_period]

/-- **Block orbit divides cycle length**

    If σ is a cycle and B is a block with B ∩ supp(σ) ≠ ∅ in a σ-invariant
    block system, then the orbit size r divides the cycle length ℓ. -/
theorem block_orbit_divides_cycle_length {σ : Perm α} (hσ : σ.IsCycle)
    {B : Set α} {Blocks : Set (Set α)} (hInv : BlockSystemInvariant σ Blocks)
    (hB : B ∈ Blocks) (hMeet : (B ∩ (σ.support : Set α)).Nonempty) :
    blockOrbitSize σ B ∣ cycleLength σ := by
  -- Strategy: blockOrbitSize = period σ B divides orderOf σ = cycleLength σ
  rw [blockOrbitSize_eq_setPeriod hσ]
  calc setPeriod σ B ∣ orderOf σ := setPeriod_dvd_orderOf σ B
    _ = cycleLength σ := by unfold cycleLength; exact hσ.orderOf

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
    {B : Set α} {Blocks : Set (Set α)} (_hInv : BlockSystemInvariant σ Blocks)
    (_hB : B ∈ Blocks) (hMeet : (B ∩ (σ.support : Set α)).Nonempty)
    (_hDisj : Blocks.PairwiseDisjoint id) :
    (σ.support : Set α) = ⋃ C ∈ blockOrbit σ B, (C ∩ (σ.support : Set α)) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · intro hx
    obtain ⟨y, hyB, hySupp⟩ := hMeet
    -- Use that σ is a cycle: there exists k such that σ^k(y) = x
    have hy_ne : σ y ≠ y := Perm.mem_support.mp hySupp
    have hx_ne : σ x ≠ x := Perm.mem_support.mp hx
    obtain ⟨k, hk⟩ := hσ.sameCycle hy_ne hx_ne
    -- σ^k(y) = x is in σ^k(B) ∩ support
    refine ⟨(σ ^ k) '' B, ⟨k, rfl⟩, ?_, ?_⟩
    · rw [← hk]; exact mem_image_of_mem _ hyB
    · rw [← hk]; exact zpow_apply_mem_support.mpr hySupp
  · intro ⟨_, _, _, hxSupp⟩
    exact hxSupp

/-- σ maps B ∩ support to (σ B) ∩ support bijectively -/
theorem sigma_preserves_intersection_card (σ : Perm α) (B : Set α) :
    (σ '' B ∩ (σ.support : Set α)).ncard = (B ∩ (σ.support : Set α)).ncard := by
  -- Key fact: σ '' B ∩ support = σ '' (B ∩ support) since σ preserves support
  have heq : σ '' B ∩ (σ.support : Set α) = σ '' (B ∩ σ.support) := by
    ext y
    constructor
    · rintro ⟨⟨x, hxB, rfl⟩, hyS⟩
      exact ⟨x, ⟨hxB, Perm.apply_mem_support.mp hyS⟩, rfl⟩
    · rintro ⟨x, ⟨hxB, hxS⟩, rfl⟩
      exact ⟨⟨x, hxB, rfl⟩, Perm.apply_mem_support.mpr hxS⟩
  rw [heq]
  exact Set.ncard_image_of_injective _ σ.injective

/-- All blocks in the orbit have the same intersection size with support -/
theorem orbit_blocks_same_card (σ : Perm α) (B : Set α) (k : ℤ) :
    ((σ ^ k) '' B ∩ (σ.support : Set α)).ncard = (B ∩ (σ.support : Set α)).ncard := by
  -- Key: (σ^k '' B) ∩ support = σ^k '' (B ∩ support), and σ^k is a bijection
  have heq : (σ ^ k) '' B ∩ (σ.support : Set α) = (σ ^ k) '' (B ∩ σ.support) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_image]
    constructor
    · rintro ⟨⟨x, hxB, rfl⟩, hyS⟩
      refine ⟨x, ⟨hxB, ?_⟩, rfl⟩
      exact zpow_apply_mem_support.mp hyS
    · rintro ⟨x, ⟨hxB, hxS⟩, rfl⟩
      exact ⟨⟨x, hxB, rfl⟩, zpow_apply_mem_support.mpr hxS⟩
  rw [heq]
  exact Set.ncard_image_of_injective _ (σ ^ k).injective

/-- **Support intersection cardinality**

    Each block in the orbit contains exactly ℓ/r elements of supp(σ),
    where ℓ is the cycle length and r is the orbit size.

    Proof outline (TODO):
    1. All orbit blocks have equal intersection size with support (orbit_blocks_same_card)
    2. Orbit blocks partition the support (orbit_blocks_partition_support)
    3. So cycleLength = blockOrbitSize × (B ∩ support).ncard
    4. Therefore (B ∩ support).ncard = cycleLength / blockOrbitSize -/
theorem block_support_intersection_card {σ : Perm α} (hσ : σ.IsCycle)
    {B : Set α} {Blocks : Set (Set α)} (_hInv : BlockSystemInvariant σ Blocks)
    (_hB : B ∈ Blocks) (hMeet : (B ∩ (σ.support : Set α)).Nonempty)
    (_hDisj : Blocks.PairwiseDisjoint id) :
    (B ∩ (σ.support : Set α)).ncard = cycleLength σ / blockOrbitSize σ B := by
  -- All orbit blocks have the same intersection size
  have _heq_card : ∀ C ∈ blockOrbit σ B, (C ∩ ↑σ.support).ncard = (B ∩ ↑σ.support).ncard := by
    intro C hC
    obtain ⟨k, rfl⟩ := hC
    exact orbit_blocks_same_card σ B k
  -- The orbit size divides the cycle length
  have _hdiv := block_orbit_divides_cycle_length hσ _hInv _hB hMeet
  -- Requires cardinality arithmetic over finite sums - see proof outline above
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
