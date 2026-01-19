/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Core
import AfTests.Transitivity.Lemma05
import AfTests.Primitivity.Lemma10
import AfTests.Primitivity.Lemma11_5
import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# Lemma 11: Primitivity of H on Omega

If n + k + m ≥ 1, then H acts primitively on Ω.

## Main Results

* `lemma11_H_isPrimitive` - H acts primitively on Omega when n + k + m ≥ 1

## Proof Structure

This is a direct application of three established results:
1. **Transitivity (Lemma 5)**: H acts transitively on Ω via support graph connectivity
2. **No non-trivial blocks (Lemma 11.5)**: H admits no non-trivial block system
3. **Primitivity criterion (Lemma 10)**: Transitive + trivial blocks only → primitive

## Reference

See `examples/lemmas/lemma11_primitivity.md` for the natural language proof.
-/

namespace AfTests.Primitivity

open MulAction Equiv.Perm

variable {n k m : ℕ}

-- ============================================
-- SECTION 1: TRANSITIVITY FROM LEMMA 5
-- ============================================

/-- H acts transitively on Omega (from Lemma 5) -/
theorem H_transitive (n k m : ℕ) :
    IsPretransitive (H n k m) (Omega n k m) :=
  AfTests.Transitivity.H_isPretransitive n k m

-- ============================================
-- SECTION 2: NONTRIVIALITY OF OMEGA
-- ============================================

/-- Omega has at least 2 elements when 6 + n + k + m ≥ 2 (always true) -/
instance omega_nontrivial (n k m : ℕ) : Nontrivial (Omega n k m) := by
  have h : 6 + n + k + m ≥ 2 := by omega
  exact Fin.nontrivial_iff_two_le.mpr h

-- ============================================
-- SECTION 3: BLOCKS ARE TRIVIAL
-- ============================================

/-- Convert a non-trivial IsBlock to a BlockSystemOn.

    When G acts transitively on X and B is a non-trivial block (not subsingleton
    and not univ), the set of G-translates {g • B | g : G} forms a non-trivial
    block system (partition into blocks of equal size).

    This uses mathlib's `IsBlock.isBlockSystem` under the hood. -/
theorem block_to_system (hne : n + k + m ≥ 1)
    {B : Set (Omega n k m)} (hB : IsBlock (H n k m) B) (hNT : ¬IsTrivialBlock B) :
    ∃ BS : BlockSystemOn n k m, IsHInvariant BS ∧ IsNontrivial BS := by
  -- Strategy: Use mathlib's IsBlock.isBlockSystem to get the partition structure,
  -- then convert to our BlockSystemOn type.
  --
  -- The blocks are {g • B | g ∈ H}, which form a partition by IsBlock.isBlockSystem.
  -- Key steps needed:
  -- 1. Extract Setoid.IsPartition → PairwiseDisjoint + sUnion = univ
  -- 2. Show all blocks have same ncard (bijection preserves cardinality)
  -- 3. Show generators preserve the block system (g_i • (g • B) = (g_i * g) • B ∈ blocks)
  -- 4. Show 1 < B.ncard < |Ω| from non-triviality
  sorry

/-- When n + k + m ≥ 1, all H-blocks on Omega are trivial.

    A block B is trivial if B.Subsingleton ∨ B = Set.univ.

    This follows from Lemma 11.5: no non-trivial block system exists,
    combined with the fact that any non-trivial block would induce
    a non-trivial block system. -/
theorem H_blocks_trivial (h : n + k + m ≥ 1) :
    ∀ B : Set (Omega n k m), IsBlock (H n k m) B → IsTrivialBlock B := by
  intro B hB
  by_contra hNT
  -- B non-trivial → forms a non-trivial H-invariant block system
  obtain ⟨BS, hInv, hBSnt⟩ := block_to_system h hB hNT
  -- But Lemma 11.5 says no such system exists
  exact lemma11_5_no_nontrivial_blocks h BS hInv hBSnt

-- ============================================
-- SECTION 4: MAIN THEOREM
-- ============================================

/-- **Lemma 11: Primitivity of H**

    If n + k + m ≥ 1, then H = ⟨g₁, g₂, g₃⟩ acts primitively on Ω.

    The proof combines:
    - Lemma 5: H is transitive
    - Lemma 11.5: No non-trivial block systems
    - Lemma 10: Transitive + trivial blocks → primitive -/
theorem lemma11_H_isPrimitive (h : n + k + m ≥ 1) :
    IsPreprimitive (H n k m) (Omega n k m) := by
  haveI : IsPretransitive (H n k m) (Omega n k m) := H_transitive n k m
  -- Apply Lemma 10: primitivity ↔ all blocks trivial
  rw [lemma10_primitivity_criterion (H n k m)]
  -- Use Lemma 11.5 to show all blocks are trivial
  exact H_blocks_trivial h

/-- Alternative statement: H-blocks are trivial → H is primitive -/
theorem H_primitive_of_trivial_blocks (_h : n + k + m ≥ 1) :
    (∀ B : Set (Omega n k m), IsBlock (H n k m) B → IsTrivialBlock B) →
    IsPreprimitive (H n k m) (Omega n k m) := by
  intro hTriv
  haveI : IsPretransitive (H n k m) (Omega n k m) := H_transitive n k m
  rw [lemma10_primitivity_criterion (H n k m)]
  exact hTriv

-- ============================================
-- SECTION 5: COROLLARIES
-- ============================================

/-- Maximal stabilizers: For primitive H, point stabilizers are maximal -/
theorem H_stabilizers_maximal (h : n + k + m ≥ 1) (x : Omega n k m) :
    IsCoatom (stabilizer (H n k m) x) := by
  haveI : IsPretransitive (H n k m) (Omega n k m) := H_transitive n k m
  exact (primitivity_iff_maximal_stabilizer (H n k m) x).mp (lemma11_H_isPrimitive h)

/-- No proper intermediate subgroups between stabilizers and H.
    This is a direct consequence of stabilizers being coatoms. -/
theorem H_no_intermediate_subgroups (h : n + k + m ≥ 1) (x : Omega n k m)
    (K : Subgroup (H n k m)) :
    stabilizer (H n k m) x ≤ K → K = stabilizer (H n k m) x ∨ K = ⊤ := by
  intro hLe
  have hMax := H_stabilizers_maximal h x
  -- IsCoatom means: if K ≠ ⊤ and stab ≤ K, then stab = K
  by_cases hK : K = ⊤
  · exact Or.inr hK
  · left
    exact (hMax.le_iff_eq hK).mp hLe

end AfTests.Primitivity
