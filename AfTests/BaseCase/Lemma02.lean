/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Core
import AfTests.BaseCase.Lemma01
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# Lemma 2: Induced Action on Blocks

The map φ: H₆ → S_{B₀} ≅ S₃ induced by the action on blocks satisfies:
1. φ(g₁) = (B₁ B₃) - transposition swapping blocks 1 and 3
2. φ(g₂) = (B₁ B₂) - transposition swapping blocks 1 and 2
3. φ(g₃) = (B₂ B₃) - transposition swapping blocks 2 and 3

Corollary: Im(φ) = S₃

## Main Results

* `blockAction` - Function mapping permutation to its action on block indices
* `φ_g₁_eq_swap` - g₁ swaps blocks 0 and 2 (i.e., Block1 and Block3)
* `φ_g₂_eq_swap` - g₂ swaps blocks 0 and 1 (i.e., Block1 and Block2)
* `φ_g₃_eq_swap` - g₃ swaps blocks 1 and 2 (i.e., Block2 and Block3)
* `φ_surjective` - The induced action is surjective onto S₃

## Proof Strategy

Read off the block permutation from Lemma 1's results.

## Reference

See `examples/lemmas/lemma02_induced_action.md` for the natural language proof.
-/

/-- Given a permutation on Fin 6 and a block index, return the index of the image block.
    Block indices: 0 = Block1, 1 = Block2, 2 = Block3 -/
def blockAction (g : Equiv.Perm (Fin 6)) (i : Fin 3) : Fin 3 :=
  let block := match i with
    | 0 => Block1
    | 1 => Block2
    | 2 => Block3
  let imageBlock := block.image g
  if imageBlock = Block1 then 0
  else if imageBlock = Block2 then 1
  else 2

/-- The block action of a permutation is a permutation of Fin 3 -/
def blockPerm (g : Equiv.Perm (Fin 6)) : Equiv.Perm (Fin 3) where
  toFun := blockAction g
  invFun := blockAction g⁻¹
  left_inv := by intro i; sorry
  right_inv := by intro i; sorry

/-- g₁ induces the transposition (0 2) on blocks: swaps Block1 ↔ Block3, fixes Block2 -/
theorem φ_g₁_eq_swap : blockPerm (g₁ 0 0 0) = Equiv.swap 0 2 := by
  sorry  -- TODO: Phase 2 - prove via blockAction computation

/-- g₂ induces the transposition (0 1) on blocks: swaps Block1 ↔ Block2, fixes Block3 -/
theorem φ_g₂_eq_swap : blockPerm (g₂ 0 0 0) = Equiv.swap 0 1 := by
  sorry  -- TODO: Phase 2 - prove via blockAction computation

/-- g₃ induces the transposition (1 2) on blocks: swaps Block2 ↔ Block3, fixes Block1 -/
theorem φ_g₃_eq_swap : blockPerm (g₃ 0 0 0) = Equiv.swap 1 2 := by
  sorry  -- TODO: Phase 2 - prove via blockAction computation

/-- The three transpositions (0 1), (0 2), (1 2) generate S₃ -/
theorem S3_generated_by_transpositions :
    Subgroup.closure ({Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2} : Set (Equiv.Perm (Fin 3)))
    = ⊤ := by
  sorry

/-- The image of {g₁, g₂, g₃} under blockPerm generates S₃ -/
theorem φ_image_generates_S3 :
    Subgroup.closure {blockPerm (g₁ 0 0 0), blockPerm (g₂ 0 0 0), blockPerm (g₃ 0 0 0)} = ⊤ := by
  rw [φ_g₁_eq_swap, φ_g₂_eq_swap, φ_g₃_eq_swap]
  -- The closure of these three transpositions is S₃
  sorry
