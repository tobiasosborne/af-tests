/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Core
import AfTests.BaseCase.Lemma01
import AfTests.BaseCase.Lemma02
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Lemma 3: Base Case Structure (H₆ ≅ S₄)

We prove H₆ = ⟨h₁, h₂, h₃⟩ is isomorphic to S₄, acting imprimitively on {1,...,6}.

## Main Results

* `H₆_iso_S4` - H₆ ≅ S₄
* `H₆_imprimitive` - H₆ acts imprimitively on Ω = {1,...,6}
* `H₆_card_eq_24` - |H₆| = 24 (as subgroup cardinality)

## Proof Strategy

By Lemma 1, H₆ preserves the partition B₀ = {{0,3}, {1,4}, {2,5}}.
By Lemma 2, the induced homomorphism φ: H₆ → S₃ is surjective.
The kernel ker(φ) is a Klein 4-group V₄ of order 4.
By the first isomorphism theorem: |H₆| = |S₃| × |V₄| = 6 × 4 = 24 = |S₄|.

## Reference

See `examples/lemmas/lemma03_base_case_structure.md` for the natural language proof.
-/

namespace AfTests.BaseCase

open Equiv Equiv.Perm

/-- The kernel of the block action homomorphism consists of elements fixing each block setwise.
    These are products of an even number of within-block transpositions. -/
def kernelElements : Finset (Equiv.Perm (Fin 6)) :=
  { 1,  -- identity
    Equiv.swap (0 : Fin 6) 3 * Equiv.swap 1 4,  -- (0 3)(1 4)
    Equiv.swap (0 : Fin 6) 3 * Equiv.swap 2 5,  -- (0 3)(2 5)
    Equiv.swap (1 : Fin 6) 4 * Equiv.swap 2 5   -- (1 4)(2 5)
  }

/-- The kernel has 4 elements -/
theorem kernelElements_card : kernelElements.card = 4 := by native_decide

/-- Identity preserves blocks -/
theorem one_preserves_B₀ : ∀ B ∈ B₀, B.image (1 : Equiv.Perm (Fin 6)) ∈ B₀ := by
  intro B hB
  convert hB using 1
  ext x
  simp only [Finset.mem_image, Equiv.Perm.coe_one, id_eq, exists_eq_right]

/-- If g preserves B₀, then g⁻¹ preserves B₀ -/
theorem inv_preserves_B₀ (g : Equiv.Perm (Fin 6))
    (hg : ∀ B ∈ B₀, B.image g ∈ B₀) : ∀ B ∈ B₀, B.image (g⁻¹ : Equiv.Perm (Fin 6)) ∈ B₀ := by
  -- g induces a bijection on B₀ (3 blocks), so g⁻¹ does too.
  -- For each B ∈ B₀, there exists B' ∈ B₀ with B'.image g = B, so B.image g⁻¹ = B'.
  intro B hB
  -- The map B ↦ B.image g is injective on B₀ (since g is injective)
  have inj : Set.InjOn (Finset.image g) B₀ := by
    intro B₁ hB₁ B₂ hB₂ heq
    ext x
    constructor
    · intro hx
      have h1 : g x ∈ B₁.image g := Finset.mem_image_of_mem g hx
      rw [heq] at h1
      obtain ⟨y, hy, heq'⟩ := Finset.mem_image.mp h1
      exact g.injective heq' ▸ hy
    · intro hx
      have h2 : g x ∈ B₂.image g := Finset.mem_image_of_mem g hx
      rw [← heq] at h2
      obtain ⟨y, hy, heq'⟩ := Finset.mem_image.mp h2
      exact g.injective heq' ▸ hy
  -- The map is surjective because it's injective on a finite set mapping to itself
  have surj : Set.SurjOn (Finset.image g) B₀ B₀ := by
    apply Finset.surjOn_of_injOn_of_card_le
    · exact fun B hB => hg B hB
    · exact inj
    · exact le_refl _
  -- Get the preimage block B' such that B'.image g = B
  obtain ⟨B', hB', heq⟩ := surj hB
  -- Show B.image g⁻¹ = B'
  convert hB' using 1
  rw [← heq]
  ext x
  simp only [Finset.mem_image, Equiv.Perm.coe_inv]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simp only [Equiv.symm_apply_apply]
    exact hz
  · intro hx
    exact ⟨g x, ⟨x, hx, rfl⟩, g.symm_apply_apply x⟩

/-- If g, h preserve B₀, then g * h preserves B₀ -/
theorem mul_preserves_B₀ (g h : Equiv.Perm (Fin 6))
    (hg : ∀ B ∈ B₀, B.image g ∈ B₀) (hh : ∀ B ∈ B₀, B.image h ∈ B₀) :
    ∀ B ∈ B₀, B.image (g * h) ∈ B₀ := by
  intro B hB
  have : B.image (g * h) = (B.image h).image g := by
    ext x
    simp only [Finset.mem_image, Equiv.Perm.coe_mul, Function.comp_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨h y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [this]
  exact hg _ (hh B hB)

/-- H₆ acts imprimitively: it preserves the non-trivial block partition B₀ -/
theorem H₆_imprimitive : ∀ (g : H₆), ∀ B ∈ B₀, B.image g.val ∈ B₀ := by
  intro ⟨g, hg⟩
  -- Use closure_induction
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact g₁_preserves_B₀
    · exact g₂_preserves_B₀
    · exact g₃_preserves_B₀
  | one => exact one_preserves_B₀
  | mul x y _ _ hx hy => exact mul_preserves_B₀ x y hx hy
  | inv x _ hx => exact inv_preserves_B₀ x hx

/-- The group H₆ is isomorphic to S₄ -/
theorem H₆_iso_S4 : Nonempty (H₆ ≃* Equiv.Perm (Fin 4)) := by
  sorry  -- TODO: Phase 2 - structural proof via first isomorphism theorem

/-- H₆ is finite with cardinality 24 -/
noncomputable instance : Fintype H₆ :=
  -- H₆ is a subgroup of the finite group Perm(Fin 6), so it's finite
  -- We use classical logic to decide membership
  @Subgroup.instFintypeSubtypeMemOfDecidablePred _ _ H₆
    (Classical.decPred _) inferInstance

/-- H₆ has cardinality 24 (as a subgroup) -/
theorem H₆_card_eq_24 : Fintype.card H₆ = 24 := by
  sorry  -- TODO: Phase 2 - follows from isomorphism with S₄

end AfTests.BaseCase
