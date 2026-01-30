/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Primitive
import AfTests.Jordan.Product

/-!
# Peirce Decomposition for Jordan Algebras

For an idempotent e in a Jordan algebra, the left multiplication operator L_e satisfies
L_e(L_e - 1/2)(L_e - 1) = 0, giving eigenspaces P₀(e), P_{1/2}(e), P₁(e).

## Main definitions

* `PeirceSpace e ev` - The ev-eigenspace of L_e
* `PeirceSpace₀`, `PeirceSpace₁₂`, `PeirceSpace₁` - The three Peirce spaces

## Main results

* `peirceSpace_disjoint` - Distinct Peirce spaces are disjoint
* `idempotent_in_peirce_one` - e ∈ P₁(e)
-/

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-! ### Peirce Space Definition -/

/-- The Peirce ev-eigenspace for idempotent e: {a | e ∘ a = ev • a}. -/
def PeirceSpace (e : J) (ev : ℝ) : Submodule ℝ J where
  carrier := {a | jmul e a = ev • a}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [jmul_add, ha, hb, smul_add]
  zero_mem' := by simp [jmul_zero, smul_zero]
  smul_mem' := fun r a ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [smul_jmul, ha, smul_comm]

theorem mem_peirceSpace_iff (e : J) (ev : ℝ) (a : J) :
    a ∈ PeirceSpace e ev ↔ jmul e a = ev • a := Iff.rfl

/-- Notation for common Peirce spaces. -/
abbrev PeirceSpace₀ (e : J) := PeirceSpace e 0
noncomputable abbrev PeirceSpace₁₂ (e : J) := PeirceSpace e (1/2)
abbrev PeirceSpace₁ (e : J) := PeirceSpace e 1

/-! ### Basic Peirce Space Properties -/

theorem peirceSpace_zero_eq_ker (e : J) :
    (PeirceSpace e 0 : Set J) = (LinearMap.ker (L e) : Set J) := by
  ext a
  simp only [SetLike.mem_coe, mem_peirceSpace_iff, LinearMap.mem_ker, L_apply, zero_smul]

theorem idempotent_in_peirce_one {e : J} (he : IsIdempotent e) :
    e ∈ PeirceSpace e 1 := by
  rw [mem_peirceSpace_iff, one_smul]
  exact he

theorem orthogonal_in_peirce_zero {e f : J} (horth : AreOrthogonal e f) :
    f ∈ PeirceSpace e 0 := by
  rw [mem_peirceSpace_iff, zero_smul]
  exact horth

/-- Peirce spaces for distinct eigenvalues are disjoint. -/
theorem peirceSpace_disjoint (e : J) {ev1 ev2 : ℝ} (hne : ev1 ≠ ev2) :
    Disjoint (PeirceSpace e ev1) (PeirceSpace e ev2) := by
  rw [Submodule.disjoint_def]
  intro a ha hb
  rw [mem_peirceSpace_iff] at ha hb
  have heq : ev1 • a = ev2 • a := ha.symm.trans hb
  have hdiff : (ev1 - ev2) • a = 0 := by
    rw [sub_smul, heq, sub_self]
  rcases eq_or_ne a 0 with rfl | hane
  · rfl
  · -- If a ≠ 0 but (ev1 - ev2) • a = 0, then ev1 - ev2 = 0
    -- Since ℝ is a field and modules over fields have no zero divisors
    have hsub : ev1 - ev2 ≠ 0 := sub_ne_zero.mpr hne
    -- (ev1 - ev2)⁻¹ • (ev1 - ev2) • a = (ev1 - ev2)⁻¹ • 0
    have h : a = (ev1 - ev2)⁻¹ • ((ev1 - ev2) • a) := by
      rw [smul_smul, inv_mul_cancel₀ hsub, one_smul]
    rw [hdiff, smul_zero] at h
    exact absurd h hane

/-- The identity is in Peirce space 1 for itself. -/
theorem jone_in_peirce_one : jone ∈ PeirceSpace (jone : J) 1 := by
  rw [mem_peirceSpace_iff, jmul_jone, one_smul]

/-- If e is idempotent, then 1-e is in Peirce space 0 of e. -/
theorem complement_in_peirce_zero {e : J} (he : IsIdempotent e) :
    jone - e ∈ PeirceSpace e 0 := by
  rw [mem_peirceSpace_iff, zero_smul]
  exact jone_sub_idempotent_orthogonal he

end JordanAlgebra
