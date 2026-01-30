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
noncomputable abbrev PeirceSpace₁₂ (e : J) := PeirceSpace e (1 / 2)
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

/-! ### Peirce Polynomial Identity -/

/-- For any idempotent e, L_e satisfies L_e(L_e - 1/2)(L_e - 1) = 0.
This fundamental identity shows L_e has eigenvalues only in {0, 1/2, 1}. -/
theorem peirce_polynomial_identity {e : J} (he : IsIdempotent e) :
    (L e) ∘ₗ ((L e) - (1/2 : ℝ) • LinearMap.id) ∘ₗ ((L e) - LinearMap.id) = 0 := by
  -- Expanded: L_e³ - (3/2)L_e² + (1 / 2)L_e = 0
  -- For x: e∘(e∘(e∘x)) = (3/2)e∘(e∘x) - (1 / 2)e∘x
  -- This follows from the Jordan identity via the operator identity.
  ext x
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, L_apply, LinearMap.zero_apply]
  -- Need: jmul e (jmul e (jmul e x) - 1/2 * (jmul e x)) - (jmul e (jmul e x) - 1/2 * x) = 0
  -- Simplify using bilinearity
  rw [jmul_sub, smul_jmul, jmul_sub]
  ring_nf
  -- The identity e∘(e∘(e∘x)) - (3/2)e∘(e∘x) + (1 / 2)e∘x = 0 for idempotent e
  -- follows from the Jordan identity by operator calculus
  sorry

/-! ### Peirce Multiplication Rules -/

/-- Product of two elements in P₀(e) stays in P₀(e). -/
theorem peirce_mult_P0_P0 {e : J} (he : IsIdempotent e) {a b : J}
    (ha : a ∈ PeirceSpace e 0) (hb : b ∈ PeirceSpace e 0) :
    jmul a b ∈ PeirceSpace e 0 := by
  rw [mem_peirceSpace_iff] at ha hb ⊢
  rw [zero_smul] at ha hb ⊢
  -- Need: e ∘ (a ∘ b) = 0 given e ∘ a = 0 and e ∘ b = 0
  -- Use linearized Jordan identity
  sorry

/-- Product of two elements in P₁(e) stays in P₁(e). -/
theorem peirce_mult_P1_P1 {e : J} (he : IsIdempotent e) {a b : J}
    (ha : a ∈ PeirceSpace e 1) (hb : b ∈ PeirceSpace e 1) :
    jmul a b ∈ PeirceSpace e 1 := by
  rw [mem_peirceSpace_iff] at ha hb ⊢
  rw [one_smul] at ha hb ⊢
  -- Need: e ∘ (a ∘ b) = a ∘ b given e ∘ a = a and e ∘ b = b
  sorry

/-- Product of an element in P₀(e) with an element in P₁(e) is zero. -/
theorem peirce_mult_P0_P1 {e : J} (he : IsIdempotent e) {a b : J}
    (ha : a ∈ PeirceSpace e 0) (hb : b ∈ PeirceSpace e 1) :
    jmul a b = 0 := by
  rw [mem_peirceSpace_iff] at ha hb
  rw [zero_smul] at ha
  rw [one_smul] at hb
  -- Need: a ∘ b = 0 given e ∘ a = 0 and e ∘ b = b
  -- This follows from the orthogonal Peirce space property
  sorry

/-- Product of two elements in P_{1/2}(e) lands in P₀(e) ⊕ P₁(e). -/
theorem peirce_mult_P12_P12 {e : J} (he : IsIdempotent e) {a b : J}
    (ha : a ∈ PeirceSpace e (1 / 2)) (hb : b ∈ PeirceSpace e (1 / 2)) :
    jmul a b ∈ PeirceSpace e 0 ⊔ PeirceSpace e 1 := by
  -- The product a ∘ b for a, b ∈ P_{1/2} has no P_{1/2} component
  sorry

/-- Product of an element in P₀(e) with an element in P_{1/2}(e) stays in P_{1/2}(e). -/
theorem peirce_mult_P0_P12 {e : J} (he : IsIdempotent e) {a b : J}
    (ha : a ∈ PeirceSpace e 0) (hb : b ∈ PeirceSpace e (1 / 2)) :
    jmul a b ∈ PeirceSpace e (1 / 2) := by
  rw [mem_peirceSpace_iff] at ha hb ⊢
  rw [zero_smul] at ha
  -- Need: e ∘ (a ∘ b) = (1 / 2)(a ∘ b) given e ∘ a = 0 and e ∘ b = (1 / 2)b
  sorry

/-- Product of an element in P₁(e) with an element in P_{1/2}(e) stays in P_{1/2}(e). -/
theorem peirce_mult_P1_P12 {e : J} (he : IsIdempotent e) {a b : J}
    (ha : a ∈ PeirceSpace e 1) (hb : b ∈ PeirceSpace e (1 / 2)) :
    jmul a b ∈ PeirceSpace e (1 / 2) := by
  rw [mem_peirceSpace_iff] at ha hb ⊢
  rw [one_smul] at ha
  -- Need: e ∘ (a ∘ b) = (1 / 2)(a ∘ b) given e ∘ a = a and e ∘ b = (1 / 2)b
  sorry

end JordanAlgebra
