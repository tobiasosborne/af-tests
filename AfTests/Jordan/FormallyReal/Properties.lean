/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.FormallyReal.Def
import AfTests.Jordan.Subalgebra
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Properties of Formally Real Jordan Algebras

This file establishes basic properties of formally real Jordan algebras.

## Main results

* `FormallyRealJordan.jsq_ne_zero` - a ≠ 0 implies a² ≠ 0
* `FormallyRealJordan.smul_jone_ne_zero'` - n • 1 ≠ 0 for positive n (when 1 ≠ 0)
* `FormallyRealJordan.jpow_two_eq_zero` - a² = 0 implies a = 0 (no nilpotents)
-/

namespace FormallyRealJordan

variable {J : Type*} [JordanAlgebra J] [FormallyRealJordan J]

/-! ### Characteristic Zero Property -/

/-- In a formally real Jordan algebra, a ≠ 0 implies a² ≠ 0. -/
theorem jsq_ne_zero {a : J} (ha : a ≠ 0) : JordanAlgebra.jsq a ≠ 0 := fun h =>
  ha (sq_eq_zero_imp_zero h)

/-- Contrapositive: a² = 0 implies a = 0. -/
theorem jsq_eq_zero_iff {a : J} : JordanAlgebra.jsq a = 0 ↔ a = 0 :=
  ⟨sq_eq_zero_imp_zero, fun h => by rw [h, JordanAlgebra.jsq_def, JordanAlgebra.jmul_zero]⟩

omit [FormallyRealJordan J] in
/-- If the identity is nonzero, then n • 1 ≠ 0 for positive n.
This is the Jordan algebra analog of characteristic zero. -/
theorem smul_jone_ne_zero' (hone : JordanAlgebra.jone ≠ (0 : J)) {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) • JordanAlgebra.jone ≠ (0 : J) := by
  intro h
  have hsq : JordanAlgebra.jsq ((n : ℝ) • (JordanAlgebra.jone : J)) =
      ((n : ℝ)^2) • (JordanAlgebra.jone : J) := by
    unfold JordanAlgebra.jsq
    rw [JordanAlgebra.jmul_smul, JordanAlgebra.smul_jmul, JordanAlgebra.jmul_jone,
      smul_smul, sq]
  have h2 : JordanAlgebra.jsq ((n : ℝ) • (JordanAlgebra.jone : J)) = 0 := by
    rw [h, JordanAlgebra.jsq_def, JordanAlgebra.jmul_zero]
  rw [hsq] at h2
  have hn2 : ((n : ℕ) : ℝ)^2 ≠ 0 := by
    have : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    positivity
  have : (JordanAlgebra.jone : J) = 0 := by
    have := congr_arg ((n : ℝ)⁻¹ ^ 2 • ·) h2
    simp only [smul_zero] at this
    rw [smul_smul] at this
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hinv : (n : ℝ)⁻¹ ^ 2 * (n : ℝ) ^ 2 = 1 := by
      field_simp
    rw [hinv, one_smul] at this
    exact this
  exact hone this

/-! ### No Nilpotent Elements -/

/-- In a formally real Jordan algebra, a² = 0 implies a = 0.
This is the fundamental "no nilpotent elements" property. -/
theorem jpow_two_eq_zero {a : J} (h : JordanAlgebra.jpow a 2 = 0) : a = 0 := by
  have : JordanAlgebra.jpow a 2 = JordanAlgebra.jsq a := JordanAlgebra.jpow_two a
  rw [this] at h
  exact sq_eq_zero_imp_zero h

/-! ### Subalgebra Heredity -/

/-- Elements of a subalgebra satisfy the formally real property.
Note: The full `FormallyRealJordan S` instance requires `JordanAlgebra S`. -/
theorem subalgebra_sq_eq_zero {a : J} (h : JordanAlgebra.jsq a = 0) : a = 0 :=
  sq_eq_zero_imp_zero h

end FormallyRealJordan
