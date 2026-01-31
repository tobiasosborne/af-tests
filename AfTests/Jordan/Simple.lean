/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Ideal

/-!
# Simple Jordan Algebras

A Jordan algebra is simple if it has no proper nontrivial ideals.

## Main definitions

* `IsSimpleJordan J` - Typeclass asserting J is a simple Jordan algebra

## Main results

* `IsSimpleJordan.ideal_eq_bot_or_top` - Every ideal is trivial
* `IsSimpleJordan.nontrivial` - Simple algebras are nontrivial
-/

open JordanAlgebra

/-- A Jordan algebra is simple if it is nontrivial and has no proper nontrivial ideals. -/
class IsSimpleJordan (J : Type*) [JordanAlgebra J] : Prop where
  /-- The algebra is nontrivial. -/
  nontrivial : ∃ a : J, a ≠ 0
  /-- Every ideal is either zero or the whole algebra. -/
  ideal_eq_bot_or_top : ∀ I : JordanIdeal J, I = ⊥ ∨ I = ⊤

namespace IsSimpleJordan

variable {J : Type*} [JordanAlgebra J] [IsSimpleJordan J]

/-- Simple Jordan algebras are nontrivial. -/
instance : Nontrivial J := by
  obtain ⟨a, ha⟩ := IsSimpleJordan.nontrivial (J := J)
  exact ⟨⟨a, 0, ha⟩⟩

/-- In a simple Jordan algebra, the identity is nonzero. -/
theorem jone_ne_zero : (jone : J) ≠ 0 := by
  intro h
  obtain ⟨a, ha⟩ := IsSimpleJordan.nontrivial (J := J)
  apply ha
  calc a = jmul a jone := (jmul_jone a).symm
    _ = jmul a 0 := by rw [h]
    _ = 0 := jmul_zero a

/-- In a simple Jordan algebra, every nonzero ideal is the whole algebra. -/
theorem ideal_eq_top_of_ne_bot {I : JordanIdeal J} (h : I ≠ ⊥) : I = ⊤ :=
  (ideal_eq_bot_or_top I).resolve_left h

/-- In a simple Jordan algebra, an ideal containing a nonzero element is the whole algebra. -/
theorem ideal_eq_top_of_mem_ne_zero {I : JordanIdeal J} {a : J} (ha : a ∈ I) (hne : a ≠ 0) :
    I = ⊤ := by
  apply ideal_eq_top_of_ne_bot
  intro heq
  rw [heq] at ha
  simp only [JordanIdeal.mem_bot] at ha
  exact hne ha

/-- The identity element generates the whole algebra. -/
theorem ideal_of_one_eq_top (I : JordanIdeal J) (h : jone ∈ I) : I = ⊤ := by
  apply ideal_eq_top_of_mem_ne_zero h
  exact jone_ne_zero

end IsSimpleJordan

/-- Constructor for simple Jordan algebras from the ideal property alone (when nontrivial). -/
theorem IsSimpleJordan.mk' {J : Type*} [JordanAlgebra J] [Nontrivial J]
    (h : ∀ I : JordanIdeal J, I = ⊥ ∨ I = ⊤) : IsSimpleJordan J where
  nontrivial := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne J
    by_cases ha : a = 0
    · exact ⟨b, fun hb => hab (ha.symm ▸ hb.symm)⟩
    · exact ⟨a, ha⟩
  ideal_eq_bot_or_top := h

/-- A Jordan algebra with no proper nontrivial ideals and containing a nonzero element
is simple. This is useful for proving simplicity of concrete algebras. -/
theorem isSimpleJordan_of_ideal_trichotomy {J : Type*} [JordanAlgebra J]
    (hne : ∃ a : J, a ≠ 0)
    (h : ∀ I : JordanIdeal J, I = ⊥ ∨ I = ⊤) : IsSimpleJordan J where
  nontrivial := hne
  ideal_eq_bot_or_top := h
