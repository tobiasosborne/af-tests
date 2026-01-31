/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Simple

/-!
# Semisimple Jordan Algebras

A Jordan algebra is semisimple if it is a direct sum of simple ideals.

## Main definitions

* `JordanIdeal.idealSum` - Sum of two ideals
* `JordanIdeal.idealInf` - Intersection of two ideals
* `IsSemisimpleJordan J` - Typeclass asserting J is a semisimple Jordan algebra

## Main results

* `IsSimpleJordan.isSemisimpleJordan` - Simple algebras are semisimple
* `IsSemisimpleJordan.ideal_has_complement` - Every ideal has a complement in semisimple algebras
-/

open JordanAlgebra

namespace JordanIdeal

variable {J : Type*} [JordanAlgebra J]

/-! ### Ideal Operations -/

/-- The sum of two ideals. -/
def idealSum (I K : JordanIdeal J) : JordanIdeal J where
  carrier := {x | ∃ a ∈ I, ∃ b ∈ K, x = a + b}
  add_mem' := fun {x y} hx hy => by
    obtain ⟨a₁, ha₁, b₁, hb₁, heq₁⟩ := hx
    obtain ⟨a₂, ha₂, b₂, hb₂, heq₂⟩ := hy
    refine ⟨a₁ + a₂, I.add_mem ha₁ ha₂, b₁ + b₂, K.add_mem hb₁ hb₂, ?_⟩
    rw [heq₁, heq₂]
    abel
  zero_mem' := ⟨0, I.zero_mem, 0, K.zero_mem, (add_zero 0).symm⟩
  smul_mem' := fun r {x} hx => by
    obtain ⟨a, ha, b, hb, heq⟩ := hx
    refine ⟨r • a, I.smul_mem r ha, r • b, K.smul_mem r hb, ?_⟩
    rw [heq, smul_add]
  neg_mem' := fun {x} hx => by
    obtain ⟨a, ha, b, hb, heq⟩ := hx
    refine ⟨-a, I.neg_mem ha, -b, K.neg_mem hb, ?_⟩
    rw [heq, neg_add]
  jmul_mem' := fun y {x} hx => by
    obtain ⟨a, ha, b, hb, heq⟩ := hx
    refine ⟨jmul y a, I.jmul_mem y ha, jmul y b, K.jmul_mem y hb, ?_⟩
    rw [heq, jmul_add]

theorem mem_idealSum {I K : JordanIdeal J} {x : J} :
    x ∈ idealSum I K ↔ ∃ a ∈ I, ∃ b ∈ K, x = a + b := Iff.rfl

theorem le_idealSum_left (I K : JordanIdeal J) : I ≤ idealSum I K := fun a ha =>
  ⟨a, ha, 0, K.zero_mem, (add_zero a).symm⟩

theorem le_idealSum_right (I K : JordanIdeal J) : K ≤ idealSum I K := fun b hb =>
  ⟨0, I.zero_mem, b, hb, (zero_add b).symm⟩

/-- The intersection of two ideals. -/
def idealInf (I K : JordanIdeal J) : JordanIdeal J where
  carrier := I.carrier ∩ K.carrier
  add_mem' := fun {_ _} ⟨haI, haK⟩ ⟨hbI, hbK⟩ => ⟨I.add_mem haI hbI, K.add_mem haK hbK⟩
  zero_mem' := ⟨I.zero_mem, K.zero_mem⟩
  smul_mem' := fun r {_} ⟨haI, haK⟩ => ⟨I.smul_mem r haI, K.smul_mem r haK⟩
  neg_mem' := fun {_} ⟨haI, haK⟩ => ⟨I.neg_mem haI, K.neg_mem haK⟩
  jmul_mem' := fun a {_} ⟨hbI, hbK⟩ => ⟨I.jmul_mem a hbI, K.jmul_mem a hbK⟩

theorem mem_idealInf {I K : JordanIdeal J} {x : J} :
    x ∈ idealInf I K ↔ x ∈ I ∧ x ∈ K := Iff.rfl

theorem idealInf_le_left (I K : JordanIdeal J) : idealInf I K ≤ I := fun _ ⟨h, _⟩ => h

theorem idealInf_le_right (I K : JordanIdeal J) : idealInf I K ≤ K := fun _ ⟨_, h⟩ => h

/-- Two ideals are independent if their intersection is zero. -/
def Independent (I K : JordanIdeal J) : Prop := idealInf I K = ⊥

theorem independent_iff {I K : JordanIdeal J} :
    Independent I K ↔ ∀ x, x ∈ I → x ∈ K → x = 0 := by
  simp only [Independent, SetLike.ext_iff, mem_idealInf, mem_bot]
  constructor
  · intro h x hI hK
    exact (h x).mp ⟨hI, hK⟩
  · intro h x
    constructor
    · exact fun ⟨hI, hK⟩ => h x hI hK
    · intro hx
      rw [hx]
      exact ⟨I.zero_mem, K.zero_mem⟩

/-- Two ideals form a direct sum decomposition if they are independent and span J. -/
def IsDirectSum (I K : JordanIdeal J) : Prop :=
  Independent I K ∧ idealSum I K = ⊤

theorem isDirectSum_iff {I K : JordanIdeal J} :
    IsDirectSum I K ↔ (∀ x, x ∈ I → x ∈ K → x = 0) ∧ (∀ y : J, ∃ a ∈ I, ∃ b ∈ K, y = a + b) := by
  rw [IsDirectSum, independent_iff]
  simp only [SetLike.ext_iff, mem_idealSum, mem_top, iff_true]

end JordanIdeal

/-- A Jordan algebra is semisimple if every ideal has a complementary ideal. -/
class IsSemisimpleJordan (J : Type*) [JordanAlgebra J] : Prop where
  /-- The algebra is nontrivial. -/
  nontrivial : ∃ a : J, a ≠ 0
  /-- Every ideal has a complement. -/
  ideal_has_complement : ∀ I : JordanIdeal J, ∃ K : JordanIdeal J, JordanIdeal.IsDirectSum I K

namespace IsSemisimpleJordan

variable {J : Type*} [JordanAlgebra J] [IsSemisimpleJordan J]

/-- Semisimple Jordan algebras are nontrivial. -/
instance : Nontrivial J := by
  obtain ⟨a, ha⟩ := IsSemisimpleJordan.nontrivial (J := J)
  exact ⟨⟨a, 0, ha⟩⟩

/-- In a semisimple Jordan algebra, the identity is nonzero. -/
theorem jone_ne_zero : (jone : J) ≠ 0 := by
  intro h
  obtain ⟨a, ha⟩ := IsSemisimpleJordan.nontrivial (J := J)
  apply ha
  calc a = jmul a jone := (jmul_jone a).symm
    _ = jmul a 0 := by rw [h]
    _ = 0 := jmul_zero a

end IsSemisimpleJordan

/-- Simple Jordan algebras are semisimple. -/
instance IsSimpleJordan.isSemisimpleJordan {J : Type*} [JordanAlgebra J] [IsSimpleJordan J] :
    IsSemisimpleJordan J where
  nontrivial := IsSimpleJordan.nontrivial
  ideal_has_complement := fun I => by
    rcases IsSimpleJordan.ideal_eq_bot_or_top I with hbot | htop
    -- Case I = ⊥: complement is ⊤
    · use ⊤
      constructor
      · rw [hbot, JordanIdeal.independent_iff]
        intro x hx _
        simp only [JordanIdeal.mem_bot] at hx
        exact hx
      · rw [hbot]
        apply SetLike.ext
        intro x
        simp only [JordanIdeal.mem_idealSum, JordanIdeal.mem_bot, JordanIdeal.mem_top, iff_true]
        exact ⟨0, rfl, x, trivial, (zero_add x).symm⟩
    -- Case I = ⊤: complement is ⊥
    · use ⊥
      constructor
      · rw [htop, JordanIdeal.independent_iff]
        intro x _ hx
        simp only [JordanIdeal.mem_bot] at hx
        exact hx
      · rw [htop]
        apply SetLike.ext
        intro x
        simp only [JordanIdeal.mem_idealSum, JordanIdeal.mem_top, JordanIdeal.mem_bot, iff_true]
        exact ⟨x, trivial, 0, rfl, (add_zero x).symm⟩

/-- Constructor for semisimple algebras from the complement property. -/
theorem IsSemisimpleJordan.mk' {J : Type*} [JordanAlgebra J] [Nontrivial J]
    (h : ∀ I : JordanIdeal J, ∃ K : JordanIdeal J, JordanIdeal.IsDirectSum I K) :
    IsSemisimpleJordan J where
  nontrivial := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne J
    by_cases ha : a = 0
    · exact ⟨b, fun hb => hab (ha.symm ▸ hb.symm)⟩
    · exact ⟨a, ha⟩
  ideal_has_complement := h
