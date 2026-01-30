/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Basic
import Mathlib.Data.SetLike.Basic

/-!
# Jordan Ideals

This file defines Jordan ideals as subspaces closed under Jordan multiplication.

## Main definitions

* `JordanIdeal J` - An ideal of a Jordan algebra

## Implementation Notes

A Jordan ideal I satisfies: for all a ∈ J and b ∈ I, we have a ∘ b ∈ I.
By commutativity of the Jordan product, this also gives b ∘ a ∈ I.
-/

/-- A Jordan ideal of `J`. -/
structure JordanIdeal (J : Type*) [JordanAlgebra J] where
  carrier : Set J
  add_mem' : ∀ ⦃a b⦄, a ∈ carrier → b ∈ carrier → a + b ∈ carrier
  zero_mem' : (0 : J) ∈ carrier
  smul_mem' : ∀ (r : ℝ) ⦃a⦄, a ∈ carrier → r • a ∈ carrier
  neg_mem' : ∀ ⦃a⦄, a ∈ carrier → -a ∈ carrier
  jmul_mem' : ∀ (a : J) ⦃b⦄, b ∈ carrier → JordanAlgebra.jmul a b ∈ carrier

namespace JordanIdeal

variable {J : Type*} [JordanAlgebra J]

instance : SetLike (JordanIdeal J) J where
  coe I := I.carrier
  coe_injective' p q h := by cases p; cases q; congr

@[simp]
theorem mem_carrier {I : JordanIdeal J} {x : J} : x ∈ I.carrier ↔ x ∈ I := Iff.rfl

theorem add_mem (I : JordanIdeal J) {a b : J} (ha : a ∈ I) (hb : b ∈ I) :
    a + b ∈ I := I.add_mem' ha hb

theorem zero_mem (I : JordanIdeal J) : (0 : J) ∈ I := I.zero_mem'

theorem smul_mem (I : JordanIdeal J) (r : ℝ) {a : J} (ha : a ∈ I) :
    r • a ∈ I := I.smul_mem' r ha

theorem neg_mem (I : JordanIdeal J) {a : J} (ha : a ∈ I) :
    -a ∈ I := I.neg_mem' ha

theorem jmul_mem (I : JordanIdeal J) (a : J) {b : J} (hb : b ∈ I) :
    JordanAlgebra.jmul a b ∈ I := I.jmul_mem' a hb

theorem jmul_mem_left (I : JordanIdeal J) {a : J} (ha : a ∈ I) (b : J) :
    JordanAlgebra.jmul a b ∈ I := by
  rw [JordanAlgebra.jmul_comm]
  exact I.jmul_mem b ha

theorem sub_mem (I : JordanIdeal J) {a b : J} (ha : a ∈ I) (hb : b ∈ I) :
    a - b ∈ I := by
  rw [sub_eq_add_neg]
  exact I.add_mem ha (I.neg_mem hb)

/-- The ideal as an AddSubgroup. -/
def toAddSubgroup (I : JordanIdeal J) : AddSubgroup J where
  carrier := I.carrier
  add_mem' := fun ha hb => I.add_mem' ha hb
  zero_mem' := I.zero_mem
  neg_mem' := fun ha => I.neg_mem' ha

/-- The ideal as a Submodule. -/
def toSubmodule (I : JordanIdeal J) : Submodule ℝ J where
  carrier := I.carrier
  add_mem' := fun ha hb => I.add_mem' ha hb
  zero_mem' := I.zero_mem
  smul_mem' := fun r _ ha => I.smul_mem' r ha

/-- The zero ideal. -/
instance : Bot (JordanIdeal J) where
  bot := {
    carrier := {0}
    add_mem' := fun ha hb => by simp_all
    zero_mem' := Set.mem_singleton 0
    smul_mem' := fun _ _ ha => by simp_all
    neg_mem' := fun ha => by simp_all
    jmul_mem' := fun _ _ hb => by simp_all [JordanAlgebra.jmul_zero]
  }

/-- The whole algebra as an ideal. -/
instance : Top (JordanIdeal J) where
  top := {
    carrier := Set.univ
    add_mem' := fun {_} {_} _ _ => Set.mem_univ _
    zero_mem' := Set.mem_univ _
    smul_mem' := fun _ {_} _ => Set.mem_univ _
    neg_mem' := fun {_} _ => Set.mem_univ _
    jmul_mem' := fun _ {_} _ => Set.mem_univ _
  }

@[simp]
theorem mem_bot {a : J} : a ∈ (⊥ : JordanIdeal J) ↔ a = 0 := Set.mem_singleton_iff

@[simp]
theorem mem_top {a : J} : a ∈ (⊤ : JordanIdeal J) := Set.mem_univ a

end JordanIdeal
