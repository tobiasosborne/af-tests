/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Basic
import Mathlib.Data.SetLike.Basic

/-!
# Jordan Subalgebras

This file defines Jordan subalgebras as subsets closed under the Jordan product.

## Main definitions

* `JordanSubalgebra J` - A subalgebra of a Jordan algebra
* `SetLike` instance for `JordanSubalgebra`
-/

/-- A Jordan subalgebra of `J`. -/
structure JordanSubalgebra (J : Type*) [JordanAlgebra J] where
  carrier : Set J
  jone_mem' : JordanAlgebra.jone ∈ carrier
  jmul_mem' : ∀ ⦃a b⦄, a ∈ carrier → b ∈ carrier → JordanAlgebra.jmul a b ∈ carrier
  add_mem' : ∀ ⦃a b⦄, a ∈ carrier → b ∈ carrier → a + b ∈ carrier
  smul_mem' : ∀ (r : ℝ) ⦃a⦄, a ∈ carrier → r • a ∈ carrier
  neg_mem' : ∀ ⦃a⦄, a ∈ carrier → -a ∈ carrier

namespace JordanSubalgebra

variable {J : Type*} [JordanAlgebra J]

instance : SetLike (JordanSubalgebra J) J where
  coe S := S.carrier
  coe_injective' p q h := by cases p; cases q; congr

@[simp]
theorem mem_carrier {S : JordanSubalgebra J} {x : J} : x ∈ S.carrier ↔ x ∈ S := Iff.rfl

theorem jone_mem (S : JordanSubalgebra J) : JordanAlgebra.jone ∈ S := S.jone_mem'

theorem jmul_mem (S : JordanSubalgebra J) {a b : J} (ha : a ∈ S) (hb : b ∈ S) :
    JordanAlgebra.jmul a b ∈ S := S.jmul_mem' ha hb

theorem add_mem (S : JordanSubalgebra J) {a b : J} (ha : a ∈ S) (hb : b ∈ S) :
    a + b ∈ S := S.add_mem' ha hb

theorem smul_mem (S : JordanSubalgebra J) (r : ℝ) {a : J} (ha : a ∈ S) :
    r • a ∈ S := S.smul_mem' r ha

theorem neg_mem (S : JordanSubalgebra J) {a : J} (ha : a ∈ S) :
    -a ∈ S := S.neg_mem' ha

theorem zero_mem (S : JordanSubalgebra J) : (0 : J) ∈ S := by
  have h := S.smul_mem 0 (S.jone_mem)
  simp at h
  exact h

theorem sub_mem (S : JordanSubalgebra J) {a b : J} (ha : a ∈ S) (hb : b ∈ S) :
    a - b ∈ S := by
  rw [sub_eq_add_neg]
  exact S.add_mem ha (S.neg_mem hb)

/-- The subalgebra as an AddSubgroup. -/
def toAddSubgroup (S : JordanSubalgebra J) : AddSubgroup J where
  carrier := S.carrier
  add_mem' := fun ha hb => S.add_mem' ha hb
  zero_mem' := S.zero_mem
  neg_mem' := fun ha => S.neg_mem' ha

/-- The subalgebra as a Submodule. -/
def toSubmodule (S : JordanSubalgebra J) : Submodule ℝ J where
  carrier := S.carrier
  add_mem' := fun ha hb => S.add_mem' ha hb
  zero_mem' := S.zero_mem
  smul_mem' := fun r _ ha => S.smul_mem' r ha

end JordanSubalgebra
