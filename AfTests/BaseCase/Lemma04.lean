/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Core
import AfTests.BaseCase.Lemma03
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Lemma 4: Base Case Exclusion (H₆ ≠ A₆, S₆)

We prove |H₆| = 24 < 360 = |A₆|, hence H₆ is not equal to A₆ or S₆.

## Main Results

* `H₆_ne_alternatingGroup` - H₆ ≠ A₆
* `H₆_ne_Perm` - H₆ ≠ S₆
* `H₆_card_lt_A6_card` - |H₆| < |A₆|
* `H₆_card_lt_S6_card` - |H₆| < |S₆|

## Proof Strategy

1. By Lemma 3, H₆ ≅ S₄, hence |H₆| = 24.
2. |A₆| = 6!/2 = 360 and |S₆| = 6! = 720.
3. Since 24 < 360 < 720, H₆ ≠ A₆ and H₆ ≠ S₆.

## Reference

See `examples/lemmas/lemma04_base_case_exclusion.md` for the natural language proof.
-/

namespace AfTests.BaseCase

open Equiv Equiv.Perm

/-- 6! = 720 -/
theorem factorial_6 : Nat.factorial 6 = 720 := by native_decide

/-- |S₆| = 720 -/
theorem S6_card : Fintype.card (Equiv.Perm (Fin 6)) = 720 := by
  rw [Fintype.card_perm, Fintype.card_fin]
  native_decide

/-- |A₆| = 360 -/
theorem A6_card : Fintype.card (alternatingGroup (Fin 6)) = 360 := by
  rw [card_alternatingGroup, Fintype.card_fin]
  native_decide

/-- |H₆| = 24 < 360 = |A₆| -/
theorem H₆_card_lt_A6_card : Fintype.card H₆ < Fintype.card (alternatingGroup (Fin 6)) := by
  rw [H₆_card_eq_24, A6_card]
  native_decide

/-- |H₆| = 24 < 720 = |S₆| -/
theorem H₆_card_lt_S6_card : Fintype.card H₆ < Fintype.card (Equiv.Perm (Fin 6)) := by
  rw [H₆_card_eq_24, S6_card]
  native_decide

/-- H₆ ≠ A₆ (as subgroups): cardinalities differ -/
theorem H₆_ne_alternatingGroup : H₆ ≠ alternatingGroup (Fin 6) := by
  sorry  -- TODO: Phase 2 - follows from cardinality comparison

/-- H₆ ≠ S₆ (trivially, since H₆ is a proper subgroup): cardinalities differ -/
theorem H₆_ne_Perm : H₆ ≠ ⊤ := by
  sorry  -- TODO: Phase 2 - follows from cardinality comparison

/-- Main result: H₆ is neither A₆ nor S₆ -/
theorem H₆_proper_subgroup : H₆ ≠ alternatingGroup (Fin 6) ∧ H₆ ≠ ⊤ :=
  ⟨H₆_ne_alternatingGroup, H₆_ne_Perm⟩

end AfTests.BaseCase
