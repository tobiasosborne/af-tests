/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Core
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Lemma 5: Transitivity of H on Omega

The group H = ⟨g₁, g₂, g₃⟩ acts transitively on Ω = Fin(6+n+k+m).

## Main Results

* `H_isPretransitive` - H acts transitively on Omega

## Proof Strategy

The proof proceeds by showing the support graph Γ is connected:
1. Identify edges from each generator (consecutive elements in cycles)
2. Show the Core {0,1,2,3,4,5} forms a connected subgraph
3. Show each tail vertex connects to the Core
4. Conclude Γ is connected, hence H acts transitively

## Reference

See `examples/lemmas/lemma05_transitivity.md` for the natural language proof.
-/

namespace AfTests.Transitivity

open Equiv.Perm

/-! ### Base Case: n = k = m = 0

For the base case, H₆ acts transitively on Fin 6.
-/

/-- In the base case, every element of Fin 6 is in the orbit of 0 under H₆.
    This implies transitivity. -/
theorem H₆_orbit_of_zero : ∀ x : Fin 6, ∃ h : H₆, h.val x = 0 := by
  sorry

/-- The base case group H₆ acts transitively on Fin 6 -/
theorem H₆_isPretransitive : MulAction.IsPretransitive H₆ (Fin 6) := by
  sorry

/-! ### General Case

For the general case with arbitrary n, k, m, we use the support graph argument.
The support graph has vertices = Omega and edges = {(x, g(x)) : g generator, x moved}.
-/

/-- The Core vertices {0,1,2,3,4,5} are connected in the support graph -/
theorem core_connected (n k m : ℕ) :
    ∀ x y : Fin 6, ∃ h : H n k m, (h.val (Fin.castLE (by omega : 6 ≤ 6 + n + k + m) x) =
      Fin.castLE (by omega : 6 ≤ 6 + n + k + m) y) := by
  sorry

/-- Each tail vertex in the a-tail (from g₁) connects to the Core -/
theorem a_tail_connected_to_core (n k m : ℕ) (i : Fin n) :
    ∃ h : H n k m, (h.val ⟨6 + i.val, by omega⟩ : Omega n k m).val < 6 := by
  sorry

/-- Each tail vertex in the b-tail (from g₂) connects to the Core -/
theorem b_tail_connected_to_core (n k m : ℕ) (j : Fin k) :
    ∃ h : H n k m, (h.val ⟨6 + n + j.val, by omega⟩ : Omega n k m).val < 6 := by
  sorry

/-- Each tail vertex in the c-tail (from g₃) connects to the Core -/
theorem c_tail_connected_to_core (n k m : ℕ) (l : Fin m) :
    ∃ h : H n k m, (h.val ⟨6 + n + k + l.val, by omega⟩ : Omega n k m).val < 6 := by
  sorry

/-- The group H acts transitively on Omega -/
theorem H_isPretransitive (n k m : ℕ) : MulAction.IsPretransitive (H n k m) (Omega n k m) := by
  sorry

/-! ### Orbit Equivalence

Alternative formulation using orbits.
-/

/-- There is only one orbit under the action of H -/
theorem H_single_orbit (n k m : ℕ) :
    ∀ x y : Omega n k m, ∃ h : H n k m, h.val x = y := by
  sorry

end AfTests.Transitivity
