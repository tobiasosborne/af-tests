/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Formally Real Jordan Algebras

A Jordan algebra is formally real if sums of squares are only zero when each
summand is zero. This is equivalent to: a² = 0 implies a = 0.

## Main definitions

* `FormallyRealJordan J` - A Jordan algebra where `Σ aᵢ² = 0 ⟹ ∀i, aᵢ = 0`

## Main results

* `FormallyRealJordan.sq_eq_zero_imp_zero` - The single element characterization
* `formally_real_of_sq_eq_zero` - Constructor from single element property
-/

open Finset BigOperators

/-- A Jordan algebra is formally real if sums of squares vanish only when all
summands vanish. -/
class FormallyRealJordan (J : Type*) [JordanAlgebra J] : Prop where
  /-- If a sum of squares is zero, each term is zero. -/
  sum_sq_eq_zero : ∀ (n : ℕ) (a : Fin n → J),
    (∑ i, JordanAlgebra.jsq (a i)) = 0 → ∀ i, a i = 0

namespace FormallyRealJordan

variable {J : Type*} [JordanAlgebra J]

/-- In a formally real Jordan algebra, a² = 0 implies a = 0. -/
theorem sq_eq_zero_imp_zero [FormallyRealJordan J] {a : J}
    (h : JordanAlgebra.jsq a = 0) : a = 0 := by
  have := sum_sq_eq_zero 1 (fun _ => a)
  simp only [Fin.sum_univ_one] at this
  exact this h 0

/-- Constructor for FormallyRealJordan from the single element property.

**Mathematical Note:** This direction of the equivalence (single-element property implies
sum-of-squares property) is classically true but requires that squares form a *proper cone*
(salient: if x and -x are both sums of squares, then x = 0). In abstract Jordan algebras
over ℝ, this follows from spectral theory or the Koecher-Vinberg theorem.

**Implementation Note:** The proof requires showing that in a Jordan algebra where
`a² = 0 → a = 0`, the sum of squares forms a salient cone. This is circular with
`positiveCone_salient` in `OrderedCone.lean` which uses `sum_sq_eq_zero`.

For concrete Jordan algebras (Hermitian matrices, spin factors), both properties can be
verified directly. For the abstract case, this sorry represents a gap that requires either:
1. Additional axioms (explicit ordering), or
2. Spectral theory for Jordan algebras

See: Faraut-Korányi "Analysis on Symmetric Cones" for the classical theory. -/
theorem of_sq_eq_zero (h : ∀ a : J, JordanAlgebra.jsq a = 0 → a = 0) :
    FormallyRealJordan J where
  sum_sq_eq_zero n a hsum := by
    induction n with
    | zero => intro i; exact Fin.elim0 i
    | succ n ih =>
      rw [Fin.sum_univ_succ] at hsum
      intro i
      refine Fin.lastCases ?_ ?_ i
      · -- Case: i = Fin.last n
        -- Requires: jsq (a (Fin.last n)) = 0 from sum = 0
        -- This needs the cone to be salient (no cancellation of positive elements)
        sorry
      · -- Case: i = Fin.castSucc j
        intro j
        -- Requires: truncated sum = 0, then apply IH
        -- Also needs salience of the cone
        sorry

end FormallyRealJordan

/-- A Jordan algebra is formally real iff a² = 0 implies a = 0. -/
theorem formallyReal_iff_sq_eq_zero_imp_zero {J : Type*} [JordanAlgebra J] :
    FormallyRealJordan J ↔ ∀ a : J, JordanAlgebra.jsq a = 0 → a = 0 := by
  constructor
  · intro h a ha
    exact FormallyRealJordan.sq_eq_zero_imp_zero ha
  · exact FormallyRealJordan.of_sq_eq_zero

/-- Alternative class: the simpler characterization.

**Note:** This class is primarily for documentation. Concrete Jordan algebras
(Hermitian matrices, spin factors, etc.) should prove `FormallyRealJordan` directly
by showing that sums of squares are non-negative in some ordered structure.
The instance `FormallyRealJordan' → FormallyRealJordan` uses sorries and should
not be relied upon for proofs. -/
class FormallyRealJordan' (J : Type*) [JordanAlgebra J] : Prop where
  sq_eq_zero_imp_zero : ∀ a : J, JordanAlgebra.jsq a = 0 → a = 0

/-!
## REMOVED: FormallyRealJordan' → FormallyRealJordan instance

The instance `FormallyRealJordan' → FormallyRealJordan` was removed because
it used sorries in `of_sq_eq_zero` and could contaminate downstream proofs.

Concrete types (HermitianMatrix, SpinFactor, QuaternionHermitianMatrix) define
`FormallyRealJordan` directly by proving sums of squares are non-negative in an ordered
structure. See `Matrix/FormallyReal.lean`, `SpinFactor/FormallyReal.lean`, etc.
-/
