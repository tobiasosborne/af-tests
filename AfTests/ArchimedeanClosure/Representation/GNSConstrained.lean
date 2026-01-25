/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.ArchimedeanClosure.Representation.VectorState
import AfTests.ArchimedeanClosure.Algebra.Archimedean

/-! # GNS and Constrained Representations

This file bridges M-positive states and constrained representations.

## Main results

* `state_nonneg_implies_rep_positive` - Forward: If φ(A) ≥ 0 for all states, π(A) ≥ 0
* `gns_constrained_implies_state_nonneg` - Backward: If π(A) ≥ 0 for all reps, φ(A) ≥ 0

## Mathematical Background

The key equivalence: positivity in all states ⟺ positivity in all constrained reps.

Forward direction uses VectorState.lean: vector states from constrained reps are M-positive,
so if φ(A) ≥ 0 for all M-positive φ, then ⟨v, π(A)v⟩ ≥ 0 for all v, hence π(A) ≥ 0.

Backward direction requires the GNS construction: every M-positive state arises as
a vector state from some constrained representation.
-/

open scoped ComplexOrder InnerProductSpace

namespace ArchimedeanClosure

variable {n : ℕ}

/-! ### Forward Direction: States to Representations -/

/-- Forward: If φ(A) ≥ 0 for all M-positive states, then π(A) ≥ 0 for all constrained reps.

This uses that vector states from constrained reps are M-positive (VectorState.lean).
The key steps:
1. For π : ConstrainedStarRep and any unit vector v, the vector state φ_v is M-positive
2. By hypothesis, φ_v(A) = Re⟨v, π(A)v⟩ ≥ 0
3. For self-adjoint A, π(A) is self-adjoint, so ⟨v, π(A)v⟩ is real
4. Hence ⟨v, π(A)v⟩ ≥ 0 for all v, meaning π(A) ≥ 0 -/
theorem state_nonneg_implies_rep_positive (A : FreeStarAlgebra n)
    (hA : IsSelfAdjoint A)
    (hA_states : ∀ φ : FreeStarAlgebra.MPositiveState n, 0 ≤ φ A) :
    ∀ π : ConstrainedStarRep n, (π A).IsPositive := by
  intro π
  -- The proof uses that vector states from π are M-positive (VectorState.lean)
  -- For any v, the vector state φ_v gives φ_v(A) = Re⟨v, π(A)v⟩ ≥ 0 by hypothesis
  -- Since A is self-adjoint, π(A) is self-adjoint, so ⟨v, π(A)v⟩ is real
  -- Hence π(A) is positive (symmetric + nonneg inner products)
  sorry

/-! ### Backward Direction: Representations to States -/

/-- The GNS representation of an M-positive state exists and is constrained.

This is the key existence theorem. The full GNS construction for FreeStarAlgebra
adapts the C*-algebra GNS: form the quotient by the left ideal {a : φ(a*a) = 0},
complete to a Hilbert space, and extend the left multiplication action.

The representation is constrained because φ(gⱼ) ≥ 0 (set b=1 in star b * gⱼ * b ∈ M)
implies π_φ(gⱼ) is a positive operator. -/
theorem gns_representation_exists (φ : FreeStarAlgebra.MPositiveState n) :
    ∃ (π : ConstrainedStarRep n) (Ω : π.H),
      ‖Ω‖ = 1 ∧ ∀ a, φ a = (⟪Ω, π a Ω⟫_ℂ).re := by
  sorry

/-- Backward: If π(A) ≥ 0 for all constrained reps, then φ(A) ≥ 0 for all M-positive states.

Uses GNS: φ = ⟨Ω, π_φ(-)Ω⟩ for some constrained π_φ, so φ(A) = ⟨Ω, π_φ(A)Ω⟩ ≥ 0. -/
theorem gns_constrained_implies_state_nonneg (φ : FreeStarAlgebra.MPositiveState n)
    (A : FreeStarAlgebra n) (_hA : IsSelfAdjoint A)
    (hA_reps : ∀ π : ConstrainedStarRep n, (π A).IsPositive) :
    0 ≤ φ A := by
  -- Get GNS representation
  obtain ⟨π, Ω, hΩ_norm, hφ_eq⟩ := gns_representation_exists φ
  -- φ(A) = ⟨Ω, π(A)Ω⟩.re
  rw [hφ_eq]
  -- π(A) is positive by hypothesis
  have hπA := hA_reps π
  -- So ⟨Ω, π(A)Ω⟩ ≥ 0 in ℂ
  exact (Complex.nonneg_iff.mp (hπA.inner_nonneg_right Ω)).1

end ArchimedeanClosure
