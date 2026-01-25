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
  -- Use isPositive_def': need IsSelfAdjoint and nonneg reApplyInnerSelf
  rw [ContinuousLinearMap.isPositive_def']
  refine ⟨hA.map π.toStarAlgHom, ?_⟩
  -- For any x, reApplyInnerSelf x = Re⟨π(A)x, x⟩ ≥ 0
  intro x
  by_cases hx : x = 0
  · simp [hx, ContinuousLinearMap.reApplyInnerSelf_apply]
  · -- For nonzero x, normalize to unit vector
    set u := (‖x‖⁻¹ : ℂ) • x with hu_def
    have hx_norm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hu_norm : ‖u‖ = 1 := norm_smul_inv_norm hx
    -- Vector state from unit vector is M-positive: φ(A) = Re⟨u, π(A)u⟩ ≥ 0
    have hφ := hA_states (vectorState π u hu_norm)
    change 0 ≤ (⟪u, π.apply A u⟫_ℂ).re at hφ
    -- π(A) is self-adjoint: adjoint = self
    have hπA_sa : ContinuousLinearMap.adjoint (π A) = π A := by
      rw [← ContinuousLinearMap.isSelfAdjoint_iff']
      exact hA.map π.toStarAlgHom
    -- reApplyInnerSelf x = Re⟨π(A)x, x⟩
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    simp only [RCLike.re_eq_complex_re]
    -- For self-adjoint: Re⟨Tx,x⟩ = Re⟨x,Tx⟩
    have hsym : (⟪(π A) x, x⟫_ℂ).re = (⟪x, (π A) x⟫_ℂ).re := by
      rw [← ContinuousLinearMap.adjoint_inner_left (π A) x x, hπA_sa]
    rw [hsym]
    -- x = ‖x‖ • u, so scale the inner product
    have hx_eq : x = (‖x‖ : ℂ) • u := by
      rw [hu_def, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hx_norm), one_smul]
    rw [hx_eq]
    -- Expand ⟨‖x‖•u, π(A)(‖x‖•u)⟩
    simp only [inner_smul_left, map_smul, inner_smul_right]
    simp only [Complex.conj_ofReal]
    -- Re(‖x‖ * ‖x‖ * ⟨u, π(A)u⟩) = ‖x‖² * Re⟨u, π(A)u⟩
    have hmul : (↑‖x‖ * (↑‖x‖ * ⟪u, (π A) u⟫_ℂ)).re = ‖x‖^2 * (⟪u, (π A) u⟫_ℂ).re := by
      rw [← mul_assoc, ← sq]
      -- (↑‖x‖^2).re = ‖x‖^2 and (↑‖x‖^2).im = 0
      simp only [Complex.mul_re]
      have hcast : (↑‖x‖ : ℂ)^2 = (‖x‖^2 : ℝ) := by norm_cast
      have hre : (↑‖x‖ ^ 2 : ℂ).re = ‖x‖^2 := by rw [hcast]; exact Complex.ofReal_re _
      have him : (↑‖x‖ ^ 2 : ℂ).im = 0 := by rw [hcast]; exact Complex.ofReal_im _
      rw [hre, him, zero_mul, sub_zero]
    rw [hmul]
    exact mul_nonneg (sq_nonneg _) hφ

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
