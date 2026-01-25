/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.ArchimedeanClosure.GNS.Bounded
import AfTests.ArchimedeanClosure.GNS.ComplexifyGNS

/-! # GNS Representation Extension

This file extends the pre-representation from the GNS quotient to the Hilbert space.

## Main definitions

* `MPositiveState.gnsBoundedPreRep` - Pre-representation as ContinuousLinearMap

## Implementation Notes

The quotient A₀/N_φ has two incompatible TopologicalSpace instances:
1. Quotient module topology (from Submodule.Quotient)
2. Seminormed topology (from gnsQuotientNormedAddCommGroup)

We must use explicit @ syntax to select the seminormed topology consistently.
See docs/GNS/learnings/completion-topology.md for details.
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ} [IsArchimedean n] (φ : MPositiveState n)

/-! ### Pre-representation as ContinuousLinearMap -/

/-- The pre-representation as a continuous linear map on the quotient.

Uses explicit @ syntax to resolve the topology diamond. All instances
are derived from gnsQuotientNormedAddCommGroup for consistency. -/
noncomputable def gnsBoundedPreRep (a : FreeStarAlgebra n) :
    @ContinuousLinearMap ℝ ℝ _ _ (RingHom.id ℝ) φ.gnsQuotient
      (@UniformSpace.toTopologicalSpace _ φ.gnsQuotientNormedAddCommGroup.toUniformSpace)
      φ.gnsQuotientNormedAddCommGroup.toAddCommMonoid φ.gnsQuotient
      (@UniformSpace.toTopologicalSpace _ φ.gnsQuotientNormedAddCommGroup.toUniformSpace)
      φ.gnsQuotientNormedAddCommGroup.toAddCommMonoid
      (NormedSpace.toModule (R := ℝ) (M := φ.gnsQuotient))
      (NormedSpace.toModule (R := ℝ) (M := φ.gnsQuotient)) :=
  @LinearMap.mkContinuous ℝ ℝ φ.gnsQuotient φ.gnsQuotient _ _
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
    (NormedSpace.toModule (R := ℝ) (M := φ.gnsQuotient))
    (NormedSpace.toModule (R := ℝ) (M := φ.gnsQuotient))
    (RingHom.id ℝ) (φ.gnsPreRep a) (Real.sqrt (archimedeanBound a))
    (fun x => φ.gnsLeftAction_bounded a x)

end MPositiveState

end FreeStarAlgebra
