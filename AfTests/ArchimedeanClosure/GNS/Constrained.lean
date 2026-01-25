/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.ArchimedeanClosure.GNS.Star
import AfTests.ArchimedeanClosure.Representation.Constrained

/-! # GNS Representation is Constrained

This file proves that the GNS representation of an M-positive state satisfies the
generator positivity constraint: π_φ(gⱼ) is a positive operator.

## Main results

* `gnsPreRep_generator_inner_nonneg` - Key identity: ⟨[b], π(gⱼ)[b]⟩ = φ(star b * gⱼ * b) ≥ 0
* `gnsRep_generator_inner_nonneg` - Extended to Hilbert space by density

## Mathematical Background

The key insight: For quotient element [b],
  ⟨[b], π(gⱼ)[b]⟩ = ⟨[b], [gⱼ * b]⟩ = φ(star b * gⱼ * b)

But star b * gⱼ * b ∈ M by the definition of the quadratic module (star_generator_mul_mem).
Since φ is M-positive, φ(star b * gⱼ * b) ≥ 0.

This extends to the full Hilbert space by continuity and density.
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ} [IsArchimedean n] (φ : MPositiveState n)

/-! ### Generator positivity on the quotient -/

omit [IsArchimedean n] in
/-- Key identity: ⟨[b], π(gⱼ)[b]⟩ = φ(star b * gⱼ * b) on quotient elements.

This combines gnsPreRep_mk and gnsInner_mk. -/
theorem gnsPreRep_generator_inner (j : Fin n) (b : FreeStarAlgebra n) :
    φ.gnsInner (Submodule.Quotient.mk b) (φ.gnsPreRep (generator j) (Submodule.Quotient.mk b)) =
    φ (star b * generator j * b) := by
  rw [gnsPreRep_mk, gnsInner_mk]
  -- star (gⱼ * b) * b = star b * star gⱼ * b = star b * gⱼ * b (gⱼ self-adjoint)
  simp only [star_mul, (isSelfAdjoint_generator j).star_eq, mul_assoc]

omit [IsArchimedean n] in
/-- The inner product ⟨[b], π(gⱼ)[b]⟩ is nonnegative for generators.

This is the key step: star b * gⱼ * b ∈ M by star_generator_mul_mem,
and φ is M-positive. -/
theorem gnsPreRep_generator_inner_nonneg (j : Fin n) (b : FreeStarAlgebra n) :
    0 ≤ φ.gnsInner (Submodule.Quotient.mk b)
      (φ.gnsPreRep (generator j) (Submodule.Quotient.mk b)) := by
  rw [gnsPreRep_generator_inner]
  exact φ.apply_m_nonneg (star_generator_mul_mem j b)

/-! ### Generator positivity on the Hilbert space -/

/-- The inner product ⟨x, π(gⱼ)x⟩ is nonnegative on the Hilbert space.

Extended from the quotient by density and continuity.
The set {x | 0 ≤ ⟪x, π(gⱼ)x⟫} is closed (continuous preimage of [0,∞)),
and contains the dense subset of quotient elements by gnsPreRep_generator_inner_nonneg. -/
theorem gnsRep_generator_inner_nonneg (j : Fin n) (x : φ.gnsHilbertSpaceReal) :
    0 ≤ @inner ℝ _ _ x (φ.gnsRep (generator j) x) := by
  letI seminorm : SeminormedAddCommGroup φ.gnsQuotient :=
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
  letI ips : InnerProductSpace ℝ φ.gnsQuotient :=
    @InnerProductSpace.ofCore ℝ _ _ _ _ φ.gnsInnerProductCore.toCore
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    -- The set {x | 0 ≤ ⟪x, π(gⱼ)x⟫} is closed
    apply isClosed_le continuous_const
    exact Continuous.inner continuous_id (φ.gnsRep (generator j)).continuous
  | ih y =>
    -- y is in the quotient, extract representative
    obtain ⟨b, rfl⟩ := φ.gnsQuotient_mk_surjective y
    rw [gnsRep_coe, @UniformSpace.Completion.inner_coe ℝ φ.gnsQuotient _ seminorm ips,
      inner_eq_gnsInner, gnsBoundedPreRep_eq_gnsPreRep]
    exact gnsPreRep_generator_inner_nonneg φ j b

end MPositiveState

end FreeStarAlgebra
