/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.ArchimedeanClosure.GNS.Star

/-! # Cyclic Vector Identity for GNS

This file proves the key cyclic vector identity: φ(a) = Re⟨Ω, π(a)Ω⟩.

## Main results

* `gnsRep_cyclicVector` - π(a)(Ω) = coe'([a]) in the real Hilbert space
* `gnsRep_inner_cyclicVector` - ⟨Ω, π(a)Ω⟩_ℝ = φ(a)

## Mathematical Background

The GNS construction produces:
- Cyclic vector Ω = [1] (the image of 1 in the quotient, embedded in completion)
- Representation π(a)[b] = [ab]

The cyclic vector identity:
  φ(a) = ⟨Ω, π(a)Ω⟩ = ⟨[1], [a*1]⟩ = ⟨[1], [a]⟩ = φ(star 1 * a) = φ(a)
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ} [IsArchimedean n] (φ : MPositiveState n)

/-! ### Cyclic Vector Identity in Real Hilbert Space -/

/-- The GNS representation maps the cyclic vector to coe'([a]).

This is π(a)(Ω) = coe'([a*1]) = coe'([a]). -/
theorem gnsRep_cyclicVector (a : FreeStarAlgebra n) :
    φ.gnsRep a φ.gnsCyclicVector =
    @UniformSpace.Completion.coe' φ.gnsQuotient φ.gnsQuotientNormedAddCommGroup.toUniformSpace
      (Submodule.Quotient.mk a) := by
  letI : SeminormedAddCommGroup φ.gnsQuotient :=
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
  -- gnsCyclicVector = coe'([1])
  unfold gnsCyclicVector
  -- Use gnsRep_coe: gnsRep a (coe' x) = coe' (gnsBoundedPreRep a x)
  rw [gnsRep_coe]
  -- gnsBoundedPreRep a [1] = gnsPreRep a [1] = [a*1] = [a]
  congr 1
  simp only [gnsBoundedPreRep_eq_gnsPreRep, gnsPreRep_mk, mul_one]

/-- The GNS inner product identity: ⟨Ω, π(a)Ω⟩_ℝ = φ(a).

This is the key identity relating the state to the GNS representation. -/
theorem gnsRep_inner_cyclicVector (a : FreeStarAlgebra n) :
    @inner ℝ φ.gnsHilbertSpaceReal _ φ.gnsCyclicVector (φ.gnsRep a φ.gnsCyclicVector) = φ a := by
  letI seminorm : SeminormedAddCommGroup φ.gnsQuotient :=
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
  letI ips : InnerProductSpace ℝ φ.gnsQuotient :=
    @InnerProductSpace.ofCore ℝ _ _ _ _ φ.gnsInnerProductCore.toCore
  -- Use the explicit formula for π(a)Ω
  rw [gnsRep_cyclicVector]
  -- Both sides are embedded quotient elements
  unfold gnsCyclicVector
  -- Inner product of coe' elements equals inner product of quotient elements
  rw [@UniformSpace.Completion.inner_coe ℝ φ.gnsQuotient _ seminorm ips]
  -- The quotient inner product is gnsInner
  rw [inner_eq_gnsInner]
  -- gnsInner [1] [a] = φ(star a * 1) by gnsInner_mk
  -- = φ(star 1 * a) by sesqForm_symm
  -- = φ(1 * a) = φ(a) by star_one and one_mul
  rw [gnsInner_mk, sesqForm_symm, star_one, one_mul]

end MPositiveState

end FreeStarAlgebra
