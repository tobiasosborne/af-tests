/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.ArchimedeanClosure.GNS.Extension
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # GNS Star Property

This file proves the GNS representation preserves the star operation: π(star a) = adjoint(π(a)).

## Main results

* `gnsPreRep_inner_star` - Key identity on quotient elements
* `gnsRep_star` - π(star a) = adjoint(π(a)) on the real Hilbert space

## Mathematical Background

The key calculation: For quotient elements [b], [c],
  ⟨[c], π(star a)[b]⟩ = ⟨[c], [star(a)*b]⟩ = φ(star(star(a)*b) * c) = φ(star(b)*a*c)
  ⟨π(a)[c], [b]⟩ = ⟨[a*c], [b]⟩ = φ(star(b) * (a*c)) = φ(star(b)*a*c)

These are equal, so π(star a) = adjoint(π(a)) by density and continuity.
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ} [IsArchimedean n] (φ : MPositiveState n)

/-! ### Star property on the pre-representation -/

/-- The pre-representation satisfies the adjoint identity on quotient elements. -/
theorem gnsPreRep_inner_star (a b c : FreeStarAlgebra n) :
    φ.gnsInner (φ.gnsPreRep (star a) (Submodule.Quotient.mk b)) (Submodule.Quotient.mk c) =
    φ.gnsInner (Submodule.Quotient.mk b) (φ.gnsPreRep a (Submodule.Quotient.mk c)) := by
  -- LHS: gnsInner [star(a)*b] [c] = φ(star(c) * (star(a)*b)) = φ(star(c)*star(a)*b)
  -- RHS: gnsInner [b] [a*c] = φ(star(a*c) * b) = φ(star(c)*star(a)*b)  (using star anti-hom)
  simp only [gnsPreRep_mk, gnsInner_mk, star_mul, mul_assoc]

/-! ### Star property on the extended representation -/

/-- gnsBoundedPreRep is just gnsPreRep with continuity data. -/
theorem gnsBoundedPreRep_eq_gnsPreRep (a : FreeStarAlgebra n) (x : φ.gnsQuotient) :
    φ.gnsBoundedPreRep a x = φ.gnsPreRep a x := by
  rfl

/-- The GNS representation preserves the star: π(star a) = adjoint(π(a)).

Uses that both sides are continuous and agree on the dense subset. -/
theorem gnsRep_star (a : FreeStarAlgebra n) :
    φ.gnsRep (star a) = ContinuousLinearMap.adjoint (φ.gnsRep a) := by
  letI : SeminormedAddCommGroup φ.gnsQuotient :=
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  -- Use density: it suffices to check on embedded quotient elements
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp =>
    apply isClosed_eq
    · exact continuous_inner.comp ((φ.gnsRep (star a)).continuous.prodMap continuous_id)
    · exact continuous_inner.comp (continuous_id.prodMap (φ.gnsRep a).continuous)
  | ih qb qc =>
    -- Extract algebra elements from quotient elements
    obtain ⟨b, rfl⟩ := φ.gnsQuotient_mk_surjective qb
    obtain ⟨c, rfl⟩ := φ.gnsQuotient_mk_surjective qc
    -- Compute both sides using the pre-representation
    simp only [gnsRep_coe, UniformSpace.Completion.inner_coe, inner_eq_gnsInner,
      gnsBoundedPreRep_eq_gnsPreRep]
    exact gnsPreRep_inner_star φ a b c

/-- Alternative formulation: star of gnsRep is adjoint. -/
theorem gnsRep_star' (a : FreeStarAlgebra n) :
    star (φ.gnsRep a) = φ.gnsRep (star a) := by
  rw [ContinuousLinearMap.star_eq_adjoint, gnsRep_star]

/-! ### Additional properties for StarAlgHom -/

/-- The representation of 0 is 0. -/
@[simp]
theorem gnsRep_zero : φ.gnsRep 0 = 0 := by
  letI : SeminormedAddCommGroup φ.gnsQuotient :=
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (φ.gnsRep 0).continuous continuous_const
  | ih y =>
    simp only [gnsRep_coe, ContinuousLinearMap.zero_apply]
    obtain ⟨z, rfl⟩ := φ.gnsQuotient_mk_surjective y
    simp only [gnsBoundedPreRep_eq_gnsPreRep, gnsPreRep_mk, zero_mul,
      Submodule.Quotient.mk_zero, UniformSpace.Completion.coe_zero]

/-- The representation respects scalar multiplication by ℝ. -/
theorem gnsRep_smul (r : ℝ) (a : FreeStarAlgebra n) : φ.gnsRep (r • a) = r • φ.gnsRep a := by
  letI : SeminormedAddCommGroup φ.gnsQuotient :=
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
  letI : NormedSpace ℝ φ.gnsQuotient := φ.gnsQuotientNormedSpace
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (φ.gnsRep _).continuous ((r • φ.gnsRep a).continuous)
  | ih y =>
    simp only [gnsRep_coe, ContinuousLinearMap.smul_apply]
    obtain ⟨z, rfl⟩ := φ.gnsQuotient_mk_surjective y
    simp only [gnsBoundedPreRep_eq_gnsPreRep, gnsPreRep_mk, Algebra.smul_mul_assoc,
      Submodule.Quotient.mk_smul]
    change (↑(r • Submodule.Quotient.mk (a * z) : φ.gnsQuotient) : φ.gnsHilbertSpaceReal) =
      r • (↑(Submodule.Quotient.mk (a * z) : φ.gnsQuotient) : φ.gnsHilbertSpaceReal)
    exact UniformSpace.Completion.coe_smul (M := ℝ) r (Submodule.Quotient.mk (a * z))

/-! ### Star property on the complexified representation -/

open ArchimedeanClosure

/-- Component norm squared inequality: ‖p.1‖² ≤ ‖p‖². -/
theorem Complexification.norm_sq_fst_le (p : Complexification φ.gnsHilbertSpaceReal) :
    ‖p.1‖^2 ≤ ‖p‖^2 := by
  rw [@norm_sq_eq_re_inner ℂ (Complexification φ.gnsHilbertSpaceReal) _
      Complexification.instNormedAddCommGroup.toSeminormedAddCommGroup
      Complexification.instInnerProductSpace]
  simp only [RCLike.re_eq_complex_re, Complexification.inner_re, real_inner_self_eq_norm_sq, sq]
  linarith [sq_nonneg ‖p.2‖]

/-- Component norm squared inequality: ‖p.2‖² ≤ ‖p‖². -/
theorem Complexification.norm_sq_snd_le (p : Complexification φ.gnsHilbertSpaceReal) :
    ‖p.2‖^2 ≤ ‖p‖^2 := by
  rw [@norm_sq_eq_re_inner ℂ (Complexification φ.gnsHilbertSpaceReal) _
      Complexification.instNormedAddCommGroup.toSeminormedAddCommGroup
      Complexification.instInnerProductSpace]
  simp only [RCLike.re_eq_complex_re, Complexification.inner_re, real_inner_self_eq_norm_sq, sq]
  linarith [sq_nonneg ‖p.1‖]

/-- Component norm is bounded by total norm: ‖p.1‖ ≤ ‖p‖. -/
theorem Complexification.norm_fst_le (p : Complexification φ.gnsHilbertSpaceReal) :
    ‖p.1‖ ≤ ‖p‖ := by
  have h := Complexification.norm_sq_fst_le φ p
  nlinarith [sq_nonneg ‖p.1‖, sq_nonneg ‖p‖, norm_nonneg p.1, norm_nonneg p]

/-- Component norm is bounded by total norm: ‖p.2‖ ≤ ‖p‖. -/
theorem Complexification.norm_snd_le (p : Complexification φ.gnsHilbertSpaceReal) :
    ‖p.2‖ ≤ ‖p‖ := by
  have h := Complexification.norm_sq_snd_le φ p
  nlinarith [sq_nonneg ‖p.2‖, sq_nonneg ‖p‖, norm_nonneg p.2, norm_nonneg p]

/-- The complexified Hilbert space is complete.

The norm ‖(x,y)‖² = ‖x‖² + ‖y‖² is equivalent to the product max norm.
Completeness follows from completeness of each component. -/
instance gnsHilbertSpaceComplex_completeSpace [IsArchimedean n] :
    CompleteSpace φ.gnsHilbertSpaceComplex := by
  letI := Complexification.instNormedAddCommGroup (H := φ.gnsHilbertSpaceReal)
  refine Metric.complete_of_cauchySeq_tendsto ?_
  intro u hu
  -- Project to components - they are Cauchy because ‖p.1‖ ≤ ‖p‖
  have h1 : CauchySeq (fun n => (u n).1) := by
    rw [Metric.cauchySeq_iff] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    use N
    intro m hm n' hn'
    calc dist (u m).1 (u n').1
        = ‖(u m).1 - (u n').1‖ := dist_eq_norm _ _
      _ = ‖(u m - u n').1‖ := rfl
      _ ≤ ‖u m - u n'‖ := Complexification.norm_fst_le φ (u m - u n')
      _ = dist (u m) (u n') := (dist_eq_norm (u m) (u n')).symm
      _ < ε := hN m hm n' hn'
  have h2 : CauchySeq (fun n => (u n).2) := by
    rw [Metric.cauchySeq_iff] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    use N
    intro m hm n' hn'
    calc dist (u m).2 (u n').2
        = ‖(u m).2 - (u n').2‖ := dist_eq_norm _ _
      _ = ‖(u m - u n').2‖ := rfl
      _ ≤ ‖u m - u n'‖ := Complexification.norm_snd_le φ (u m - u n')
      _ = dist (u m) (u n') := (dist_eq_norm (u m) (u n')).symm
      _ < ε := hN m hm n' hn'
  -- Get limits by completeness of gnsHilbertSpaceReal
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete h1
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete h2
  -- The pair converges
  let lim : Complexification φ.gnsHilbertSpaceReal := (x, y)
  refine ⟨lim, ?_⟩
  rw [Metric.tendsto_atTop] at hx hy ⊢
  intro ε hε
  obtain ⟨N1, hN1⟩ := hx (ε / 2) (half_pos hε)
  obtain ⟨N2, hN2⟩ := hy (ε / 2) (half_pos hε)
  use max N1 N2
  intro n hn
  have hn1 : N1 ≤ n := le_of_max_le_left hn
  have hn2 : N2 ≤ n := le_of_max_le_right hn
  have hnorm1 : ‖(u n).1 - x‖ < ε / 2 := by rw [← dist_eq_norm]; exact hN1 n hn1
  have hnorm2 : ‖(u n).2 - y‖ < ε / 2 := by rw [← dist_eq_norm]; exact hN2 n hn2
  have hdiff1 : (u n - lim).1 = (u n).1 - x := rfl
  have hdiff2 : (u n - lim).2 = (u n).2 - y := rfl
  rw [dist_eq_norm]
  have hbd : ‖(u n - lim).1‖^2 + ‖(u n - lim).2‖^2 < ε^2 := by
    rw [hdiff1, hdiff2]
    have hsq1 : ‖(u n).1 - x‖^2 < (ε/2)^2 :=
      (sq_lt_sq₀ (norm_nonneg _) (by linarith : 0 ≤ ε/2)).mpr hnorm1
    have hsq2 : ‖(u n).2 - y‖^2 < (ε/2)^2 :=
      (sq_lt_sq₀ (norm_nonneg _) (by linarith : 0 ≤ ε/2)).mpr hnorm2
    calc ‖(u n).1 - x‖^2 + ‖(u n).2 - y‖^2
        < (ε/2)^2 + (ε/2)^2 := add_lt_add hsq1 hsq2
      _ = ε^2/2 := by ring
      _ < ε^2 := by linarith [sq_pos_of_pos hε]
  have hnorm_sq : ‖u n - lim‖^2 = ‖(u n - lim).1‖^2 + ‖(u n - lim).2‖^2 := by
    rw [@norm_sq_eq_re_inner ℂ _ _ Complexification.instNormedAddCommGroup.toSeminormedAddCommGroup
        Complexification.instInnerProductSpace (u n - lim)]
    have hinner : @inner ℂ _ Complexification.instInnerComplex (u n - lim) (u n - lim)
        = { re := @inner ℝ _ _ (u n - lim).1 (u n - lim).1 +
                  @inner ℝ _ _ (u n - lim).2 (u n - lim).2,
            im := @inner ℝ _ _ (u n - lim).1 (u n - lim).2 -
                  @inner ℝ _ _ (u n - lim).2 (u n - lim).1 } :=
      Complexification.inner_def _ _
    simp only [hinner, real_inner_self_eq_norm_sq, sq]
    rfl
  calc ‖u n - lim‖
      = Real.sqrt (‖u n - lim‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖(u n - lim).1‖^2 + ‖(u n - lim).2‖^2) := by rw [hnorm_sq]
    _ < Real.sqrt (ε^2) := Real.sqrt_lt_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)) hbd
    _ = ε := Real.sqrt_sq (le_of_lt hε)

/-- The complexified representation preserves the star: π_ℂ(star a) = adjoint(π_ℂ(a)).

The key is that gnsRepComplex acts componentwise: π_ℂ(a)(x,y) = (π(a)x, π(a)y).
Using gnsRep_star on each component gives the adjoint property. -/
theorem gnsRepComplex_star [IsArchimedean n] (a : FreeStarAlgebra n) :
    φ.gnsRepComplex (star a) = ContinuousLinearMap.adjoint (φ.gnsRepComplex a) := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro p q
  -- Expand inner products on complexification
  apply Complex.ext
  · -- Real part: Re⟪π_ℂ(star a) p, q⟫ = Re⟪p, π_ℂ(a) q⟫
    simp only [Complexification.inner_re]
    -- gnsRepComplex acts componentwise via mapComplex
    have hL1 : (φ.gnsRepComplex (star a) p).1 = φ.gnsRep (star a) p.1 := rfl
    have hL2 : (φ.gnsRepComplex (star a) p).2 = φ.gnsRep (star a) p.2 := rfl
    have hR1 : (φ.gnsRepComplex a q).1 = φ.gnsRep a q.1 := rfl
    have hR2 : (φ.gnsRepComplex a q).2 = φ.gnsRep a q.2 := rfl
    rw [hL1, hL2, hR1, hR2]
    -- Use gnsRep_star: π(star a) = adjoint(π(a)), then adjoint property
    simp only [gnsRep_star, ContinuousLinearMap.adjoint_inner_left]
  · -- Imaginary part: similar calculation
    simp only [Complexification.inner_im]
    have hL1 : (φ.gnsRepComplex (star a) p).1 = φ.gnsRep (star a) p.1 := rfl
    have hL2 : (φ.gnsRepComplex (star a) p).2 = φ.gnsRep (star a) p.2 := rfl
    have hR1 : (φ.gnsRepComplex a q).1 = φ.gnsRep a q.1 := rfl
    have hR2 : (φ.gnsRepComplex a q).2 = φ.gnsRep a q.2 := rfl
    rw [hL1, hL2, hR1, hR2]
    simp only [gnsRep_star, ContinuousLinearMap.adjoint_inner_left]

/-- The complexified representation sends 1 to the identity. -/
theorem gnsRepComplex_one : φ.gnsRepComplex 1 = ContinuousLinearMap.id ℂ _ := by
  ext p
  · simp only [ContinuousLinearMap.id_apply]
    unfold gnsRepComplex
    simp only [LinearMap.mkContinuous_apply, Complexification.mapComplex_fst]
    rw [gnsRep_one]
    simp only [ContinuousLinearMap.coe_id, LinearMap.id_apply]
  · simp only [ContinuousLinearMap.id_apply]
    unfold gnsRepComplex
    simp only [LinearMap.mkContinuous_apply, Complexification.mapComplex_snd]
    rw [gnsRep_one]
    simp only [ContinuousLinearMap.coe_id, LinearMap.id_apply]

/-- The complexified representation preserves multiplication: π_ℂ(a*b) = π_ℂ(a) ∘ π_ℂ(b). -/
theorem gnsRepComplex_mul (a b : FreeStarAlgebra n) :
    φ.gnsRepComplex (a * b) = (φ.gnsRepComplex a).comp (φ.gnsRepComplex b) := by
  ext p
  · simp only [ContinuousLinearMap.comp_apply]
    unfold gnsRepComplex
    simp only [LinearMap.mkContinuous_apply, Complexification.mapComplex_fst]
    rw [gnsRep_mul]
    rfl
  · simp only [ContinuousLinearMap.comp_apply]
    unfold gnsRepComplex
    simp only [LinearMap.mkContinuous_apply, Complexification.mapComplex_snd]
    rw [gnsRep_mul]
    rfl

end MPositiveState

end FreeStarAlgebra
