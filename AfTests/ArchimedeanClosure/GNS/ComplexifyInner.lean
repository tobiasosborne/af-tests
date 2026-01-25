/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.ArchimedeanClosure.GNS.Complexify

/-! # InnerProductSpace Axioms for Complexification

This file proves the InnerProductSpace axioms for the complexification of a
real inner product space.

## Main results

* `inner_conj_symm'` - Conjugate symmetry: conj⟪q, p⟫ = ⟪p, q⟫
* `inner_add_left'` - Additivity: ⟪p + p', q⟫ = ⟪p, q⟫ + ⟪p', q⟫
* `inner_nonneg_re'` - Positivity: 0 ≤ Re⟪p, p⟫
* `inner_smul_left'` - Scalar multiplication: ⟪c • p, q⟫ = conj(c) * ⟪p, q⟫
* `inner_definite'` - Definiteness: ⟪p, p⟫ = 0 → p = 0

All 5 InnerProductSpace.Core axioms are now proven!
-/

namespace ArchimedeanClosure

open scoped InnerProductSpace

namespace Complexification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Conjugate symmetry: ⟪q, p⟫_ℂ = conj(⟪p, q⟫_ℂ).

Uses that the real inner product is symmetric: ⟪a, b⟫_ℝ = ⟪b, a⟫_ℝ. -/
theorem inner_conj_symm' (p q : Complexification H) :
    starRingEnd ℂ ⟪q, p⟫_ℂ = ⟪p, q⟫_ℂ := by
  apply Complex.ext
  · -- Real part: ⟪q.1,p.1⟫ + ⟪q.2,p.2⟫ = ⟪p.1,q.1⟫ + ⟪p.2,q.2⟫
    simp only [Complex.conj_re, inner_re]
    rw [real_inner_comm q.1 p.1, real_inner_comm q.2 p.2]
  · -- Imaginary part: -(⟪q.1,p.2⟫ - ⟪q.2,p.1⟫) = ⟪p.1,q.2⟫ - ⟪p.2,q.1⟫
    simp only [Complex.conj_im, inner_im, neg_sub]
    rw [real_inner_comm q.1 p.2, real_inner_comm q.2 p.1]

/-- Additivity: ⟪p + p', q⟫_ℂ = ⟪p, q⟫_ℂ + ⟪p', q⟫_ℂ. -/
theorem inner_add_left' (p p' q : Complexification H) :
    ⟪p + p', q⟫_ℂ = ⟪p, q⟫_ℂ + ⟪p', q⟫_ℂ := by
  apply Complex.ext
  · -- Real part: ⟪(p+p').1, q.1⟫ + ⟪(p+p').2, q.2⟫ = ...
    simp only [inner_re, Complex.add_re]
    -- (p + p').1 = p.1 + p'.1 and (p + p').2 = p.2 + p'.2
    change @inner ℝ H _ (p.1 + p'.1) q.1 + @inner ℝ H _ (p.2 + p'.2) q.2 = _
    rw [inner_add_left (𝕜 := ℝ) p.1 p'.1 q.1, inner_add_left (𝕜 := ℝ) p.2 p'.2 q.2]
    ring
  · -- Imaginary part
    simp only [inner_im, Complex.add_im]
    change @inner ℝ H _ (p.1 + p'.1) q.2 - @inner ℝ H _ (p.2 + p'.2) q.1 = _
    rw [inner_add_left (𝕜 := ℝ) p.1 p'.1 q.2, inner_add_left (𝕜 := ℝ) p.2 p'.2 q.1]
    ring

/-- Positivity: 0 ≤ Re⟪p, p⟫_ℂ.

For p = (x, y), Re⟪p, p⟫ = ⟪x, x⟫_ℝ + ⟪y, y⟫_ℝ ≥ 0. -/
theorem inner_nonneg_re' (p : Complexification H) :
    0 ≤ (⟪p, p⟫_ℂ).re := by
  simp only [inner_re]
  exact add_nonneg real_inner_self_nonneg real_inner_self_nonneg

/-- Scalar multiplication: ⟪c • p, q⟫_ℂ = conj(c) * ⟪p, q⟫_ℂ.

For c = a + bi, expands c • p = (a·x - b·y, a·y + b·x) and uses real inner
product linearity. -/
theorem inner_smul_left' (c : ℂ) (p q : Complexification H) :
    ⟪c • p, q⟫_ℂ = starRingEnd ℂ c * ⟪p, q⟫_ℂ := by
  apply Complex.ext
  · -- Real part: Re⟪c•p, q⟫ = Re(conj(c) * ⟪p,q⟫) = a·Re⟪p,q⟫ + b·Im⟪p,q⟫
    simp only [inner_re, smul_fst, smul_snd, Complex.mul_re, Complex.conj_re,
               Complex.conj_im, inner_im]
    -- LHS: ⟪a·x₁ - b·y₁, x₂⟫ + ⟪a·y₁ + b·x₁, y₂⟫
    -- Use inner_sub_left and inner_add_left, then inner_smul_left
    rw [inner_sub_left (𝕜 := ℝ), inner_add_left (𝕜 := ℝ)]
    rw [inner_smul_left (𝕜 := ℝ), inner_smul_left (𝕜 := ℝ),
        inner_smul_left (𝕜 := ℝ), inner_smul_left (𝕜 := ℝ)]
    simp only [RCLike.conj_to_real]
    ring
  · -- Imaginary part: Im⟪c•p, q⟫ = Im(conj(c) * ⟪p,q⟫) = a·Im⟪p,q⟫ - b·Re⟪p,q⟫
    simp only [inner_im, smul_fst, smul_snd, Complex.mul_im, Complex.conj_re,
               Complex.conj_im, inner_re]
    rw [inner_sub_left (𝕜 := ℝ), inner_add_left (𝕜 := ℝ)]
    rw [inner_smul_left (𝕜 := ℝ), inner_smul_left (𝕜 := ℝ),
        inner_smul_left (𝕜 := ℝ), inner_smul_left (𝕜 := ℝ)]
    simp only [RCLike.conj_to_real]
    ring

/-- Definiteness: ⟪p, p⟫_ℂ = 0 → p = 0.

For p = (x, y), ⟪p, p⟫ = 0 implies ⟪x, x⟫_ℝ + ⟪y, y⟫_ℝ = 0.
Since both terms are nonnegative, each is 0, so x = y = 0. -/
theorem inner_definite' (p : Complexification H) (hp : ⟪p, p⟫_ℂ = 0) : p = 0 := by
  -- Extract that real part is 0
  have hre : (⟪p, p⟫_ℂ).re = 0 := by rw [hp]; rfl
  simp only [inner_re] at hre
  -- Both ⟪p.1, p.1⟫ and ⟪p.2, p.2⟫ are nonneg, sum = 0 implies each = 0
  have h1 : @inner ℝ H _ p.1 p.1 = 0 :=
    (add_eq_zero_iff_of_nonneg real_inner_self_nonneg real_inner_self_nonneg).mp hre |>.1
  have h2 : @inner ℝ H _ p.2 p.2 = 0 :=
    (add_eq_zero_iff_of_nonneg real_inner_self_nonneg real_inner_self_nonneg).mp hre |>.2
  -- By definiteness of real inner product
  have hp1 : p.1 = 0 := inner_self_eq_zero (𝕜 := ℝ).mp h1
  have hp2 : p.2 = 0 := inner_self_eq_zero (𝕜 := ℝ).mp h2
  ext <;> assumption

end Complexification

end ArchimedeanClosure
