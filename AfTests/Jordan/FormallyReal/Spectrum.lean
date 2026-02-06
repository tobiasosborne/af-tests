/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.FormallyReal.Properties
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Spectral Properties of Jordan Algebras

This file develops spectral theory for Jordan algebras, including idempotents,
orthogonal decompositions, and spectral properties.

## Main definitions

* `JordanAlgebra.IsIdempotent` - e² = e
* `JordanAlgebra.AreOrthogonal` - orthogonal idempotents
* `JordanAlgebra.SpectralDecomp` - spectral decomposition structure

## Main results

* `IsIdempotent.jsq_eq_self` - e² = e
* `IsIdempotent.complement` - (1 - e) is idempotent when e is
* `jone_sub_idempotent_orthogonal` - e and (1 - e) are orthogonal

## Mathematical Background

In a finite-dimensional formally real Jordan algebra, every element `a` has a
unique spectral decomposition: `a = ∑ᵢ λᵢ eᵢ` where:
- `{eᵢ}` is a complete system of orthogonal primitive idempotents
- `λᵢ ∈ ℝ` are the eigenvalues (spectrum) of `a`
- `∑ᵢ eᵢ = 1` and `eᵢ ∘ eⱼ = 0` for i ≠ j

This is the Jordan algebra analog of the spectral theorem for Hermitian matrices.
-/

open Finset BigOperators

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-! ### Orthogonal Idempotents -/

-- Note: IsIdempotent is now defined in Basic.lean

/-- Two elements are orthogonal (in Jordan sense) if their product is zero. -/
def AreOrthogonal (e f : J) : Prop := jmul e f = 0

theorem AreOrthogonal.symm {e f : J} (h : AreOrthogonal e f) : AreOrthogonal f e := by
  unfold AreOrthogonal at *
  rw [jmul_comm]
  exact h

/-- An idempotent and its complement are orthogonal. -/
theorem jone_sub_idempotent_orthogonal {e : J} (he : IsIdempotent e) :
    AreOrthogonal e (jone - e) := by
  unfold AreOrthogonal IsIdempotent jsq at *
  rw [jmul_sub, jmul_jone, he, sub_self]

/-! ### Complete System of Orthogonal Idempotents -/

/-- A family of idempotents is pairwise orthogonal. -/
def PairwiseOrthogonal {n : ℕ} (e : Fin n → J) : Prop :=
  ∀ i j, i ≠ j → AreOrthogonal (e i) (e j)

/-- A complete system of orthogonal idempotents: pairwise orthogonal, sum to 1. -/
structure CSOI (J : Type*) [JordanAlgebra J] (n : ℕ) where
  /-- The idempotents. -/
  idem : Fin n → J
  /-- Each element is idempotent. -/
  is_idem : ∀ i, IsIdempotent (idem i)
  /-- Pairwise orthogonal. -/
  orthog : PairwiseOrthogonal idem
  /-- Sum to identity. -/
  complete : ∑ i, idem i = jone

/-! ### Spectral Decomposition -/

/-- A spectral decomposition of an element: a = ∑ᵢ λᵢ eᵢ where eᵢ form a CSOI. -/
structure SpectralDecomp (a : J) where
  /-- Number of eigenvalues. -/
  n : ℕ
  /-- The eigenvalues. -/
  eigenvalues : Fin n → ℝ
  /-- The idempotent system. -/
  csoi : CSOI J n
  /-- Decomposition equation. -/
  decomp : a = ∑ i, eigenvalues i • csoi.idem i

/-- The spectrum of an element (if it has a spectral decomposition). -/
def jordanSpectrum (a : J) (sd : SpectralDecomp a) : Set ℝ :=
  Set.range sd.eigenvalues

/-! ### Properties of Orthogonal Idempotents -/

/-- The sum of orthogonal idempotents is idempotent. -/
theorem orthogonal_sum_isIdempotent {e f : J}
    (he : IsIdempotent e) (hf : IsIdempotent f) (horth : AreOrthogonal e f) :
    IsIdempotent (e + f) := by
  unfold IsIdempotent jsq at *
  -- Goal: jmul (e + f) (e + f) = e + f
  rw [add_jmul, jmul_add, jmul_add, he, hf]
  -- Now: e + jmul e f + (jmul f e + f) = e + f
  rw [jmul_comm f e, horth, add_zero, zero_add]

/-- Product of orthogonal idempotents with scalars. -/
theorem jmul_orthog_idem {e f : J}
    (horth : AreOrthogonal e f) (r s : ℝ) :
    jmul (r • e) (s • f) = 0 := by
  rw [jmul_smul, smul_jmul, horth, smul_zero, smul_zero]

/-- Squaring a scalar multiple of an idempotent. -/
theorem jsq_smul_idem {e : J} (he : IsIdempotent e) (r : ℝ) :
    jsq (r • e) = (r ^ 2) • e := by
  unfold jsq at *
  rw [jmul_smul, smul_jmul, smul_smul]
  unfold IsIdempotent jsq at he
  rw [he, sq]

/-! ### Spectral Properties of Squares -/

/-- In a spectral decomposition, if all eigenvalues are zero, the element is zero. -/
theorem spectral_zero_of_eigenvalues_zero {a : J} (sd : SpectralDecomp a)
    (h : ∀ i, sd.eigenvalues i = 0) : a = 0 := by
  rw [sd.decomp]
  simp only [h, zero_smul, Finset.sum_const_zero]

/-- Squaring eigenvalues preserves non-negativity (trivially). -/
theorem spectral_eigenvalues_sq_nonneg {a : J} (sd : SpectralDecomp a) :
    ∀ i, 0 ≤ (sd.eigenvalues i) ^ 2 :=
  fun _ => sq_nonneg _

/-! ### Formally Real and Spectral Properties -/

-- NOTE: spectral_sq_eigenvalues_nonneg has been moved to SpectralTheorem.lean
-- as `sq_eigenvalues_nonneg`, where the trace inner product infrastructure is
-- available. It requires [FinDimJordanAlgebra J] [FormallyRealTrace J] and
-- nonzero idempotents: (hne : ∀ i, sd.csoi.idem i ≠ 0).

end JordanAlgebra
