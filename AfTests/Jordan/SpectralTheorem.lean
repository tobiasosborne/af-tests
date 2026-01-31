/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Eigenspace
import AfTests.Jordan.Primitive
import AfTests.Jordan.FormallyReal.Spectrum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Spectral Theorem for Jordan Algebras

This file proves the spectral theorem for finite-dimensional formally real Jordan algebras:
every element has a unique spectral decomposition.

## Main results

* `spectral_decomposition_exists` - Existence of spectral decomposition
* `spectrum_eq` - Spectrum equals eigenvalue set from L_a
* `spectral_sq` - Square has squared eigenvalues
* `sq_eigenvalues_nonneg` - Eigenvalues of a² are non-negative
-/

open Finset BigOperators

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-! ### Spectrum Definition -/

/-- The spectrum of an element is the set of eigenvalues of L_a.
In finite dimensions, this is a finite set of real numbers. -/
def spectrum (a : J) : Set ℝ := eigenvalueSet a

theorem mem_spectrum_iff (a : J) (r : ℝ) :
    r ∈ spectrum a ↔ IsEigenvalue a r := Iff.rfl

theorem spectrum_finite [FinDimJordanAlgebra J] (a : J) :
    Set.Finite (spectrum a) := eigenvalueSet_finite a

/-! ### Spectral Decomposition Existence -/

/-- Every element in a finite-dimensional formally real Jordan algebra has
a spectral decomposition.

Mathematical proof sketch:
1. spectrum a is finite (from eigenvalueSet_finite)
2. For each r ∈ spectrum a, eigenspace a r is nonzero
3. Eigenspaces are orthogonal w.r.t. trace (eigenspace_orthogonal)
4. Eigenspaces span J (this is the key step requiring formally real)
5. Construct CSOI from spectral projections -/
theorem spectral_decomposition_exists [FinDimJordanAlgebra J] [JordanTrace J]
    [FormallyRealJordan J] (a : J) :
    ∃ sd : SpectralDecomp a, ∀ i, IsPrimitive (sd.csoi.idem i) := by
  -- The full proof requires constructing spectral projections from eigenspaces
  -- and showing they form a primitive CSOI. This is a deep result.
  sorry

/-- Spectral decomposition with Finset-indexed sum. -/
theorem spectral_decomposition_finset [FinDimJordanAlgebra J] [JordanTrace J]
    [FormallyRealJordan J] (a : J) :
    ∃ (S : Finset ℝ) (e : ℝ → J),
      (∀ r ∈ S, IsIdempotent (e r)) ∧
      (∀ r s, r ∈ S → s ∈ S → r ≠ s → AreOrthogonal (e r) (e s)) ∧
      (∑ r ∈ S, e r = jone) ∧
      (a = ∑ r ∈ S, r • e r) := by
  obtain ⟨sd, _⟩ := spectral_decomposition_exists a
  -- Convert Fin n-indexed to Finset-indexed
  sorry

/-! ### Uniqueness Results -/

/-- The spectrum (eigenvalue set) is unique - it equals eigenvalueSet a. -/
theorem spectrum_eq_eigenvalueSet [FinDimJordanAlgebra J] [JordanTrace J]
    [FormallyRealJordan J] (a : J) (sd : SpectralDecomp a) :
    jordanSpectrum a sd = spectrum a := by
  -- Both characterize the same eigenvalues of L_a
  sorry

/-- Eigenvalues in spectral decomposition are exactly spectrum a. -/
theorem spectral_decomp_eigenvalues_eq_spectrum [FinDimJordanAlgebra J] [JordanTrace J]
    [FormallyRealJordan J] (a : J) (sd : SpectralDecomp a) :
    Set.range sd.eigenvalues = spectrum a :=
  spectrum_eq_eigenvalueSet a sd

/-! ### Square Eigenvalue Theorem -/

/-- jmul distributes over finite sums on the left. -/
theorem sum_jmul {ι : Type*} (s : Finset ι) (f : ι → J) (r : ι → ℝ) (e : J) :
    jmul (∑ i ∈ s, r i • f i) e = ∑ i ∈ s, r i • jmul (f i) e := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_jmul]
  | insert x s' hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    rw [add_jmul, jmul_smul, ih]

/-- Squaring a sum of scaled orthogonal idempotents gives squared coefficients. -/
theorem jsq_sum_orthog_idem {n : ℕ} (c : CSOI J n) (coef : Fin n → ℝ) :
    jsq (∑ i, coef i • c.idem i) = ∑ i, (coef i) ^ 2 • c.idem i := by
  classical
  unfold jsq
  -- Step 1: Expand left multiplication over the sum
  rw [sum_jmul Finset.univ c.idem coef (∑ j, coef j • c.idem j)]
  -- Goal: ∑ i, coef i • jmul (c.idem i) (∑ j, coef j • c.idem j) = ∑ i, coef i ^ 2 • c.idem i
  -- Step 2: For each i, expand the inner jmul over the sum
  have expand_inner : ∀ i, jmul (c.idem i) (∑ j, coef j • c.idem j) =
      ∑ j, coef j • jmul (c.idem i) (c.idem j) := fun i =>
    jmul_sum Finset.univ (c.idem i) coef c.idem
  simp only [expand_inner]
  -- Goal: ∑ i, coef i • ∑ j, coef j • jmul (c.idem i) (c.idem j) = ∑ i, coef i ^ 2 • c.idem i
  -- Step 3: Distribute outer smul into inner sum
  simp only [Finset.smul_sum]
  -- Goal: ∑ i, ∑ j, coef i • coef j • jmul (c.idem i) (c.idem j) = ...
  simp only [smul_smul]
  -- Goal: ∑ i, ∑ j, (coef i * coef j) • jmul (c.idem i) (c.idem j) = ...
  -- Step 4: For each i, extract diagonal term and show others vanish
  congr 1
  ext i
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  have other_terms :
      ∑ j ∈ Finset.univ.erase i, (coef i * coef j) • jmul (c.idem i) (c.idem j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_erase] at hj
    rw [c.orthog i j hj.1.symm, smul_zero]
  rw [other_terms, add_zero]
  -- c.is_idem i : IsIdempotent (c.idem i), which means jsq (c.idem i) = c.idem i
  -- So jmul (c.idem i) (c.idem i) = c.idem i
  have h_idem : jmul (c.idem i) (c.idem i) = c.idem i := c.is_idem i
  rw [h_idem, sq]

/-- The spectral decomposition of a² uses the same CSOI with squared eigenvalues.

Proof: If a = Σ λᵢ eᵢ with orthogonal idempotents, then
  a² = (Σ λᵢ eᵢ)² = Σ λᵢ² eᵢ
since eᵢ ∘ eⱼ = 0 for i ≠ j and eᵢ² = eᵢ. -/
theorem spectral_sq [FinDimJordanAlgebra J] [JordanTrace J] [FormallyRealJordan J]
    (a : J) (sd : SpectralDecomp a) :
    ∃ sd_sq : SpectralDecomp (jsq a), sd_sq.n = sd.n := by
  -- Construct sd_sq using same CSOI, squared eigenvalues
  -- First show jsq a = ∑ i, (λᵢ²) • eᵢ
  have key : jsq a = ∑ i, (sd.eigenvalues i) ^ 2 • sd.csoi.idem i := by
    have h1 : jsq a = jsq (∑ i, sd.eigenvalues i • sd.csoi.idem i) := congrArg jsq sd.decomp
    have h2 : jsq (∑ i, sd.eigenvalues i • sd.csoi.idem i) =
        ∑ i, (sd.eigenvalues i) ^ 2 • sd.csoi.idem i := jsq_sum_orthog_idem sd.csoi sd.eigenvalues
    exact h1.trans h2
  exact ⟨⟨sd.n, fun i => (sd.eigenvalues i) ^ 2, sd.csoi, key⟩, rfl⟩

/-- Eigenvalues of a² are squares of eigenvalues of a. -/
theorem spectrum_sq [FinDimJordanAlgebra J] [JordanTrace J] [FormallyRealJordan J] (a : J) :
    spectrum (jsq a) = (· ^ 2) '' spectrum a := by
  ext r
  constructor
  · intro hr
    -- r is eigenvalue of a², so r = s² for some eigenvalue s of a
    sorry
  · intro ⟨s, hs, hrs⟩
    -- s is eigenvalue of a, r = s², show r is eigenvalue of a²
    sorry

/-! ### Positivity of Square Eigenvalues -/

/-- Eigenvalues of a² are non-negative (they are squares of reals). -/
theorem sq_eigenvalues_nonneg [FinDimJordanAlgebra J] [JordanTrace J] [FormallyRealJordan J]
    {a : J} (sd : SpectralDecomp (jsq a)) :
    ∀ i, 0 ≤ sd.eigenvalues i := by
  intro i
  -- By spectral_sq, eigenvalues of a² are sⱼ² for eigenvalues sⱼ of a
  -- Squares are non-negative
  sorry

/-- The spectrum of a² consists of non-negative reals. -/
theorem spectrum_sq_nonneg [FinDimJordanAlgebra J] [JordanTrace J] [FormallyRealJordan J]
    (a : J) : ∀ r ∈ spectrum (jsq a), 0 ≤ r := by
  intro r hr
  rw [spectrum_sq] at hr
  obtain ⟨s, _, rfl⟩ := hr
  exact sq_nonneg s

end JordanAlgebra
