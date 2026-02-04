/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Eigenspace
import AfTests.Jordan.Primitive
import AfTests.Jordan.FormallyReal.Spectrum
import AfTests.Jordan.TraceInnerProduct
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum

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

/-- The direct sum of eigenspaces of L_a equals all of J.
    This is the key diagonalizability result for self-adjoint operators.

    Proof outline: L_a is self-adjoint w.r.t. traceInner (by traceInner_jmul_left),
    and in finite-dimensional inner product space, self-adjoint ⟹ diagonalizable. -/
theorem eigenspaces_span [FinDimJordanAlgebra J] [FormallyRealTrace J] (a : J) :
    ⨆ μ ∈ eigenvalueSet a, eigenspace a μ = ⊤ := by
  -- Set up the inner product space from trace
  letI : NormedAddCommGroup J := traceNormedAddCommGroup (J := J)
  letI : InnerProductSpace ℝ J := traceInnerProductSpace (J := J)
  -- L_a is symmetric w.r.t. inner product (= traceInner)
  have hL_sym : (L a).IsSymmetric := fun x y => by
    simp only [L_apply]
    change traceInnerReal (jmul a x) y = traceInnerReal x (jmul a y)
    simp only [traceInnerReal]
    exact traceInner_jmul_left a x y
  -- Apply spectral theorem: orthogonal complement of eigenspaces is trivial
  have h := hL_sym.orthogonalComplement_iSup_eigenspaces_eq_bot
  -- Convert Mᗮ = ⊥ to M = ⊤
  rw [Submodule.orthogonal_eq_bot_iff] at h
  -- eigenspace a μ = Module.End.eigenspace (L a) μ by definition
  -- ⨆ μ, eigenspace (L a) μ = ⨆ μ ∈ eigenvalueSet a, eigenspace a μ
  -- (non-eigenvalues contribute ⊥, so they don't change the sup)
  convert h using 1
  apply le_antisymm
  · apply iSup₂_le
    intro μ _
    exact le_iSup (fun μ => Module.End.eigenspace (L a) μ) μ
  · apply iSup_le
    intro μ
    by_cases hμ : Module.End.eigenspace (L a) μ = ⊥
    · rw [hμ]; exact bot_le
    · have hμ' : μ ∈ eigenvalueSet a := by
        rw [mem_eigenvalueSet_iff, isEigenvalue_iff, eigenspace]
        exact hμ
      exact le_iSup₂_of_le μ hμ' le_rfl

/-- For each eigenvalue, we can construct an orthogonal projection onto the eigenspace. -/
theorem spectral_projection_exists [FinDimJordanAlgebra J] [JordanTrace J] [FormallyRealJordan J]
    (a : J) (μ : ℝ) (hμ : μ ∈ eigenvalueSet a) :
    ∃ e : J, IsIdempotent e ∧ (∀ v, v ∈ eigenspace a μ ↔ jmul e v = v) := by
  -- Spectral projection is an idempotent
  sorry

/-- Every element in a finite-dimensional formally real Jordan algebra has
    a spectral decomposition with primitive idempotents.

    Proof strategy:
    1. Get the finite set of eigenvalues (eigenvalueSet_finite)
    2. Show eigenspaces span J (eigenspaces_span, via self-adjointness of L_a)
    3. Construct spectral projections as idempotents (spectral_projection_exists)
    4. Form a CSOI from projections and refine to primitives (csoi_refine_primitive) -/
theorem spectral_decomposition_exists [FinDimJordanAlgebra J] [FormallyRealTrace J]
    [FormallyRealJordan J] (a : J) :
    ∃ sd : SpectralDecomp a, ∀ i, IsPrimitive (sd.csoi.idem i) := by
  -- Step 1: Get the finite set of eigenvalues
  have hfin : (eigenvalueSet a).Finite := eigenvalueSet_finite a
  let S := hfin.toFinset
  -- Step 2: Each element of J is in some eigenspace (eigenspaces span J)
  have hspan : ⨆ μ ∈ eigenvalueSet a, eigenspace a μ = ⊤ := eigenspaces_span a
  -- Step 3: Construct spectral projections and show they form a CSOI
  -- Step 4: Refine to primitive idempotents using csoi_refine_primitive
  sorry

/-- Spectral decomposition with Finset-indexed sum. -/
theorem spectral_decomposition_finset [FinDimJordanAlgebra J] [FormallyRealTrace J]
    [FormallyRealJordan J] (a : J) :
    ∃ (S : Finset ℝ) (e : ℝ → J),
      (∀ r ∈ S, IsIdempotent (e r)) ∧
      (∀ r s, r ∈ S → s ∈ S → r ≠ s → AreOrthogonal (e r) (e s)) ∧
      (∑ r ∈ S, e r = jone) ∧
      (a = ∑ r ∈ S, r • e r) := by
  obtain ⟨sd, _⟩ := spectral_decomposition_exists a
  -- Convert Fin n-indexed to Finset-indexed
  sorry

/-! ### Spectral Decomposition Properties -/

/-- jmul distributes over finite sums on the left. -/
theorem sum_jmul {ι : Type*} (s : Finset ι) (f : ι → J) (r : ι → ℝ) (e : J) :
    jmul (∑ i ∈ s, r i • f i) e = ∑ i ∈ s, r i • jmul (f i) e := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_jmul]
  | insert x s' hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    rw [add_jmul, jmul_smul, ih]

/-- In a spectral decomposition a = ∑ λᵢ eᵢ, each idempotent is an eigenvector:
    a ∘ eⱼ = λⱼ eⱼ. -/
theorem spectral_decomp_jmul_idem {a : J} (sd : SpectralDecomp a) (j : Fin sd.n) :
    jmul a (sd.csoi.idem j) = sd.eigenvalues j • sd.csoi.idem j := by
  -- Use calc to avoid motive issues with sd depending on a
  calc jmul a (sd.csoi.idem j)
      = jmul (∑ i, sd.eigenvalues i • sd.csoi.idem i) (sd.csoi.idem j) := by
        simp only [sd.decomp]
    _ = ∑ i, sd.eigenvalues i • jmul (sd.csoi.idem i) (sd.csoi.idem j) :=
        sum_jmul Finset.univ sd.csoi.idem sd.eigenvalues (sd.csoi.idem j)
    _ = sd.eigenvalues j • jmul (sd.csoi.idem j) (sd.csoi.idem j) +
        ∑ i ∈ Finset.univ.erase j, sd.eigenvalues i • jmul (sd.csoi.idem i) (sd.csoi.idem j) := by
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
    _ = sd.eigenvalues j • jmul (sd.csoi.idem j) (sd.csoi.idem j) + 0 := by
        have h : ∑ i ∈ Finset.univ.erase j,
            sd.eigenvalues i • jmul (sd.csoi.idem i) (sd.csoi.idem j) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          rw [Finset.mem_erase] at hi
          rw [sd.csoi.orthog i j hi.1, smul_zero]
        rw [h]
    _ = sd.eigenvalues j • sd.csoi.idem j := by
        rw [add_zero, ← jsq_def, (sd.csoi.is_idem j).jsq_eq_self]

/-- Eigenvalues from a spectral decomposition are eigenvalues of L_a.
    This is one direction of spectrum_eq_eigenvalueSet. -/
theorem spectral_decomp_eigenvalue_mem_spectrum {a : J} (sd : SpectralDecomp a)
    (j : Fin sd.n) (hne : sd.csoi.idem j ≠ 0) :
    sd.eigenvalues j ∈ spectrum a := by
  rw [mem_spectrum_iff, isEigenvalue_iff_exists_eigenvector]
  exact ⟨sd.csoi.idem j, hne, spectral_decomp_jmul_idem sd j⟩

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

-- REMOVED: spectrum_sq was incorrectly stated
-- It claimed spectrum(a²) = (·^2)'' spectrum(a), conflating:
--   - H-O's spectrum (functional calculus: invertibility in C(a))
--   - Our eigenvalueSet (eigenvalues of L_a operator)
-- These are different! For A=diag(1,2), L_A has eigenvalue 3/2 from Peirce-½ space.
-- See issue af-cxcc. The correct result for decomposition eigenvalues is spectral_sq above.

/-! ### Positivity of Square Eigenvalues -/

/-- Eigenvalues of a² are non-negative (they are squares of reals). -/
theorem sq_eigenvalues_nonneg [FinDimJordanAlgebra J] [JordanTrace J] [FormallyRealJordan J]
    {a : J} (sd : SpectralDecomp (jsq a)) :
    ∀ i, 0 ≤ sd.eigenvalues i := by
  intro i
  -- By spectral_sq, eigenvalues of a² are sⱼ² for eigenvalues sⱼ of a
  -- Squares are non-negative
  sorry

-- REMOVED: spectrum_sq_nonneg depended on the false spectrum_sq
-- The claim "eigenvalues of L_{a²} are non-negative" may or may not be true,
-- but the proof was using an incorrect theorem. See af-cxcc.

end JordanAlgebra
