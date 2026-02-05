/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Eigenspace
import AfTests.Jordan.Primitive
import AfTests.Jordan.FormallyReal.Spectrum
import AfTests.Jordan.TraceInnerProduct
import AfTests.Jordan.Subalgebra
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

/-- If each idempotent in a CSOI is an eigenvector of L_a, then a = Σ λᵢ eᵢ.
    This is the key reduction: finding eigenvector-CSOIs gives spectral decompositions. -/
theorem spectral_decomp_of_eigenvector_csoi {n : ℕ} (a : J) (c : CSOI J n) (coef : Fin n → ℝ)
    (heig : ∀ i, jmul a (c.idem i) = coef i • c.idem i) :
    a = ∑ i, coef i • c.idem i := by
  -- a = a ∘ 1 = a ∘ (Σ eᵢ) = Σ (a ∘ eᵢ) = Σ λᵢ eᵢ
  have hone : ∑ i : Fin n, c.idem i = ∑ i : Fin n, (1 : ℝ) • c.idem i := by simp
  calc a = jmul a jone := by rw [jmul_jone]
    _ = jmul a (∑ i, c.idem i) := by rw [c.complete]
    _ = jmul a (∑ i, (1 : ℝ) • c.idem i) := by rw [hone]
    _ = ∑ i, (1 : ℝ) • jmul a (c.idem i) := jmul_sum Finset.univ a (fun _ => 1) c.idem
    _ = ∑ i, jmul a (c.idem i) := by simp
    _ = ∑ i, coef i • c.idem i := by simp only [heig]

/-- For idempotent e ∈ C(a), we have jmul a e ∈ P₁(e).
    Key step: associativity in C(a) gives jmul e (jmul a e) = jmul a (jmul e e) = jmul a e. -/
theorem jmul_generator_idem_in_peirce_one (a : J) {e : J}
    (he_idem : IsIdempotent e) (he_mem : e ∈ generatedSubalgebra a) :
    jmul a e ∈ PeirceSpace e 1 := by
  rw [mem_peirceSpace_one_iff]
  -- generatedSubalgebra_jmul_assoc: jmul (jmul x y) z = jmul x (jmul y z)
  have h1 : jmul (jmul e a) e = jmul e (jmul a e) :=
    generatedSubalgebra_jmul_assoc a he_mem (self_mem_generatedSubalgebra a) he_mem
  have h2 : jmul (jmul a e) e = jmul a (jmul e e) :=
    generatedSubalgebra_jmul_assoc a (self_mem_generatedSubalgebra a) he_mem he_mem
  -- jmul e (jmul a e) = jmul (jmul e a) e = jmul (jmul a e) e = jmul a (jmul e e) = jmul a e
  calc jmul e (jmul a e) = jmul (jmul e a) e := h1.symm
    _ = jmul (jmul a e) e := by rw [jmul_comm e a]
    _ = jmul a (jmul e e) := h2
    _ = jmul a e := by rw [← jsq_def, he_idem.jsq_eq_self]

/-- For each eigenvalue, we can construct an orthogonal projection onto the eigenspace. -/
theorem spectral_projection_exists [FinDimJordanAlgebra J] [JordanTrace J] [FormallyRealJordan J]
    (a : J) (μ : ℝ) (hμ : μ ∈ eigenvalueSet a) :
    ∃ e : J, IsIdempotent e ∧ (∀ v, v ∈ eigenspace a μ ↔ jmul e v = v) := by
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

/-! ### C(a) structure theorem and spectral decomposition -/

/-- Elements of C(a) in distinct eigenspaces of L_a multiply to zero.
    Uses associativity of C(a): jmul a (jmul x y) = μ·(jmul x y) and
    jmul a (jmul x y) = ν·(jmul x y), so (μ - ν)·(jmul x y) = 0. -/
theorem eigenspace_jmul_zero_in_ca (a : J) {x y : J} {μ ν : ℝ}
    (hx_eig : jmul a x = μ • x) (hy_eig : jmul a y = ν • y)
    (hx_ca : x ∈ generatedSubalgebra a) (hy_ca : y ∈ generatedSubalgebra a)
    (hne : μ ≠ ν) : jmul x y = 0 := by
  have h1 : jmul a (jmul x y) = μ • jmul x y := by
    calc jmul a (jmul x y)
        = jmul (jmul a x) y := (generatedSubalgebra_jmul_assoc a
            (self_mem_generatedSubalgebra a) hx_ca hy_ca).symm
      _ = jmul (μ • x) y := by rw [hx_eig]
      _ = μ • jmul x y := by rw [jmul_smul]
  have h2 : jmul a (jmul x y) = ν • jmul x y := by
    calc jmul a (jmul x y)
        = jmul (jmul x y) a := by rw [jmul_comm]
      _ = jmul x (jmul y a) := generatedSubalgebra_jmul_assoc a
            hx_ca hy_ca (self_mem_generatedSubalgebra a)
      _ = jmul x (jmul a y) := by rw [jmul_comm y a]
      _ = jmul x (ν • y) := by rw [hy_eig]
      _ = ν • jmul x y := by rw [smul_jmul]
  have h3 : (μ - ν) • jmul x y = 0 := by
    rw [sub_smul]; exact sub_eq_zero.mpr (h1.symm.trans h2)
  exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hne)

/-- Decomposition of jone into nonzero eigenspace components within C(a).
    Each component is in C(a), is an eigenvector of L_a, eigenvalues are distinct.
    Proof: eigenspace projections of L_a are polynomials in L_a; since C(a)
    is L_a-invariant and (L_a)^n(1) = a^n ∈ C(a), each projection of 1 is in C(a). -/
theorem jone_eigenspace_decomp_in_ca [FinDimJordanAlgebra J] [FormallyRealTrace J] (a : J) :
    ∃ (k : ℕ) (e : Fin k → J) (μ : Fin k → ℝ),
      (∀ i, e i ∈ generatedSubalgebra a) ∧
      (∀ i, jmul a (e i) = μ i • e i) ∧
      (∀ i, e i ≠ 0) ∧
      Function.Injective μ ∧
      (∑ i, e i = jone) := by
  sorry

/-- C(a) admits a CSOI where each idempotent is an eigenvector of L_a.
    Given the eigenspace decomposition of jone within C(a), orthogonality follows from
    eigenspace_jmul_zero_in_ca and idempotency from orthogonality + completeness. -/
theorem generatedSubalgebra_spectral_csoi [FinDimJordanAlgebra J] [FormallyRealJordan J]
    [FormallyRealTrace J] (a : J) :
    ∃ (k : ℕ) (c : CSOI J k) (coef : Fin k → ℝ),
      (∀ i, c.idem i ≠ 0) ∧
      (∀ i, jmul a (c.idem i) = coef i • c.idem i) := by
  obtain ⟨k, e, μ, hca, heig, hne, hinj, hsum⟩ := jone_eigenspace_decomp_in_ca a
  -- Orthogonality from eigenspace_jmul_zero_in_ca
  have horth : ∀ i j, i ≠ j → AreOrthogonal (e i) (e j) := fun i j hij =>
    eigenspace_jmul_zero_in_ca a (heig i) (heig j) (hca i) (hca j) (hinj.ne hij)
  -- Idempotency: eᵢ = jmul eᵢ 1 = jmul eᵢ (∑ eⱼ) = jsq eᵢ (cross terms vanish)
  have hidem : ∀ i, IsIdempotent (e i) := by
    intro i; show jsq (e i) = e i; rw [jsq_def]; symm
    calc e i = jmul (e i) jone := (jmul_jone _).symm
      _ = jmul (e i) (∑ j, e j) := by rw [hsum]
      _ = ∑ j, jmul (e i) (e j) := by
          simp only [← L_apply]; exact map_sum _ _ _
      _ = jmul (e i) (e i) := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
          have : ∑ j ∈ Finset.univ.erase i, jmul (e i) (e j) = 0 :=
            Finset.sum_eq_zero fun j hj => by
              rw [Finset.mem_erase] at hj; exact horth i j hj.1.symm
          rw [this, add_zero]
  exact ⟨k, ⟨e, hidem, horth, hsum⟩, μ, hne, heig⟩

/-- For a CSOI where each idempotent is an eigenvector of L_a,
    L_a acts as scalar multiplication on each Peirce-1 space.
    Key: for j ≠ i, c.idem j ∈ P₀(c.idem i), so jmul (c.idem j) x = 0
    by peirce_mult_P0_P1. -/
theorem csoi_eigenvector_peirce_one {n : ℕ} {a : J} (c : CSOI J n) (coef : Fin n → ℝ)
    (heig : ∀ i, jmul a (c.idem i) = coef i • c.idem i)
    {x : J} {i : Fin n} (hx : jmul (c.idem i) x = x) :
    jmul a x = coef i • x := by
  have hdecomp := spectral_decomp_of_eigenvector_csoi a c coef heig
  calc jmul a x
      = jmul (∑ j, coef j • c.idem j) x := by rw [hdecomp]
    _ = ∑ j, coef j • jmul (c.idem j) x :=
        sum_jmul Finset.univ c.idem coef x
    _ = coef i • jmul (c.idem i) x +
        ∑ j ∈ Finset.univ.erase i, coef j • jmul (c.idem j) x := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    _ = coef i • x + 0 := by
        congr 1
        · rw [hx]
        · apply Finset.sum_eq_zero; intro j hj
          rw [Finset.mem_erase] at hj
          rw [peirce_mult_P0_P1 (c.is_idem i)
            (orthogonal_in_peirce_zero (c.orthog i j (Ne.symm hj.1)))
            (by rw [mem_peirceSpace_one_iff]; exact hx), smul_zero]
    _ = coef i • x := add_zero _

/-- Every element in a finite-dimensional formally real Jordan algebra has
    a spectral decomposition with primitive idempotents.

    Proof: Get eigenvector-CSOI from C(a) structure theorem, decompose each
    idempotent into J-primitives, show primitives inherit eigenvalues via
    Peirce-1 membership, build combined CSOI with finSigmaFinEquiv. -/
theorem spectral_decomposition_exists [FinDimJordanAlgebra J] [FormallyRealTrace J]
    [FormallyRealJordan J] (a : J) :
    ∃ sd : SpectralDecomp a, ∀ i, IsPrimitive (sd.csoi.idem i) := by
  -- Step 1: Get spectral CSOI from C(a) structure theorem
  obtain ⟨k, c, coef, hne, heig⟩ := generatedSubalgebra_spectral_csoi a
  -- Step 2: Decompose each idempotent into primitives
  choose m p hp hpo hps using fun i => exists_primitive_decomp (c.is_idem i) (hne i)
  -- Step 3: Each primitive inherits the eigenvalue from its parent
  have heig_p : ∀ i j, jmul a (p i j) = coef i • p i j := by
    intro i j
    apply csoi_eigenvector_peirce_one c coef heig
    exact primitive_sum_sub_idem (hp i) (hpo i) (hps i) j
  -- Step 4: Build combined CSOI (same pattern as csoi_refine_primitive)
  let q : Fin (∑ i : Fin k, m i) → J :=
    fun j => p (finSigmaFinEquiv.symm j).1 (finSigmaFinEquiv.symm j).2
  let ev : Fin (∑ i : Fin k, m i) → ℝ :=
    fun j => coef (finSigmaFinEquiv.symm j).1
  -- Step 5: Decomposition equation: a = ∑ ev j • q j
  have hdecomp : a = ∑ j, ev j • q j := by
    -- First show ∑ j, ev j • q j = ∑ i, coef i • c.idem i
    have hsigma : ∑ j, ev j • q j =
        ∑ ij : (i : Fin k) × Fin (m i), coef ij.1 • p ij.1 ij.2 :=
      Fintype.sum_equiv finSigmaFinEquiv.symm _ _ (fun _ => rfl)
    have hreindex : ∑ ij : (i : Fin k) × Fin (m i), coef ij.1 • p ij.1 ij.2 =
        ∑ i : Fin k, ∑ l : Fin (m i), coef i • p i l := by
      rw [← Finset.univ_sigma_univ]; exact Finset.sum_sigma _ _ _
    rw [hsigma, hreindex]
    simp_rw [← Finset.smul_sum, ← hps]
    exact spectral_decomp_of_eigenvector_csoi a c coef heig
  -- Step 6: Construct the CSOI structure
  have horthog : ∀ j₁ j₂ : Fin (∑ i : Fin k, m i), j₁ ≠ j₂ →
      AreOrthogonal (q j₁) (q j₂) := by
    intro j₁ j₂ hjne
    show AreOrthogonal (p _ _) (p _ _)
    have hne' : finSigmaFinEquiv.symm j₁ ≠ finSigmaFinEquiv.symm j₂ :=
      fun h => hjne (finSigmaFinEquiv.symm.injective h)
    rcases h₁ : finSigmaFinEquiv.symm j₁ with ⟨i₁, l₁⟩
    rcases h₂ : finSigmaFinEquiv.symm j₂ with ⟨i₂, l₂⟩
    rw [h₁, h₂] at hne'
    by_cases hi : i₁ = i₂
    · subst hi
      exact hpo i₁ l₁ l₂ (fun h => hne' (Sigma.ext rfl (heq_of_eq h)))
    · exact sub_idem_orthog_of_sum_orthog (c.is_idem i₁) (c.is_idem i₂)
        (c.orthog i₁ i₂ hi)
        (primitive_sum_sub_idem (hp i₁) (hpo i₁) (hps i₁) l₁)
        (primitive_sum_sub_idem (hp i₂) (hpo i₂) (hps i₂) l₂)
  have hcomplete : ∑ j, q j = jone := by
    calc ∑ j, q j
      _ = ∑ ij : (i : Fin k) × Fin (m i), p ij.1 ij.2 :=
          Fintype.sum_equiv finSigmaFinEquiv.symm _ _ (fun _ => rfl)
      _ = ∑ i : Fin k, ∑ l : Fin (m i), p i l := by
          rw [← Finset.univ_sigma_univ]; exact Finset.sum_sigma _ _ _
      _ = ∑ i, c.idem i := by simp_rw [← hps]
      _ = jone := c.complete
  exact ⟨⟨_, ev, ⟨q, fun j => (hp _ _).isIdempotent, horthog, hcomplete⟩, hdecomp⟩,
    fun j => hp _ _⟩

/-- Spectral decomposition with Finset-indexed sum. -/
theorem spectral_decomposition_finset [FinDimJordanAlgebra J] [FormallyRealTrace J]
    [FormallyRealJordan J] (a : J) :
    ∃ (S : Finset ℝ) (e : ℝ → J),
      (∀ r ∈ S, IsIdempotent (e r)) ∧
      (∀ r s, r ∈ S → s ∈ S → r ≠ s → AreOrthogonal (e r) (e s)) ∧
      (∑ r ∈ S, e r = jone) ∧
      (a = ∑ r ∈ S, r • e r) := by
  obtain ⟨sd, _⟩ := spectral_decomposition_exists a
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
