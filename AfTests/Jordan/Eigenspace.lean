/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Peirce
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Eigenspaces in Jordan Algebras

For a Jordan algebra element `a`, we define eigenspaces of the left multiplication
operator `L_a`. This generalizes the Peirce decomposition (which uses idempotents).

## Main definitions

* `JordanAlgebra.eigenspace` - The μ-eigenspace of L_a
* `JordanAlgebra.IsEigenvalue` - μ is an eigenvalue of a
* `JordanAlgebra.eigenvalueSet` - The set of eigenvalues

## Main results

* `eigenspace_eq_peirceSpace` - Eigenspace matches PeirceSpace
* `eigenvalueSet_jone` - The eigenvalues of 1 are {1}
-/

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-! ### Eigenspace Definition -/

/-- The μ-eigenspace of left multiplication by a.
This is the set of elements v such that a ∘ v = μ • v. -/
def eigenspace (a : J) (μ : ℝ) : Submodule ℝ J :=
  Module.End.eigenspace (L a) μ

theorem mem_eigenspace_iff (a : J) (μ : ℝ) (v : J) :
    v ∈ eigenspace a μ ↔ jmul a v = μ • v := by
  rw [eigenspace, Module.End.mem_eigenspace_iff, L_apply]

theorem eigenspace_zero (a : J) : eigenspace a 0 = LinearMap.ker (L a) := by
  rw [eigenspace, Module.End.eigenspace_zero]

/-- Eigenspaces match Peirce spaces (same definition, different names). -/
theorem eigenspace_eq_peirceSpace (a : J) (μ : ℝ) :
    eigenspace a μ = PeirceSpace a μ := by
  ext v
  rw [mem_eigenspace_iff, mem_peirceSpace_iff]

/-! ### Eigenvalue and Spectrum Definitions -/

/-- μ is an eigenvalue of a if the μ-eigenspace is nontrivial. -/
def IsEigenvalue (a : J) (μ : ℝ) : Prop :=
  Module.End.HasEigenvalue (L a) μ

theorem isEigenvalue_iff (a : J) (μ : ℝ) :
    IsEigenvalue a μ ↔ eigenspace a μ ≠ ⊥ := by
  rw [IsEigenvalue, Module.End.hasEigenvalue_iff, eigenspace]

theorem isEigenvalue_iff_exists_eigenvector (a : J) (μ : ℝ) :
    IsEigenvalue a μ ↔ ∃ v ≠ 0, jmul a v = μ • v := by
  rw [isEigenvalue_iff]
  constructor
  · intro h
    rw [Submodule.ne_bot_iff] at h
    obtain ⟨v, hv, hvne⟩ := h
    exact ⟨v, hvne, (mem_eigenspace_iff a μ v).mp hv⟩
  · intro ⟨v, hvne, hv⟩
    rw [Submodule.ne_bot_iff]
    exact ⟨v, (mem_eigenspace_iff a μ v).mpr hv, hvne⟩

/-- The eigenvalue set of a (set of eigenvalues of L_a). -/
def eigenvalueSet (a : J) : Set ℝ := {μ | IsEigenvalue a μ}

theorem mem_eigenvalueSet_iff (a : J) (μ : ℝ) :
    μ ∈ eigenvalueSet a ↔ IsEigenvalue a μ := Iff.rfl

/-! ### Basic Eigenvalue Properties -/

/-- The eigenspace of jone at 1 is the whole algebra. -/
theorem eigenspace_jone_one : eigenspace (jone : J) 1 = ⊤ := by
  ext v
  simp [mem_eigenspace_iff, jone_jmul, one_smul]

variable [Nontrivial J]

/-- 1 is an eigenvalue of jone (the identity element). -/
theorem isEigenvalue_jone_one : IsEigenvalue (jone : J) 1 := by
  rw [isEigenvalue_iff_exists_eigenvector]
  refine ⟨jone, jone_ne_zero, ?_⟩
  simp [jone_jmul, one_smul]

/-- The eigenvalue set of jone is exactly {1}. -/
theorem eigenvalueSet_jone : eigenvalueSet (jone : J) = {1} := by
  ext μ
  simp only [mem_eigenvalueSet_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    rw [isEigenvalue_iff_exists_eigenvector] at h
    obtain ⟨v, hvne, hv⟩ := h
    -- jone ∘ v = v, so μ • v = v
    simp only [jone_jmul] at hv
    -- v = μ • v means (1 - μ) • v = 0
    have hsub : (1 - μ) • v = 0 := by
      calc (1 - μ) • v = v - μ • v := by rw [sub_smul, one_smul]
        _ = 0 := by rw [← hv, sub_self]
    -- Since v ≠ 0, we have 1 - μ = 0
    have h2 : (1 - μ) = 0 := by
      by_contra h
      have hvinv : v = 0 := by
        rw [← one_smul ℝ v, ← inv_mul_cancel₀ h, mul_smul, hsub, smul_zero]
      exact hvne hvinv
    linarith
  · intro h
    rw [h]
    exact isEigenvalue_jone_one

/-! ### Connection to Peirce Decomposition -/

omit [Nontrivial J] in
/-- For an idempotent, eigenvalues are restricted to {0, 1/2, 1}.
This is a consequence of the Peirce polynomial identity. -/
theorem idempotent_eigenvalues_subset (e : J) (he : IsIdempotent e) :
    eigenvalueSet e ⊆ {0, (1:ℝ)/2, 1} := by
  intro μ hμ
  rw [mem_eigenvalueSet_iff, isEigenvalue_iff_exists_eigenvector] at hμ
  obtain ⟨v, hvne, hv⟩ := hμ
  -- For an eigenvector v with L_e(v) = μv, iterating gives L_e^n(v) = μ^n v
  have hL2 : jmul e (jmul e v) = μ^2 • v := by
    calc jmul e (jmul e v)
      = jmul e (μ • v) := by rw [hv]
      _ = μ • jmul e v := by rw [smul_jmul]
      _ = μ • (μ • v) := by rw [hv]
      _ = μ^2 • v := by rw [smul_smul]; ring_nf
  have hL3 : jmul e (jmul e (jmul e v)) = μ^3 • v := by
    calc jmul e (jmul e (jmul e v))
      = jmul e (μ^2 • v) := by rw [hL2]
      _ = μ^2 • jmul e v := by rw [smul_jmul]
      _ = μ^2 • (μ • v) := by rw [hv]
      _ = μ^3 • v := by rw [smul_smul]; ring_nf
  -- The Peirce polynomial identity gives 2L³ - 3L² + L = 0
  have hpeirce := peirce_polynomial_identity he
  have happ : (L e ∘ₗ (L e - (1/2 : ℝ) • LinearMap.id) ∘ₗ (L e - LinearMap.id)) v = 0 := by
    rw [hpeirce]; simp
  -- Expanding the composition step by step
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, L_apply] at happ
  -- happ: jmul e (jmul e (jmul e v - v) - (1/2) • (jmul e v - v)) = 0
  -- Substitute jmul e v = μ • v
  rw [hv] at happ
  -- happ: jmul e (jmul e (μ • v - v) - (1/2) • (μ • v - v)) = 0
  -- Simplify: μ • v - v = (μ - 1) • v
  have sub1 : μ • v - v = (μ - 1) • v := by rw [sub_smul, one_smul]
  rw [sub1] at happ
  -- jmul e ((μ - 1) • v) = (μ - 1) • jmul e v = (μ - 1) • (μ • v) = ((μ - 1) * μ) • v
  have jmul1 : jmul e ((μ - 1) • v) = ((μ - 1) * μ) • v := by
    rw [smul_jmul, hv, smul_smul]
  rw [jmul1] at happ
  -- Now: jmul e (((μ-1)*μ) • v - (1/2) • (μ-1) • v) = 0
  -- Simplify the inner expression
  have inner : ((μ - 1) * μ) • v - (1/2 : ℝ) • (μ - 1) • v =
               ((μ - 1) * μ - (1/2) * (μ - 1)) • v := by
    rw [smul_smul, ← sub_smul]
  rw [inner] at happ
  -- jmul e (scalar • v) = scalar • jmul e v = (scalar * μ) • v
  have jmul2 : jmul e (((μ - 1) * μ - (1/2 : ℝ) * (μ - 1)) • v) =
               (((μ - 1) * μ - (1/2 : ℝ) * (μ - 1)) * μ) • v := by
    rw [smul_jmul, hv, smul_smul]
  rw [jmul2] at happ
  -- Now happ: (((μ-1)*μ - (1/2)*(μ-1)) * μ) • v = 0
  -- The scalar is ((μ-1)*μ - (1/2)*(μ-1)) * μ = (μ-1)*(μ - 1/2)*μ = μ*(μ-1)*(μ-1/2)
  have poly : μ * (μ - 1) * (μ - 1/2) = 0 := by
    by_contra hpoly
    -- The scalar in happ equals μ*(μ-1)*(μ-1/2)
    have hfactor : ((μ - 1) * μ - (1/2 : ℝ) * (μ - 1)) * μ = μ * (μ - 1) * (μ - 1/2) := by ring
    rw [hfactor] at happ
    rw [smul_eq_zero] at happ
    cases happ with
    | inl h => exact absurd h hpoly
    | inr h => exact hvne h
  -- poly: μ * (μ - 1) * (μ - 1/2) = 0
  -- Factor: either μ * (μ - 1) = 0, or (μ - 1/2) = 0
  rcases mul_eq_zero.mp poly with h | hμhalf
  · -- h: μ * (μ - 1) = 0, so μ = 0 or μ = 1
    rcases mul_eq_zero.mp h with hμ0 | hμ1
    · simp [hμ0]
    · have hμeq : μ = 1 := sub_eq_zero.mp hμ1
      simp [hμeq]
  · -- hμhalf: μ - 1/2 = 0, so μ = 1/2
    have hμeq : μ = 1/2 := sub_eq_zero.mp hμhalf
    simp [hμeq]

end JordanAlgebra
