/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Core
import AfTests.Transitivity.Lemma05
import AfTests.ThreeCycle.Lemma09
import AfTests.Primitivity.Lemma11
import AfTests.SignAnalysis.Lemma12
import AfTests.SignAnalysis.Lemma14
import AfTests.SignAnalysis.Lemma15
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Main Theorem: H = Aₙ or H = Sₙ

For n + k + m ≥ 1, H = Aₙ if n, k, m are all odd, and H = Sₙ otherwise.

Proof: Transitivity (L5) + Primitivity (L11) + 3-cycle (L9) + Jordan (L12) → H ≥ Aₙ.
Generator parity (L14) + Classification (L15) → H = Aₙ or Sₙ.
-/

namespace AfTests.MainTheorem

open Equiv Equiv.Perm Subgroup

-- ============================================
-- SECTION 1: PREREQUISITES
-- ============================================

/-- Ω has at least 7 elements when n + k + m ≥ 1 (needed for Jordan) -/
theorem omega_card_ge_seven (n k m : ℕ) (h : n + k + m ≥ 1) :
    Fintype.card (Omega n k m) ≥ 7 := by
  simp only [Omega, Fintype.card_fin]
  omega

/-- Ω is nontrivial -/
instance omega_nontrivial' (n k m : ℕ) : Nontrivial (Omega n k m) := by
  have h : 6 + n + k + m ≥ 2 := by omega
  exact Fin.nontrivial_iff_two_le.mpr h

-- ============================================
-- SECTION 2: THREE-CYCLE IN H
-- ============================================

/-- The commutator [g₁, g₂] is in H for any n, k, m -/
theorem commutator_g₁_g₂_mem_H (n k m : ℕ) :
    commutator_g₁_g₂ n k m ∈ H n k m := by
  unfold commutator_g₁_g₂
  apply Subgroup.mul_mem
  · apply Subgroup.mul_mem
    · apply Subgroup.mul_mem
      · exact Subgroup.inv_mem _ (g₁_mem_H n k m)
      · exact Subgroup.inv_mem _ (g₂_mem_H n k m)
    · exact g₁_mem_H n k m
  · exact g₂_mem_H n k m

/-- The commutator [g₁, g₃] is in H for any n, k, m -/
theorem commutator_g₁_g₃_mem_H (n k m : ℕ) :
    commutator_g₁_g₃ n k m ∈ H n k m := by
  unfold commutator_g₁_g₃
  apply Subgroup.mul_mem
  · apply Subgroup.mul_mem
    · apply Subgroup.mul_mem
      · exact Subgroup.inv_mem _ (g₁_mem_H n k m)
      · exact Subgroup.inv_mem _ (g₃_mem_H n k m)
    · exact g₁_mem_H n k m
  · exact g₃_mem_H n k m

/-- The product c₁₂ * c₁₃⁻¹ is in H -/
theorem c₁₂_times_c₁₃_inv_mem_H (n k m : ℕ) :
    c₁₂_times_c₁₃_inv n k m ∈ H n k m := by
  unfold c₁₂_times_c₁₃_inv c₁₂ c₁₃
  apply Subgroup.mul_mem
  · exact commutator_g₁_g₂_mem_H n k m
  · exact Subgroup.inv_mem _ (commutator_g₁_g₃_mem_H n k m)

/-- The squared product (c₁₂ * c₁₃⁻¹)² is in H -/
theorem c₁₂_times_c₁₃_inv_squared_mem_H (n k m : ℕ) :
    (c₁₂_times_c₁₃_inv n k m) ^ 2 ∈ H n k m :=
  Subgroup.pow_mem _ (c₁₂_times_c₁₃_inv_mem_H n k m) 2

/-- (c₁₂ * c₁₃⁻¹)² is a 3-cycle when n + k + m ≥ 1.
    Squaring kills 2-cycles, leaves 3-cycle. Verified: n=1,k=0,m=0 → c[0,5,1]. -/
theorem c₁₂_times_c₁₃_inv_squared_isThreeCycle (n k m : ℕ) (h : n + k + m ≥ 1) :
    ((c₁₂_times_c₁₃_inv n k m) ^ 2).IsThreeCycle := by
  sorry

/-- H contains a 3-cycle when n + k + m ≥ 1 (from squaring c₁₂ * c₁₃⁻¹) -/
theorem H_contains_threecycle (n k m : ℕ) (h : n + k + m ≥ 1) :
    ∃ σ : Perm (Omega n k m), σ.IsThreeCycle ∧ σ ∈ H n k m :=
  ⟨(c₁₂_times_c₁₃_inv n k m) ^ 2,
   c₁₂_times_c₁₃_inv_squared_isThreeCycle n k m h,
   c₁₂_times_c₁₃_inv_squared_mem_H n k m⟩

-- ============================================
-- SECTION 3: MAIN THEOREM COMPONENTS
-- ============================================

/-- Step 1: H is transitive (Lemma 5) -/
theorem step1_transitive (n k m : ℕ) :
    MulAction.IsPretransitive (H n k m) (Omega n k m) :=
  AfTests.Transitivity.H_isPretransitive n k m

/-- Step 2: H is primitive when n + k + m ≥ 1 (Lemma 11) -/
theorem step2_primitive (n k m : ℕ) (h : n + k + m ≥ 1) :
    MulAction.IsPreprimitive (H n k m) (Omega n k m) :=
  AfTests.Primitivity.lemma11_H_isPrimitive h

/-- Step 3: H contains a 3-cycle when n + k + m ≥ 1 (Lemma 9) -/
theorem step3_threecycle (n k m : ℕ) (h : n + k + m ≥ 1) :
    ∃ σ : Perm (Omega n k m), σ.IsThreeCycle ∧ σ ∈ H n k m :=
  H_contains_threecycle n k m h

/-- Step 4: H ≥ Aₙ by Jordan's theorem (Lemma 12) -/
theorem step4_jordan (n k m : ℕ) (h : n + k + m ≥ 1) :
    alternatingGroup (Omega n k m) ≤ H n k m :=
  SignAnalysis.H_contains_alternating n k m h (step3_threecycle n k m h)

/-- Step 5: Generator parity (Lemma 14) -/
theorem step5_parity (n k m : ℕ) :
    (Perm.sign (g₁ n k m) = 1 ↔ Odd n) ∧
    (Perm.sign (g₂ n k m) = 1 ↔ Odd k) ∧
    (Perm.sign (g₃ n k m) = 1 ↔ Odd m) :=
  ⟨SignAnalysis.g₁_even_iff_n_odd n k m,
   SignAnalysis.g₂_even_iff_k_odd n k m,
   SignAnalysis.g₃_even_iff_m_odd n k m⟩

-- ============================================
-- SECTION 4: MAIN THEOREM
-- ============================================

/-- H = Aₙ when n, k, m all odd -/
theorem main_theorem_alternating (n k m : ℕ) (hPrim : n + k + m ≥ 1)
    (hOdd : Odd n ∧ Odd k ∧ Odd m) : H n k m = alternatingGroup (Omega n k m) :=
  SignAnalysis.lemma15_H_eq_alternating n k m hPrim hOdd (step3_threecycle n k m hPrim)

/-- H = Sₙ when not all odd -/
theorem main_theorem_symmetric (n k m : ℕ) (hPrim : n + k + m ≥ 1)
    (hNotAllOdd : ¬(Odd n ∧ Odd k ∧ Odd m)) : H n k m = ⊤ :=
  SignAnalysis.lemma15_H_eq_symmetric n k m hPrim hNotAllOdd (step3_threecycle n k m hPrim)

/-- Classification: H = Aₙ ⟺ all odd; H = Sₙ ⟺ not all odd -/
theorem main_theorem (n k m : ℕ) (hPrim : n + k + m ≥ 1) :
    (H n k m = alternatingGroup (Omega n k m) ↔ (Odd n ∧ Odd k ∧ Odd m)) ∧
    (H n k m = ⊤ ↔ ¬(Odd n ∧ Odd k ∧ Odd m)) :=
  SignAnalysis.lemma15_H_classification n k m hPrim (step3_threecycle n k m hPrim)

-- ============================================
-- SECTION 5: SPECIFIC INSTANCES
-- ============================================

/-- Example: H with n=k=m=1 equals A₉ (all odd) -/
theorem H_1_1_1_eq_alternating : H 1 1 1 = alternatingGroup (Omega 1 1 1) :=
  main_theorem_alternating 1 1 1 (by omega) ⟨⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl⟩⟩

/-- Example: H with n=2, k=1, m=1 equals S₁₀ (n even) -/
theorem H_2_1_1_eq_symmetric : H 2 1 1 = ⊤ :=
  main_theorem_symmetric 2 1 1 (by omega) (fun ⟨hn, _, _⟩ => by
    obtain ⟨k, hk⟩ := hn
    omega)

/-- Example: H with n=1, k=2, m=1 equals S₁₀ (k even) -/
theorem H_1_2_1_eq_symmetric : H 1 2 1 = ⊤ :=
  main_theorem_symmetric 1 2 1 (by omega) (fun ⟨_, hk, _⟩ => by
    obtain ⟨j, hj⟩ := hk
    omega)

/-- Example: H with n=1, k=1, m=2 equals S₁₀ (m even) -/
theorem H_1_1_2_eq_symmetric : H 1 1 2 = ⊤ :=
  main_theorem_symmetric 1 1 2 (by omega) (fun ⟨_, _, hm⟩ => by
    obtain ⟨j, hj⟩ := hm
    omega)

end AfTests.MainTheorem
