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

For n + k + m ≥ 1, let N = 6 + n + k + m and H = ⟨g₁, g₂, g₃⟩ where:
- g₁ = (1 6 4 3 a₁...aₙ)
- g₂ = (1 2 4 5 b₁...bₖ)
- g₃ = (5 6 2 3 c₁...cₘ)

Then H = Aₙ if n, k, m are all odd, and H = Sₙ otherwise.

## Proof Overview

The proof combines five validated lemmas and one classical theorem:

1. **Transitivity (Lemma 5)**: H acts transitively on Ω via support graph connectivity
2. **Primitivity (Lemma 11)**: When n + k + m ≥ 1, H acts primitively on Ω
3. **3-Cycle Existence (Lemma 9)**: H contains a 3-cycle (from commutators)
4. **Jordan's Theorem (Lemma 12)**: Primitive + 3-cycle → H ≥ Aₙ
5. **Generator Parity (Lemma 14)**: sign(gᵢ) depends on tail length parity
6. **Classification (Lemma 15)**: H = Aₙ iff all generators even; H = Sₙ otherwise

## Reference

See `examples/lemmas/main_theorem.md` for the natural language proof.
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

/-- H contains a 3-cycle.

    This follows from Lemma 9: the product c₁₂ * c₁₃⁻¹ is a product of
    two disjoint 3-cycles in the base case. Using conjugation, we can
    extract individual 3-cycles from H. -/
theorem H_contains_threecycle (n k m : ℕ) :
    ∃ σ : Perm (Omega n k m), σ.IsThreeCycle ∧ σ ∈ H n k m := by
  -- Phase 2: Prove via embedding from base case or direct construction
  sorry

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

/-- Step 3: H contains a 3-cycle (Lemma 9) -/
theorem step3_threecycle (n k m : ℕ) :
    ∃ σ : Perm (Omega n k m), σ.IsThreeCycle ∧ σ ∈ H n k m :=
  H_contains_threecycle n k m

/-- Step 4: H ≥ Aₙ by Jordan's theorem (Lemma 12) -/
theorem step4_jordan (n k m : ℕ) (h : n + k + m ≥ 1) :
    alternatingGroup (Omega n k m) ≤ H n k m :=
  SignAnalysis.H_contains_alternating n k m h (step3_threecycle n k m)

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

/-- **Main Theorem: H = Aₙ when all generators are even**

    For n + k + m ≥ 1, if n, k, m are all odd, then H = Aₙ. -/
theorem main_theorem_alternating (n k m : ℕ) (hPrim : n + k + m ≥ 1)
    (hOdd : Odd n ∧ Odd k ∧ Odd m) :
    H n k m = alternatingGroup (Omega n k m) :=
  SignAnalysis.lemma15_H_eq_alternating n k m hPrim hOdd (step3_threecycle n k m)

/-- **Main Theorem: H = Sₙ when some generator is odd**

    For n + k + m ≥ 1, if not all of n, k, m are odd, then H = Sₙ. -/
theorem main_theorem_symmetric (n k m : ℕ) (hPrim : n + k + m ≥ 1)
    (hNotAllOdd : ¬(Odd n ∧ Odd k ∧ Odd m)) :
    H n k m = ⊤ :=
  SignAnalysis.lemma15_H_eq_symmetric n k m hPrim hNotAllOdd (step3_threecycle n k m)

/-- **Main Theorem: Classification of H**

    For n + k + m ≥ 1:
    - H = Aₙ ⟺ n, k, m are all odd
    - H = Sₙ ⟺ not all of n, k, m are odd -/
theorem main_theorem (n k m : ℕ) (hPrim : n + k + m ≥ 1) :
    (H n k m = alternatingGroup (Omega n k m) ↔ (Odd n ∧ Odd k ∧ Odd m)) ∧
    (H n k m = ⊤ ↔ ¬(Odd n ∧ Odd k ∧ Odd m)) :=
  SignAnalysis.lemma15_H_classification n k m hPrim (step3_threecycle n k m)

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
