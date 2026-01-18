/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Core
import AfTests.SignAnalysis.Lemma13

/-!
# Lemma 14: Generator Parity

Each generator g₁, g₂, g₃ has a specific sign depending on n, k, m:
- sign(g₁) = (-1)^{n+3}
- sign(g₂) = (-1)^{k+3}
- sign(g₃) = (-1)^{m+3}

## Main Results

* `lemma14_sign_g₁` - sign(g₁) = (-1)^{n+3}
* `lemma14_sign_g₂` - sign(g₂) = (-1)^{k+3}
* `lemma14_sign_g₃` - sign(g₃) = (-1)^{m+3}

## Proof Strategy

Each generator gᵢ is a single cycle of length 4 + (tail length).
By Lemma 13, an l-cycle has sign (-1)^{l-1}.
- g₁ is a (4+n)-cycle, so sign = (-1)^{4+n-1} = (-1)^{n+3}
- g₂ is a (4+k)-cycle, so sign = (-1)^{4+k-1} = (-1)^{k+3}
- g₃ is a (4+m)-cycle, so sign = (-1)^{4+m-1} = (-1)^{m+3}

## Reference

See `examples/lemmas/lemma14_generator_parity.md` for the natural language proof.
-/

namespace AfTests.SignAnalysis

open Equiv Equiv.Perm

-- ============================================
-- SECTION 1: GENERATORS ARE CYCLES
-- ============================================

/-- g₁ is a cycle (Phase 2: prove using formPerm properties) -/
theorem g₁_isCycle (n k m : ℕ) : (g₁ n k m).IsCycle := by
  sorry

/-- g₂ is a cycle (Phase 2: prove using formPerm properties) -/
theorem g₂_isCycle (n k m : ℕ) : (g₂ n k m).IsCycle := by
  sorry

/-- g₃ is a cycle (Phase 2: prove using formPerm properties) -/
theorem g₃_isCycle (n k m : ℕ) : (g₃ n k m).IsCycle := by
  sorry

-- ============================================
-- SECTION 2: SUPPORT CARDINALITY
-- ============================================

/-- The support of g₁ has cardinality 4 + n -/
theorem g₁_support_card (n k m : ℕ) :
    (g₁ n k m).support.card = 4 + n := by
  sorry

/-- The support of g₂ has cardinality 4 + k -/
theorem g₂_support_card (n k m : ℕ) :
    (g₂ n k m).support.card = 4 + k := by
  sorry

/-- The support of g₃ has cardinality 4 + m -/
theorem g₃_support_card (n k m : ℕ) :
    (g₃ n k m).support.card = 4 + m := by
  sorry

-- ============================================
-- SECTION 3: MAIN THEOREMS
-- ============================================

/-- **Lemma 14a: Sign of g₁**

    sign(g₁) = (-1)^{n+3}

    Proof: g₁ is a cycle of length 4 + n.
    By Lemma 13, sign = (-1)^{(4+n)-1} = (-1)^{n+3}. -/
theorem lemma14_sign_g₁ (n k m : ℕ) :
    Perm.sign (g₁ n k m) = (-1 : ℤˣ) ^ (n + 3) := by
  have hCycle := g₁_isCycle n k m
  have hCard := g₁_support_card n k m
  rw [lemma13_cycle_sign hCycle (by omega : (g₁ n k m).support.card ≥ 1)]
  rw [hCard]
  congr 1
  omega

/-- **Lemma 14b: Sign of g₂**

    sign(g₂) = (-1)^{k+3}

    Proof: g₂ is a cycle of length 4 + k.
    By Lemma 13, sign = (-1)^{(4+k)-1} = (-1)^{k+3}. -/
theorem lemma14_sign_g₂ (n k m : ℕ) :
    Perm.sign (g₂ n k m) = (-1 : ℤˣ) ^ (k + 3) := by
  have hCycle := g₂_isCycle n k m
  have hCard := g₂_support_card n k m
  rw [lemma13_cycle_sign hCycle (by omega : (g₂ n k m).support.card ≥ 1)]
  rw [hCard]
  congr 1
  omega

/-- **Lemma 14c: Sign of g₃**

    sign(g₃) = (-1)^{m+3}

    Proof: g₃ is a cycle of length 4 + m.
    By Lemma 13, sign = (-1)^{(4+m)-1} = (-1)^{m+3}. -/
theorem lemma14_sign_g₃ (n k m : ℕ) :
    Perm.sign (g₃ n k m) = (-1 : ℤˣ) ^ (m + 3) := by
  have hCycle := g₃_isCycle n k m
  have hCard := g₃_support_card n k m
  rw [lemma13_cycle_sign hCycle (by omega : (g₃ n k m).support.card ≥ 1)]
  rw [hCard]
  congr 1
  omega

-- ============================================
-- SECTION 4: PARITY COROLLARIES
-- ============================================

/-- g₁ is an even permutation iff n is odd -/
theorem g₁_even_iff_n_odd (n k m : ℕ) :
    Perm.sign (g₁ n k m) = 1 ↔ Odd n := by
  rw [lemma14_sign_g₁]
  sorry  -- Phase 2: prove parity equivalence

/-- g₂ is an even permutation iff k is odd -/
theorem g₂_even_iff_k_odd (n k m : ℕ) :
    Perm.sign (g₂ n k m) = 1 ↔ Odd k := by
  rw [lemma14_sign_g₂]
  sorry  -- Phase 2: prove parity equivalence

/-- g₃ is an even permutation iff m is odd -/
theorem g₃_even_iff_m_odd (n k m : ℕ) :
    Perm.sign (g₃ n k m) = 1 ↔ Odd m := by
  rw [lemma14_sign_g₃]
  sorry  -- Phase 2: prove parity equivalence

-- ============================================
-- SECTION 5: ALL GENERATORS EVEN IFF ALL ODD
-- ============================================

/-- All three generators are even permutations iff n, k, m are all odd -/
theorem all_generators_even_iff (n k m : ℕ) :
    (Perm.sign (g₁ n k m) = 1 ∧ Perm.sign (g₂ n k m) = 1 ∧ Perm.sign (g₃ n k m) = 1) ↔
    (Odd n ∧ Odd k ∧ Odd m) := by
  rw [g₁_even_iff_n_odd, g₂_even_iff_k_odd, g₃_even_iff_m_odd]

end AfTests.SignAnalysis
