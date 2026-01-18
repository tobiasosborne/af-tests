/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Core
import AfTests.ThreeCycle.Lemma06
import AfTests.ThreeCycle.Lemma07
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# Lemma 9: 3-Cycle Extraction

Extract 3-cycles from products of commutators. We compute c₁₂ * c₁₃⁻¹ where:
- c₁₂ = [g₁, g₂] (from Lemma 6)
- c₁₃ = [g₁, g₃] (from Lemma 7)

## Main Results

* `c₁₂_times_c₁₃_inv` - The product c₁₂ * c₁₃⁻¹
* `c₁₂_times_c₁₃_inv_base_case_eq` - In base case: c₁₂ * c₁₃⁻¹ = (0 1 5)(2 3 4)
* `c₁₂_times_c₁₃_inv_mem_H` - The product is in H

## Proof Strategy

Direct computation using `native_decide` for the base case n=k=m=0.
The product c₁₂ * c₁₃⁻¹ is a product of two disjoint 3-cycles.

## Reference

See `examples/lemmas/lemma09_3cycle_extraction.md` for the natural language proof.
-/

open Equiv Perm

-- ============================================
-- DEFINITIONS
-- ============================================

/-- c₁₂ = [g₁, g₂] from Lemma 6 -/
abbrev c₁₂ (n k m : ℕ) : Perm (Omega n k m) := commutator_g₁_g₂ n k m

/-- c₁₃ = [g₁, g₃] from Lemma 7 -/
abbrev c₁₃ (n k m : ℕ) : Perm (Omega n k m) := commutator_g₁_g₃ n k m

/-- The product c₁₂ * c₁₃⁻¹ -/
def c₁₂_times_c₁₃_inv (n k m : ℕ) : Perm (Omega n k m) :=
  c₁₂ n k m * (c₁₃ n k m)⁻¹

-- ============================================
-- BASE CASE: n = k = m = 0 (S₆)
-- ============================================

/-- c₁₂ * c₁₃⁻¹ in base case equals (0 1 5)(2 3 4).
    This is a product of two disjoint 3-cycles. -/
theorem c₁₂_times_c₁₃_inv_base_case_eq :
    c₁₂_times_c₁₃_inv 0 0 0 = c[0, 1, 5] * c[2, 3, 4] := by
  native_decide

-- ============================================
-- ELEMENT-WISE VERIFICATION
-- ============================================

/-- Product action on element 0: 0 → 1 -/
theorem product_action_0 : c₁₂_times_c₁₃_inv 0 0 0 0 = 1 := by native_decide

/-- Product action on element 1: 1 → 5 -/
theorem product_action_1 : c₁₂_times_c₁₃_inv 0 0 0 1 = 5 := by native_decide

/-- Product action on element 2: 2 → 3 -/
theorem product_action_2 : c₁₂_times_c₁₃_inv 0 0 0 2 = 3 := by native_decide

/-- Product action on element 3: 3 → 4 -/
theorem product_action_3 : c₁₂_times_c₁₃_inv 0 0 0 3 = 4 := by native_decide

/-- Product action on element 4: 4 → 2 -/
theorem product_action_4 : c₁₂_times_c₁₃_inv 0 0 0 4 = 2 := by native_decide

/-- Product action on element 5: 5 → 0 -/
theorem product_action_5 : c₁₂_times_c₁₃_inv 0 0 0 5 = 0 := by native_decide

/-- First 3-cycle (0 1 5) closes: 0 → 1 → 5 → 0 -/
theorem first_cycle_closes :
    c₁₂_times_c₁₃_inv 0 0 0 (c₁₂_times_c₁₃_inv 0 0 0 (c₁₂_times_c₁₃_inv 0 0 0 0)) = 0 := by
  native_decide

/-- Second 3-cycle (2 3 4) closes: 2 → 3 → 4 → 2 -/
theorem second_cycle_closes :
    c₁₂_times_c₁₃_inv 0 0 0 (c₁₂_times_c₁₃_inv 0 0 0 (c₁₂_times_c₁₃_inv 0 0 0 2)) = 2 := by
  native_decide

-- ============================================
-- 3-CYCLE COMPONENTS
-- ============================================

/-- The first component c[0, 1, 5] -/
def first_3cycle_L9 : Perm (Omega 0 0 0) := c[0, 1, 5]

/-- The second component c[2, 3, 4] -/
def second_3cycle_L9 : Perm (Omega 0 0 0) := c[2, 3, 4]

/-- The two 3-cycles are disjoint -/
theorem cycles_L9_disjoint :
    Disjoint (first_3cycle_L9).support (second_3cycle_L9).support := by
  native_decide

-- ============================================
-- MEMBERSHIP IN H
-- ============================================

/-- c₁₂ * c₁₃⁻¹ is in H since both c₁₂ and c₁₃ are in H -/
theorem c₁₂_times_c₁₃_inv_mem_H : c₁₂_times_c₁₃_inv 0 0 0 ∈ H 0 0 0 := by
  unfold c₁₂_times_c₁₃_inv c₁₂ c₁₃
  apply Subgroup.mul_mem
  · exact commutator_g₁_g₂_mem_H
  · exact Subgroup.inv_mem _ commutator_g₁_g₃_mem_H

/-- The 3-cycle c[0, 1, 5] is in H -/
theorem first_3cycle_L9_mem_H : first_3cycle_L9 ∈ H 0 0 0 := by
  sorry -- Requires extraction from product of disjoint cycles

/-- The 3-cycle c[2, 3, 4] is in H -/
theorem second_3cycle_L9_mem_H : second_3cycle_L9 ∈ H 0 0 0 := by
  sorry -- Requires extraction from product of disjoint cycles

-- ============================================
-- 3-CYCLE PROPERTIES
-- ============================================

/-- The product c₁₂ * c₁₃⁻¹ has order 3 (since it's a product of disjoint 3-cycles) -/
theorem c₁₂_times_c₁₃_inv_cubed :
    (c₁₂_times_c₁₃_inv 0 0 0) ^ 3 = 1 := by
  native_decide

/-- H contains elements with 3-cycles -/
theorem H_contains_3cycle_product :
    ∃ σ ∈ H 0 0 0, σ = c[0, 1, 5] * c[2, 3, 4] :=
  ⟨c₁₂_times_c₁₃_inv 0 0 0, c₁₂_times_c₁₃_inv_mem_H, c₁₂_times_c₁₃_inv_base_case_eq⟩
