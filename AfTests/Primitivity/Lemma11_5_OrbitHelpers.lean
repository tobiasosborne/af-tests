/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Primitivity.Lemma11_5_OrbitHelpers_Core
import AfTests.Primitivity.Lemma11_5_OrbitHelpers_TailB
import AfTests.Primitivity.Lemma11_5_OrbitHelpers_TailC

/-!
# Orbit Helpers Aggregator

Re-exports helpers from Core, TailB, TailC, plus additional lemmas for orbit analysis.
-/

open Equiv Equiv.Perm Set OrbitCore OrbitTailB OrbitTailC

variable {n k m : ℕ}

/-- g₁^j fixes element 1 for integer j -/
theorem g₁_zpow_fixes_elem1 (j : ℤ) :
    (g₁ n k m ^ j) (⟨1, by omega⟩ : Omega n k m) = ⟨1, by omega⟩ := by
  have hFix : g₁ n k m (⟨1, by omega⟩ : Omega n k m) = ⟨1, by omega⟩ := g₁_fixes_elem1'
  exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hFix j

/-- Element outside supp(g₁) is either 1, 4, tailB, or tailC -/
theorem elem_not_in_support_g₁_cases (x : Omega n k m)
    (hx : x ∉ (g₁ n k m).support) :
    x.val = 1 ∨ x.val = 4 ∨ isTailB x ∨ isTailC x := by
  rcases Omega.partition x with hCore | hA | hB | hC
  · simp only [isCore] at hCore
    have hCases : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 ∨ x.val = 3 ∨ x.val = 4 ∨ x.val = 5 :=
      by omega
    rcases hCases with h0 | h1 | h2 | h3 | h4 | h5
    · exfalso; have heq : x = ⟨0, by omega⟩ := Fin.ext h0
      rw [heq] at hx; exact hx elem0_in_support_g₁
    · left; exact h1
    · exfalso; have heq : x = ⟨2, by omega⟩ := Fin.ext h2
      rw [heq] at hx; exact hx elem2_in_support_g₁'
    · exfalso; have heq : x = ⟨3, by omega⟩ := Fin.ext h3
      rw [heq] at hx; exact hx elem3_in_support_g₁
    · right; left; exact h4
    · exfalso; have heq : x = ⟨5, by omega⟩ := Fin.ext h5
      rw [heq] at hx; exact hx elem5_in_support_g₁
  · exfalso
    simp only [isTailA] at hA
    have hi : x.val - 6 < n := by have := x.isLt; omega
    have hx_supp : x ∈ (g₁ n k m).support := by
      convert tailA_in_support_g₁ (⟨x.val - 6, hi⟩ : Fin n) using 1
      simp only [Fin.ext_iff]; omega
    exact hx hx_supp
  · right; right; left; exact hB
  · right; right; right; exact hC

/-- g₂ applied to element outside supp(g₁) never gives 6 (needs n ≥ 1) -/
theorem g₂_image_not_6 (hn : n ≥ 1) (y : Omega n k m)
    (hy : y.val = 1 ∨ y.val = 4 ∨ isTailB y ∨ isTailC y) :
    (g₂ n k m y).val ≠ 6 := by
  rcases hy with h1 | h4 | hB | hC
  · have heq : y = ⟨1, by omega⟩ := Fin.ext h1
    rw [heq, g₂_elem1_eq_elem3]; simp
  · have heq : y = ⟨4, by omega⟩ := Fin.ext h4
    rw [heq, g₂_elem4_eq_elem0']; simp
  · rcases g₂_tailB_to_tailB_or_1 y hB with hB' | h1'
    · simp only [isTailB] at hB'; omega
    · rw [h1']; simp
  · have hFix := g₂_fixes_tailC y hC
    rw [hFix]; simp only [isTailC] at hC; omega

/-- g₁^j preserves tailC elements for integer j (since g₁ fixes tailC) -/
theorem g₁_zpow_fixes_tailC (j : ℤ) (x : Omega n k m) (hx : isTailC x) :
    (g₁ n k m ^ j) x = x := by
  have hFix : g₁ n k m x = x := g₁_fixes_tailC x hx
  exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hFix j

/-- g₁⁻²(0) is not in {1} ∪ tailB ∪ tailC (used for j≤-3 case) -/
theorem g₁_inv2_elem0_not_fixed_region :
    let x := (g₁ n k m ^ (2 : ℕ)).symm (⟨0, by omega⟩ : Omega n k m)
    x.val ≠ 1 ∧ ¬isTailB x ∧ ¬isTailC x := by
  -- Key: If y is fixed by g₁, then g₁²(y) = y, so y ≠ g₁⁻²(0) since g₁²(g₁⁻²(0)) = 0
  set x := (g₁ n k m ^ (2 : ℕ)).symm (⟨0, by omega⟩ : Omega n k m) with hx_def
  have hx_apply : (g₁ n k m ^ (2 : ℕ)) x = ⟨0, by omega⟩ :=
    (g₁ n k m ^ (2 : ℕ)).apply_symm_apply _
  constructor
  · -- x.val ≠ 1
    intro h
    have heq : x = ⟨1, by omega⟩ := Fin.ext h
    rw [heq] at hx_apply
    have h1_fixed : (g₁ n k m ^ (2 : ℕ)) (⟨1, by omega⟩ : Omega n k m) = ⟨1, by omega⟩ := by
      simp only [pow_two, Equiv.Perm.coe_mul, Function.comp_apply]
      rw [g₁_fixes_elem1', g₁_fixes_elem1']
    simp only [Fin.ext_iff] at hx_apply h1_fixed; omega
  constructor
  · -- ¬isTailB x
    intro hB
    have hB_fixed : (g₁ n k m ^ (2 : ℕ)) x = x := by
      simp only [pow_two, Equiv.Perm.coe_mul, Function.comp_apply]
      rw [g₁_fixes_tailB _ hB, g₁_fixes_tailB _ hB]
    rw [hB_fixed] at hx_apply
    simp only [isTailB, Fin.ext_iff] at hB hx_apply; omega
  · -- ¬isTailC x
    intro hC
    have hC_fixed : (g₁ n k m ^ (2 : ℕ)) x = x := by
      simp only [pow_two, Equiv.Perm.coe_mul, Function.comp_apply]
      rw [g₁_fixes_tailC _ hC, g₁_fixes_tailC _ hC]
    rw [hC_fixed] at hx_apply
    simp only [isTailC, Fin.ext_iff] at hC hx_apply; omega
