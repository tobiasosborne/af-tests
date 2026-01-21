/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Core
import AfTests.Primitivity.Lemma11_5_Defs
import AfTests.Primitivity.Lemma11_5_CycleSupport
import AfTests.Primitivity.Lemma11_5_OrbitContinuation
import AfTests.Primitivity.Lemma11_5_Case2

/-!
# Additional Orbit Helper Lemmas for Case 2

Lemmas for the j ≥ 2 and j ≤ -3 orbit cases in the Case 2 proof.
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

/-- g₁²(0) = 3 (composition of g₁(0) = 5 and g₁(5) = 3) -/
theorem g₁_sq_elem0_eq_elem3 :
    g₁ n k m (g₁ n k m (⟨0, by omega⟩ : Omega n k m)) = ⟨3, by omega⟩ := by
  rw [g₁_elem0_eq_elem5, g₁_elem5_eq_elem3]

/-- Element 4 is not in tailA -/
theorem elem4_not_tailA : ¬isTailA (⟨4, by omega⟩ : Omega n k m) := by simp [isTailA]

/-- Element 1 is not in tailA (re-export for convenience) -/
theorem elem1_not_tailA' : ¬isTailA (⟨1, by omega⟩ : Omega n k m) := elem1_not_tailA

/-- g₁ fixes element 1 -/
theorem g₁_fixes_elem1' : g₁ n k m (⟨1, by omega⟩ : Omega n k m) = ⟨1, by omega⟩ :=
  g₁_fixes_elem1

/-- g₁^j fixes element 1 for any natural j -/
theorem g₁_pow_fixes_elem1 (j : ℕ) :
    (g₁ n k m ^ j) (⟨1, by omega⟩ : Omega n k m) = ⟨1, by omega⟩ := by
  induction j with
  | zero => simp
  | succ j' ih =>
    rw [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply, ih, g₁_fixes_elem1']

/-- g₁^j(b) = b for any tailB element b -/
theorem g₁_pow_fixes_tailB (j : ℕ) (x : Omega n k m) (hx : isTailB x) :
    (g₁ n k m ^ j) x = x := by
  induction j with
  | zero => simp
  | succ j' ih =>
    rw [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply, ih, g₁_fixes_tailB x hx]

/-- g₂ maps 4 to 0 (element 4 is at index 2 in g₂CoreList = [1,3,4,0], next is 0) -/
theorem g₂_elem4_eq_elem0' :
    g₂ n k m (⟨4, by omega⟩ : Omega n k m) = ⟨0, by omega⟩ := by
  unfold g₂
  have hNodup := g₂_list_nodup n k m
  have h_len := g₂_cycle_length n k m
  have h_core_len : (g₂CoreList n k m).length = 4 := by simp [g₂CoreList]
  -- Element 4 is at index 2 in g₂CoreList = [1, 3, 4, 0]
  have h_2_lt : 2 < (g₂CoreList n k m ++ tailBList n k m).length := by rw [h_len]; omega
  have h_2_lt_core : 2 < (g₂CoreList n k m).length := by rw [h_core_len]; omega
  have h_idx : (g₂CoreList n k m ++ tailBList n k m)[2]'h_2_lt =
      (⟨4, by omega⟩ : Omega n k m) := by
    rw [List.getElem_append_left h_2_lt_core]
    simp [g₂CoreList]
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 2 h_2_lt]
  simp only [h_len]
  -- (2 + 1) % (4 + k) = 3 always (since k ≥ 0)
  have h_mod : (2 + 1) % (4 + k) = 3 := Nat.mod_eq_of_lt (by omega)
  simp only [h_mod]
  -- Index 3 is 0 in g₂CoreList
  have h_3_lt_core : 3 < (g₂CoreList n k m).length := by rw [h_core_len]; omega
  rw [List.getElem_append_left h_3_lt_core]
  simp [g₂CoreList]

/-- g₂ maps 1 to 3 (element 1 is at index 0, next is 3) -/
theorem g₂_elem1_eq_elem3 :
    g₂ n k m (⟨1, by omega⟩ : Omega n k m) = ⟨3, by omega⟩ := by
  unfold g₂
  have hNodup := g₂_list_nodup n k m
  have h_len := g₂_cycle_length n k m
  have h_core_len : (g₂CoreList n k m).length = 4 := by simp [g₂CoreList]
  have h_0_lt : 0 < (g₂CoreList n k m ++ tailBList n k m).length := by rw [h_len]; omega
  have h_idx : (g₂CoreList n k m ++ tailBList n k m)[0]'h_0_lt =
      (⟨1, by omega⟩ : Omega n k m) := by
    rw [List.getElem_append_left (by omega : 0 < (g₂CoreList n k m).length)]
    simp [g₂CoreList]
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 0 h_0_lt]
  simp only [h_len]
  have h_mod : (0 + 1) % (4 + k) = 1 := Nat.mod_eq_of_lt (by omega)
  simp only [h_mod]
  rw [List.getElem_append_left (by omega : 1 < (g₂CoreList n k m).length)]
  simp [g₂CoreList]

/-- g₂ maps 3 to 4 (element 3 is at index 1, next is 4) -/
theorem g₂_elem3_eq_elem4 :
    g₂ n k m (⟨3, by omega⟩ : Omega n k m) = ⟨4, by omega⟩ := by
  unfold g₂
  have hNodup := g₂_list_nodup n k m
  have h_len := g₂_cycle_length n k m
  have h_core_len : (g₂CoreList n k m).length = 4 := by simp [g₂CoreList]
  have h_1_lt : 1 < (g₂CoreList n k m ++ tailBList n k m).length := by rw [h_len]; omega
  have h_idx : (g₂CoreList n k m ++ tailBList n k m)[1]'h_1_lt =
      (⟨3, by omega⟩ : Omega n k m) := by
    rw [List.getElem_append_left (by omega : 1 < (g₂CoreList n k m).length)]
    simp [g₂CoreList]
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 1 h_1_lt]
  simp only [h_len]
  have h_mod : (1 + 1) % (4 + k) = 2 := Nat.mod_eq_of_lt (by omega)
  simp only [h_mod]
  rw [List.getElem_append_left (by omega : 2 < (g₂CoreList n k m).length)]
  simp [g₂CoreList]

/-- First tailB element is in tailB -/
theorem first_tailB_is_tailB (hk : k ≥ 1) : isTailB (⟨6 + n, by omega⟩ : Omega n k m) := by
  simp only [isTailB]; omega

/-- tailB elements are disjoint from tailA -/
theorem tailB_not_tailA (x : Omega n k m) (hx : isTailB x) : ¬isTailA x :=
  tailB_disjoint_tailA x hx

/-- g₁^j preserves tailB elements for integer j (since g₁ fixes tailB) -/
theorem g₁_zpow_fixes_tailB (j : ℤ) (x : Omega n k m) (hx : isTailB x) :
    (g₁ n k m ^ j) x = x := by
  have hFix : g₁ n k m x = x := g₁_fixes_tailB x hx
  exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hFix j

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
  · -- Core element: must be 1 or 4 (others are in supp(g₁))
    simp only [isCore] at hCore
    have hCases : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 ∨ x.val = 3 ∨ x.val = 4 ∨ x.val = 5 := by omega
    rcases hCases with h0 | h1 | h2 | h3 | h4 | h5
    · exfalso; have heq : x = ⟨0, by omega⟩ := Fin.ext h0; rw [heq] at hx; exact hx elem0_in_support_g₁
    · left; exact h1
    · exfalso; have heq : x = ⟨2, by omega⟩ := Fin.ext h2; rw [heq] at hx; exact hx elem2_in_support_g₁'
    · exfalso; have heq : x = ⟨3, by omega⟩ := Fin.ext h3; rw [heq] at hx; exact hx elem3_in_support_g₁
    · right; left; exact h4
    · exfalso; have heq : x = ⟨5, by omega⟩ := Fin.ext h5; rw [heq] at hx; exact hx elem5_in_support_g₁
  · -- tailA: all in supp(g₁)
    exfalso
    simp only [isTailA] at hA
    have hi : x.val - 6 < n := by have := x.isLt; omega
    have hx_supp : x ∈ (g₁ n k m).support := by
      convert tailA_in_support_g₁ (⟨x.val - 6, hi⟩ : Fin n) using 1
      simp only [Fin.ext_iff]; omega
    exact hx hx_supp
  · right; right; left; exact hB
  · right; right; right; exact hC

/-- g₁² applied to element 0 gives element 3 -/
theorem g₁_pow2_elem0_eq_elem3 :
    (g₁ n k m ^ (2 : ℕ)) (⟨0, by omega⟩ : Omega n k m) = ⟨3, by omega⟩ := by
  simp only [pow_two, Equiv.Perm.coe_mul, Function.comp_apply]
  exact g₁_sq_elem0_eq_elem3

/-- g₂ maps tailB element to tailB or 1 -/
theorem g₂_tailB_to_tailB_or_1 (x : Omega n k m) (hx : isTailB x) :
    isTailB (g₂ n k m x) ∨ g₂ n k m x = ⟨1, by omega⟩ := by
  simp only [isTailB] at hx
  have hNodup := g₂_list_nodup n k m
  have h_len := g₂_cycle_length n k m
  have h_core_len : (g₂CoreList n k m).length = 4 := by simp [g₂CoreList]
  -- x is at some index in the tailB portion (indices 4 to 4+k-1)
  -- The position of x in tailB is (x.val - 6 - n), so its index in the full list is 4 + (x.val - 6 - n)
  have hx_mem : x ∈ g₂CoreList n k m ++ tailBList n k m := by
    simp only [List.mem_append, tailBList, List.mem_map, List.mem_finRange]
    right
    exact ⟨⟨x.val - 6 - n, by omega⟩, trivial, by simp only [Fin.ext_iff]; omega⟩
  have hg₂x_mem := List.formPerm_apply_mem_of_mem hx_mem
  -- g₂(x) is in the cycle list, so it's either in g₂CoreList or tailBList
  simp only [List.mem_append, g₂CoreList, List.mem_cons, List.not_mem_nil,
    or_false, tailBList, List.mem_map, List.mem_finRange] at hg₂x_mem
  rcases hg₂x_mem with hCore | hTailB
  · -- g₂(x) ∈ {1, 3, 4, 0}. Must show only 1 is possible.
    rcases hCore with h1 | h3 | h4 | h0
    · right; exact h1
    · -- g₂(x) = 3 is impossible. g₂⁻¹(3) = 1, but x ∈ tailB, so x ≠ 1
      exfalso
      have hinv : g₂ n k m (⟨1, by omega⟩ : Omega n k m) = ⟨3, by omega⟩ := g₂_elem1_eq_elem3
      have hinj := (g₂ n k m).injective
      have : x = ⟨1, by omega⟩ := hinj (h3.trans hinv.symm)
      simp only [Fin.ext_iff] at this; omega
    · -- g₂(x) = 4 is impossible. g₂⁻¹(4) = 3, but x ∈ tailB, so x ≠ 3
      exfalso
      have hinv : g₂ n k m (⟨3, by omega⟩ : Omega n k m) = ⟨4, by omega⟩ := g₂_elem3_eq_elem4
      have hinj := (g₂ n k m).injective
      have : x = ⟨3, by omega⟩ := hinj (h4.trans hinv.symm)
      simp only [Fin.ext_iff] at this; omega
    · -- g₂(x) = 0 is impossible. g₂⁻¹(0) = 4, but x ∈ tailB, so x ≠ 4
      exfalso
      have hinv : g₂ n k m (⟨4, by omega⟩ : Omega n k m) = ⟨0, by omega⟩ := g₂_elem4_eq_elem0'
      have hinj := (g₂ n k m).injective
      have : x = ⟨4, by omega⟩ := hinj (h0.trans hinv.symm)
      simp only [Fin.ext_iff] at this; omega
  · -- g₂(x) is in tailB
    left
    obtain ⟨idx, _, hidx⟩ := hTailB
    simp only [isTailB, Fin.ext_iff] at hidx ⊢
    -- hidx says (formPerm result).val = 6 + n + idx
    -- We need to show g₂ x = formPerm x (defeq) and use hidx
    have hg₂_eq : (g₂ n k m x).val = (List.formPerm
        (g₂CoreList n k m ++ tailBList n k m) x).val := rfl
    simp only [g₂CoreList, tailBList] at hg₂_eq
    have := idx.isLt
    omega

/-- g₂ of tailB element is not in tailA -/
theorem g₂_tailB_not_tailA (x : Omega n k m) (hx : isTailB x) : ¬isTailA (g₂ n k m x) := by
  rcases g₂_tailB_to_tailB_or_1 x hx with hTailB | h1
  · exact tailB_not_tailA _ hTailB
  · rw [h1]; exact elem1_not_tailA

/-- g₂ applied to element outside supp(g₁) never gives 6 (needs n ≥ 1) -/
theorem g₂_image_not_6 (hn : n ≥ 1) (y : Omega n k m)
    (hy : y.val = 1 ∨ y.val = 4 ∨ isTailB y ∨ isTailC y) :
    (g₂ n k m y).val ≠ 6 := by
  rcases hy with h1 | h4 | hB | hC
  · -- y = 1: g₂(1) = 3 ≠ 6
    have heq : y = ⟨1, by omega⟩ := Fin.ext h1
    rw [heq, g₂_elem1_eq_elem3]; simp
  · -- y = 4: g₂(4) = 0 ≠ 6
    have heq : y = ⟨4, by omega⟩ := Fin.ext h4
    rw [heq, g₂_elem4_eq_elem0']; simp
  · -- y ∈ tailB: g₂(y) ∈ tailB ∪ {1}, values are 1 or ≥ 6+n ≥ 7
    rcases g₂_tailB_to_tailB_or_1 y hB with hB' | h1'
    · simp only [isTailB] at hB'; omega
    · rw [h1']; simp
  · -- y ∈ tailC: g₂(y) = y, values ≥ 6+n+k ≥ 7
    have hFix := g₂_fixes_tailC y hC
    rw [hFix]; simp only [isTailC] at hC; omega

/-- g₁^j preserves tailC elements for integer j (since g₁ fixes tailC) -/
theorem g₁_zpow_fixes_tailC (j : ℤ) (x : Omega n k m) (hx : isTailC x) :
    (g₁ n k m ^ j) x = x := by
  have hFix : g₁ n k m x = x := g₁_fixes_tailC x hx
  exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hFix j

