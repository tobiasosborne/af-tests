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
# Core Orbit Helper Lemmas

Basic lemmas about element mappings under g₁ and g₂.
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

namespace OrbitCore

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

/-- g₂ maps 4 to 0 (element 4 is at index 2 in g₂CoreList = [1,3,4,0], next is 0) -/
theorem g₂_elem4_eq_elem0' :
    g₂ n k m (⟨4, by omega⟩ : Omega n k m) = ⟨0, by omega⟩ := by
  unfold g₂
  have hNodup := g₂_list_nodup n k m
  have h_len := g₂_cycle_length n k m
  have h_core_len : (g₂CoreList n k m).length = 4 := by simp [g₂CoreList]
  have h_2_lt : 2 < (g₂CoreList n k m ++ tailBList n k m).length := by rw [h_len]; omega
  have h_2_lt_core : 2 < (g₂CoreList n k m).length := by rw [h_core_len]; omega
  have h_idx : (g₂CoreList n k m ++ tailBList n k m)[2]'h_2_lt =
      (⟨4, by omega⟩ : Omega n k m) := by
    rw [List.getElem_append_left h_2_lt_core]
    simp [g₂CoreList]
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 2 h_2_lt]
  simp only [h_len]
  have h_mod : (2 + 1) % (4 + k) = 3 := Nat.mod_eq_of_lt (by omega)
  simp only [h_mod]
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

/-- g₁² applied to element 0 gives element 3 -/
theorem g₁_pow2_elem0_eq_elem3 :
    (g₁ n k m ^ (2 : ℕ)) (⟨0, by omega⟩ : Omega n k m) = ⟨3, by omega⟩ := by
  simp only [pow_two, Equiv.Perm.coe_mul, Function.comp_apply]
  exact g₁_sq_elem0_eq_elem3

end OrbitCore
