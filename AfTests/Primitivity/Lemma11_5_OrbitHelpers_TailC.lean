/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Primitivity.Lemma11_5_OrbitHelpers_Core

/-!
# TailC Orbit Helper Lemmas

Lemmas about g₃ action on tailC elements. Symmetric to TailB helpers.
-/

open Equiv Equiv.Perm Set OrbitCore

variable {n k m : ℕ}

namespace OrbitTailC

/-- First tailC element is in tailC -/
theorem first_tailC_is_tailC (hm : m ≥ 1) : isTailC (⟨6 + n + k, by omega⟩ : Omega n k m) := by
  simp only [isTailC]; omega

/-- tailC elements are disjoint from tailA -/
theorem tailC_not_tailA (x : Omega n k m) (hx : isTailC x) : ¬isTailA x :=
  tailC_disjoint_tailA x hx

/-- g₁^j(c) = c for any tailC element c -/
theorem g₁_pow_fixes_tailC (j : ℕ) (x : Omega n k m) (hx : isTailC x) :
    (g₁ n k m ^ j) x = x := by
  induction j with
  | zero => simp
  | succ j' ih =>
    rw [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply, ih, g₁_fixes_tailC x hx]

/-- g₁^j preserves tailC elements for integer j -/
theorem g₁_zpow_fixes_tailC (j : ℤ) (x : Omega n k m) (hx : isTailC x) :
    (g₁ n k m ^ j) x = x := by
  have hFix : g₁ n k m x = x := g₁_fixes_tailC x hx
  exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hFix j

/-- g₃^j(c₁) = 6+n+k+j when j < m -/
theorem g₃_pow_c₁_eq_tailC_elem (hm : m ≥ 1) (hm2 : m ≥ 2) (j : Fin m) (hj : j.val > 0) :
    (g₃ n k m ^ j.val) (⟨6 + n + k, by omega⟩ : Omega n k m) = ⟨6 + n + k + j.val, by omega⟩ := by
  -- Proof uses formPerm_pow_apply_getElem with index computation
  sorry

/-- g₃(c₁) = c₂ (next tailC element) when m ≥ 2 -/
theorem g₃_c₁_eq_c₁_succ (hm : m ≥ 1) (hm2 : m ≥ 2) :
    g₃ n k m (⟨6 + n + k, by omega⟩ : Omega n k m) = ⟨6 + n + k + 1, by omega⟩ := by
  have := g₃_pow_c₁_eq_tailC_elem (n := n) (k := k) hm hm2 ⟨1, by omega⟩ (by omega : (1 : ℕ) > 0)
  simp only [pow_one] at this
  exact this

/-- g₃ maps tailC element to tailC or to element 2 (when at cycle end) -/
theorem g₃_tailC_to_tailC_or_2 (x : Omega n k m) (hx : isTailC x) :
    isTailC (g₃ n k m x) ∨ g₃ n k m x = ⟨2, by omega⟩ := by
  simp only [isTailC] at hx
  have hNodup := g₃_list_nodup n k m
  have hx_mem : x ∈ g₃CoreList n k m ++ tailCList n k m := by
    simp only [List.mem_append, tailCList, List.mem_map, List.mem_finRange]
    right
    exact ⟨⟨x.val - 6 - n - k, by omega⟩, trivial, by simp only [Fin.ext_iff]; omega⟩
  have hg₃x_mem := List.formPerm_apply_mem_of_mem hx_mem
  simp only [List.mem_append, g₃CoreList, List.mem_cons, List.not_mem_nil,
    or_false, tailCList, List.mem_map, List.mem_finRange] at hg₃x_mem
  rcases hg₃x_mem with hCore | hTailC
  · rcases hCore with h2 | h4 | h5 | h1
    · right; exact h2
    · exfalso
      have hinv : g₃ n k m (⟨2, by omega⟩ : Omega n k m) = ⟨4, by omega⟩ := g₃_elem2_eq_elem4
      have hinj := (g₃ n k m).injective
      have : x = ⟨2, by omega⟩ := hinj (h4.trans hinv.symm)
      simp only [Fin.ext_iff] at this; omega
    · exfalso
      have hinv : g₃ n k m (⟨4, by omega⟩ : Omega n k m) = ⟨5, by omega⟩ := g₃_elem4_eq_elem5
      have hinj := (g₃ n k m).injective
      have : x = ⟨4, by omega⟩ := hinj (h5.trans hinv.symm)
      simp only [Fin.ext_iff] at this; omega
    · exfalso
      have hinv : g₃ n k m (⟨5, by omega⟩ : Omega n k m) = ⟨1, by omega⟩ := g₃_elem5_eq_elem1
      have hinj := (g₃ n k m).injective
      have : x = ⟨5, by omega⟩ := hinj (h1.trans hinv.symm)
      simp only [Fin.ext_iff] at this; omega
  · left
    obtain ⟨idx, _, hidx⟩ := hTailC
    have hidx_lt := idx.isLt
    simp only [isTailC, g₃]
    simp only [g₃CoreList, tailCList, Fin.ext_iff] at hidx ⊢
    omega

/-- g₃ of tailC element is not in tailA -/
theorem g₃_tailC_not_tailA (x : Omega n k m) (hx : isTailC x) : ¬isTailA (g₃ n k m x) := by
  rcases g₃_tailC_to_tailC_or_2 x hx with hTailC | h2
  · exact tailC_not_tailA _ hTailC
  · rw [h2]; exact elem2_not_tailA

/-- The orbit of c₁ under g₃^j eventually exits tailC for j ≥ 2 -/
theorem g₃_pow_orbit_hits_core (hm : m ≥ 1) (hm2 : m ≥ 2) (j : ℕ) (hj : j ≥ 2) (hjm : j < m) :
    ∃ r : ℕ, r ≥ 1 ∧ ¬isTailC ((g₃ n k m ^ (r * j)) (⟨6 + n + k, by omega⟩ : Omega n k m)) := by
  -- The g₃ cycle has length 4 + m
  -- Starting from position 4 (element 6+n+k), after r*j steps we're at position (4 + r*j) mod (4+m)
  -- Eventually reaches position 0 (element 2) which is not in tailC
  sorry

end OrbitTailC
