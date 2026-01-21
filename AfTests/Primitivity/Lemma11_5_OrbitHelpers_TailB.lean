/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Primitivity.Lemma11_5_OrbitHelpers_Core

/-!
# TailB Orbit Helper Lemmas

Lemmas about g₁ and g₂ actions on tailB elements.
-/

open Equiv Equiv.Perm Set OrbitCore

variable {n k m : ℕ}

namespace OrbitTailB

/-- First tailB element is in tailB -/
theorem first_tailB_is_tailB (hk : k ≥ 1) : isTailB (⟨6 + n, by omega⟩ : Omega n k m) := by
  simp only [isTailB]; omega

/-- tailB elements are disjoint from tailA -/
theorem tailB_not_tailA (x : Omega n k m) (hx : isTailB x) : ¬isTailA x :=
  tailB_disjoint_tailA x hx

/-- g₁^j(b) = b for any tailB element b -/
theorem g₁_pow_fixes_tailB (j : ℕ) (x : Omega n k m) (hx : isTailB x) :
    (g₁ n k m ^ j) x = x := by
  induction j with
  | zero => simp
  | succ j' ih =>
    rw [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply, ih, g₁_fixes_tailB x hx]

/-- g₁^j preserves tailB elements for integer j (since g₁ fixes tailB) -/
theorem g₁_zpow_fixes_tailB (j : ℤ) (x : Omega n k m) (hx : isTailB x) :
    (g₁ n k m ^ j) x = x := by
  have hFix : g₁ n k m x = x := g₁_fixes_tailB x hx
  exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hFix j

/-- g₂^j(b₁) = 6+n+j when j < k -/
theorem g₂_pow_b₁_eq_tailB_elem (hk : k ≥ 1) (hk2 : k ≥ 2) (j : Fin k) (hj : j.val > 0) :
    (g₂ n k m ^ j.val) (⟨6 + n, by omega⟩ : Omega n k m) = ⟨6 + n + j.val, by omega⟩ := by
  -- Proof uses formPerm_pow_apply_getElem with index computation
  sorry

/-- g₂(b₁) = b₂ (next tailB element) when k ≥ 2 -/
theorem g₂_b₁_eq_b₁_succ (hk : k ≥ 1) (hk2 : k ≥ 2) :
    g₂ n k m (⟨6 + n, by omega⟩ : Omega n k m) = ⟨6 + n + 1, by omega⟩ := by
  have := g₂_pow_b₁_eq_tailB_elem (n := n) (m := m) hk hk2 ⟨1, by omega⟩ (by omega : (1 : ℕ) > 0)
  simp only [pow_one] at this
  exact this

/-- g₂ maps tailB element to tailB or to element 1 (when at cycle end) -/
theorem g₂_tailB_to_tailB_or_1 (x : Omega n k m) (hx : isTailB x) :
    isTailB (g₂ n k m x) ∨ g₂ n k m x = ⟨1, by omega⟩ := by
  simp only [isTailB] at hx
  have hNodup := g₂_list_nodup n k m
  have hx_mem : x ∈ g₂CoreList n k m ++ tailBList n k m := by
    simp only [List.mem_append, tailBList, List.mem_map, List.mem_finRange]
    right
    exact ⟨⟨x.val - 6 - n, by omega⟩, trivial, by simp only [Fin.ext_iff]; omega⟩
  have hg₂x_mem := List.formPerm_apply_mem_of_mem hx_mem
  simp only [List.mem_append, g₂CoreList, List.mem_cons, List.not_mem_nil,
    or_false, tailBList, List.mem_map, List.mem_finRange] at hg₂x_mem
  rcases hg₂x_mem with hCore | hTailB
  · rcases hCore with h1 | h3 | h4 | h0
    · right; exact h1
    · exfalso
      have hinv : g₂ n k m (⟨1, by omega⟩ : Omega n k m) = ⟨3, by omega⟩ := g₂_elem1_eq_elem3
      have hinj := (g₂ n k m).injective
      have : x = ⟨1, by omega⟩ := hinj (h3.trans hinv.symm)
      simp only [Fin.ext_iff] at this; omega
    · exfalso
      have hinv : g₂ n k m (⟨3, by omega⟩ : Omega n k m) = ⟨4, by omega⟩ := g₂_elem3_eq_elem4
      have hinj := (g₂ n k m).injective
      have : x = ⟨3, by omega⟩ := hinj (h4.trans hinv.symm)
      simp only [Fin.ext_iff] at this; omega
    · exfalso
      have hinv : g₂ n k m (⟨4, by omega⟩ : Omega n k m) = ⟨0, by omega⟩ := g₂_elem4_eq_elem0'
      have hinj := (g₂ n k m).injective
      have : x = ⟨4, by omega⟩ := hinj (h0.trans hinv.symm)
      simp only [Fin.ext_iff] at this; omega
  · left
    obtain ⟨idx, _, hidx⟩ := hTailB
    have hidx_lt := idx.isLt
    simp only [isTailB, g₂]
    -- hidx says formPerm(x) = 6+n+idx where idx < k
    -- So formPerm(x) is in tailB range
    simp only [g₂CoreList, tailBList, Fin.ext_iff] at hidx ⊢
    omega

/-- g₂ of tailB element is not in tailA -/
theorem g₂_tailB_not_tailA (x : Omega n k m) (hx : isTailB x) : ¬isTailA (g₂ n k m x) := by
  rcases g₂_tailB_to_tailB_or_1 x hx with hTailB | h1
  · exact tailB_not_tailA _ hTailB
  · rw [h1]; exact elem1_not_tailA

/-- The orbit of b₁ under g₂^j eventually exits tailB for j ≥ 2 -/
theorem g₂_pow_orbit_hits_core (hk : k ≥ 1) (hk2 : k ≥ 2) (j : ℕ) (hj : j ≥ 2) (hjk : j < k) :
    ∃ r : ℕ, r ≥ 1 ∧ ¬isTailB ((g₂ n k m ^ (r * j)) (⟨6 + n, by omega⟩ : Omega n k m)) := by
  -- The g₂ cycle has length 4 + k
  -- Starting from position 4 (element 6+n), after r*j steps we're at position (4 + r*j) mod (4+k)
  -- For r*j ≥ k, position wraps to r*j - k which is < j < 4 (for j ≤ 3) or in tailB but exits
  -- Eventually reaches position 0 (element 1) which is not in tailB
  sorry

end OrbitTailB
