/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Basic
import AfTests.Jordan.LinearizedJordan
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Formally Real Jordan Algebras

A Jordan algebra is formally real if sums of squares are only zero when each
summand is zero (H-O Definition 2.9.1).

## Main definitions

* `FormallyRealJordan J` - A Jordan algebra where `Σ aᵢ² = 0 ⟹ ∀i, aᵢ = 0`

## Main results

* `FormallyRealJordan.sq_eq_zero_imp_zero` - Corollary: a² = 0 implies a = 0
-/

open Finset BigOperators

/-- A Jordan algebra is formally real if sums of squares vanish only when all
summands vanish. -/
class FormallyRealJordan (J : Type*) [JordanAlgebra J] : Prop where
  /-- If a sum of squares is zero, each term is zero. -/
  sum_sq_eq_zero : ∀ (n : ℕ) (a : Fin n → J),
    (∑ i, JordanAlgebra.jsq (a i)) = 0 → ∀ i, a i = 0

namespace FormallyRealJordan

variable {J : Type*} [JordanAlgebra J]

/-- In a formally real Jordan algebra, a² = 0 implies a = 0. -/
theorem sq_eq_zero_imp_zero [FormallyRealJordan J] {a : J}
    (h : JordanAlgebra.jsq a = 0) : a = 0 := by
  have := sum_sq_eq_zero 1 (fun _ => a)
  simp only [Fin.sum_univ_one] at this
  exact this h 0

end FormallyRealJordan

/-!
## No Nilpotent Elements (H-O 2.9.4(i))

Formally real Jordan algebras have no nilpotent elements. This follows from
power associativity: if a^n = 0, then (a^k)² = a^{2k} = 0 for k = ⌈n/2⌉,
so by formal reality a^k = 0. By induction, a = 0.
-/

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-- If a^n = 0 and m ≥ n, then a^m = 0. Uses jpow_add (power associativity). -/
theorem jpow_eq_zero_of_ge {a : J} {n m : ℕ} (hn : jpow a n = 0) (hm : m ≥ n) :
    jpow a m = 0 := by
  have heq : m = n + (m - n) := by omega
  rw [heq, ← jpow_add]
  rw [hn, zero_jmul]

/-- Formally real Jordan algebras have no nilpotent elements (H-O 2.9.4(i)).

If a^n = 0 for some n ≥ 1, then a = 0.

The proof uses power associativity (jpow_add): for k = ⌈n/2⌉,
  (a^k)² = a^{2k} = 0 (since 2k ≥ n)
By formal reality, a^k = 0. Since k < n (for n ≥ 2), we reduce n by induction. -/
theorem no_nilpotent_of_formallyReal [FormallyRealJordan J]
    {a : J} {n : ℕ} (hn : n ≥ 1) (h : jpow a n = 0) : a = 0 := by
  -- Strong induction on n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => omega  -- n ≥ 1 contradicts n = 0
    | 1 =>
      -- jpow a 1 = a = 0
      simp only [jpow_one] at h
      exact h
    | n + 2 =>
      -- For n+2 ≥ 2, let k = (n + 3) / 2 = ⌈(n+2)/2⌉
      let k := (n + 3) / 2
      have hk_lt : k < n + 2 := by omega
      have hk_ge1 : k ≥ 1 := by omega
      have h2k_ge : 2 * k ≥ n + 2 := by omega
      -- Show a^(2k) = 0 (since 2k ≥ n+2 and a^{n+2} = 0)
      have h2k : jpow a (2 * k) = 0 := jpow_eq_zero_of_ge h h2k_ge
      -- Show (a^k)² = a^(2k) = 0
      have hsq : jsq (jpow a k) = 0 := by
        rw [jsq_def, jpow_add]
        convert h2k using 2
        ring
      -- By formal reality, a^k = 0
      have hak : jpow a k = 0 := FormallyRealJordan.sq_eq_zero_imp_zero hsq
      -- By IH (since k < n+2 and k ≥ 1), a = 0
      exact ih k hk_lt hk_ge1 hak

end JordanAlgebra
