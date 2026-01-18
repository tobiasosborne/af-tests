/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import Mathlib.Data.Fin.Basic

/-!
# The Domain Omega

This file defines the domain Ω(n,k,m) = Fin(6 + n + k + m) on which our
permutation group acts.

## Main Definitions

* `Omega n k m` - The type `Fin (6 + n + k + m)`
* `isCore` - Predicate for core points {0,1,2,3,4,5} (= {1,...,6} in 1-indexed)
* `isTailA`, `isTailB`, `isTailC` - Predicates for tail points

## Index Convention

AF proofs use 1-indexed elements. Lean's `Fin n` is 0-indexed.
- AF element k → Lean `Fin.mk (k-1)`
- Core elements {1,2,3,4,5,6} in AF → {0,1,2,3,4,5} in Lean
-/

/-- The domain Ω for parameters n, k, m is Fin (6 + n + k + m) -/
abbrev Omega (n k m : ℕ) := Fin (6 + n + k + m)

/-- The size of Ω -/
def Omega.card (n k m : ℕ) : ℕ := 6 + n + k + m

/-- Core points are {0,1,2,3,4,5} (representing {1,2,3,4,5,6} in 1-indexed) -/
def isCore {n k m : ℕ} (x : Omega n k m) : Prop := x.val < 6

/-- Tail A points are {6, ..., 6+n-1} (representing a₁, ..., aₙ) -/
def isTailA {n k m : ℕ} (x : Omega n k m) : Prop := 6 ≤ x.val ∧ x.val < 6 + n

/-- Tail B points are {6+n, ..., 6+n+k-1} (representing b₁, ..., bₖ) -/
def isTailB {n k m : ℕ} (x : Omega n k m) : Prop := 6 + n ≤ x.val ∧ x.val < 6 + n + k

/-- Tail C points are {6+n+k, ..., 6+n+k+m-1} (representing c₁, ..., cₘ) -/
def isTailC {n k m : ℕ} (x : Omega n k m) : Prop :=
  6 + n + k ≤ x.val ∧ x.val < 6 + n + k + m

/-- Every point is either in core or one of the tails -/
theorem Omega.partition {n k m : ℕ} (x : Omega n k m) :
    isCore x ∨ isTailA x ∨ isTailB x ∨ isTailC x := by
  sorry

/-- The size of Omega is at least 6 -/
theorem Omega.card_ge_six (n k m : ℕ) : Omega.card n k m ≥ 6 := by
  unfold Omega.card
  omega
