/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.Core.Omega
import Mathlib.GroupTheory.Perm.List

/-!
# Generators g₁, g₂, g₃

This file defines the three generators of the permutation group H.

## Main Definitions

* `g₁ n k m` - First generator: (1 6 4 3 a₁ ... aₙ) in 1-indexed
* `g₂ n k m` - Second generator: (2 4 5 1 b₁ ... bₖ) in 1-indexed
* `g₃ n k m` - Third generator: (3 5 6 2 c₁ ... cₘ) in 1-indexed

## Index Convention

AF uses 1-indexed, Lean uses 0-indexed:
- g₁ = (1 6 4 3 a₁...aₙ) → c[0, 5, 3, 2, 6, 7, ..., 5+n]
- g₂ = (2 4 5 1 b₁...bₖ) → c[1, 3, 4, 0, 6+n, ..., 5+n+k]
- g₃ = (3 5 6 2 c₁...cₘ) → c[2, 4, 5, 1, 6+n+k, ..., 5+n+k+m]

The generators are cycles of length (4 + tail_length).
-/

/-- Helper: build a list of Fin values for the tail A elements: [6, 7, ..., 5+n] -/
def tailAList (n k m : ℕ) : List (Omega n k m) :=
  (List.finRange n).map fun i =>
    ⟨6 + i.val, by have := i.isLt; omega⟩

/-- Helper: build a list of Fin values for the tail B elements: [6+n, ..., 5+n+k] -/
def tailBList (n k m : ℕ) : List (Omega n k m) :=
  (List.finRange k).map fun i =>
    ⟨6 + n + i.val, by have := i.isLt; omega⟩

/-- Helper: build a list of Fin values for the tail C elements: [6+n+k, ..., 5+n+k+m] -/
def tailCList (n k m : ℕ) : List (Omega n k m) :=
  (List.finRange m).map fun i =>
    ⟨6 + n + k + i.val, by have := i.isLt; omega⟩

/-- Core points for g₁: [0, 5, 3, 2] (representing (1 6 4 3) in 1-indexed) -/
def g₁CoreList (n k m : ℕ) : List (Omega n k m) :=
  [⟨0, by omega⟩, ⟨5, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩]

/-- Core points for g₂: [1, 3, 4, 0] (representing (2 4 5 1) in 1-indexed) -/
def g₂CoreList (n k m : ℕ) : List (Omega n k m) :=
  [⟨1, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩, ⟨0, by omega⟩]

/-- Core points for g₃: [2, 4, 5, 1] (representing (3 5 6 2) in 1-indexed) -/
def g₃CoreList (n k m : ℕ) : List (Omega n k m) :=
  [⟨2, by omega⟩, ⟨4, by omega⟩, ⟨5, by omega⟩, ⟨1, by omega⟩]

/-- Generator g₁ = (1 6 4 3 a₁ ... aₙ) as a permutation.
    In 0-indexed: cycle through [0, 5, 3, 2, 6, 7, ..., 5+n] -/
def g₁ (n k m : ℕ) : Equiv.Perm (Omega n k m) :=
  (g₁CoreList n k m ++ tailAList n k m).formPerm

/-- Generator g₂ = (2 4 5 1 b₁ ... bₖ) as a permutation.
    In 0-indexed: cycle through [1, 3, 4, 0, 6+n, ..., 5+n+k] -/
def g₂ (n k m : ℕ) : Equiv.Perm (Omega n k m) :=
  (g₂CoreList n k m ++ tailBList n k m).formPerm

/-- Generator g₃ = (3 5 6 2 c₁ ... cₘ) as a permutation.
    In 0-indexed: cycle through [2, 4, 5, 1, 6+n+k, ..., 5+n+k+m] -/
def g₃ (n k m : ℕ) : Equiv.Perm (Omega n k m) :=
  (g₃CoreList n k m ++ tailCList n k m).formPerm

/-- The cycle length of g₁ is 4 + n -/
theorem g₁_cycle_length (n k m : ℕ) :
    (g₁CoreList n k m ++ tailAList n k m).length = 4 + n := by
  simp [g₁CoreList, tailAList, List.finRange]; omega

/-- The cycle length of g₂ is 4 + k -/
theorem g₂_cycle_length (n k m : ℕ) :
    (g₂CoreList n k m ++ tailBList n k m).length = 4 + k := by
  simp [g₂CoreList, tailBList, List.finRange]; omega

/-- The cycle length of g₃ is 4 + m -/
theorem g₃_cycle_length (n k m : ℕ) :
    (g₃CoreList n k m ++ tailCList n k m).length = 4 + m := by
  simp [g₃CoreList, tailCList, List.finRange]; omega
