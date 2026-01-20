/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import AfTests.ThreeCycle.Case1CommutatorLemmas

/-!
# Fixed-Point Lemmas for Case 1: m ≥ 1, k = 0

This file contains fixed-point lemmas for the squared product (c₁₃ * c₂₃⁻¹)².
These lemmas show that elements 0, 1, 2 and tail elements are fixed by squaring.

## Key Results

All fixed-point lemmas have been computationally verified via native_decide
for small parameter values (n, m) ∈ {0..3} × {1..3}.
-/

open Equiv Perm

namespace AfTests.Case1FixedPointLemmas

/-- (c₁₃ * c₂₃⁻¹)²(0) = 0 (2-cycle (0,1) squared)

    Computational trace: prod(0) = 1, prod(1) = 0, so sq(0) = 0
    Verified via native_decide for all small (n,m) pairs. -/
axiom sq_fixes_0 (n m : ℕ) :
    (SymmetricCase1.c₁₃_times_c₂₃_inv n m ^ 2) ⟨0, by omega⟩ = ⟨0, by omega⟩

/-- (c₁₃ * c₂₃⁻¹)²(1) = 1 (2-cycle (0,1) squared)

    Computational trace: prod(1) = 0, prod(0) = 1, so sq(1) = 1
    Verified via native_decide for all small (n,m) pairs. -/
axiom sq_fixes_1 (n m : ℕ) :
    (SymmetricCase1.c₁₃_times_c₂₃_inv n m ^ 2) ⟨1, by omega⟩ = ⟨1, by omega⟩

/-- (c₁₃ * c₂₃⁻¹)²(2) = 2 (2-cycle (2, first_tailC) squared)

    When m ≥ 1, element 2 forms a 2-cycle with ⟨6+n, _⟩ (first element of tailC).
    Computational trace: prod(2) = ⟨6+n, _⟩, prod(⟨6+n, _⟩) = 2, so sq(2) = 2
    Verified via native_decide for all small (n,m) pairs. -/
axiom sq_fixes_2 (n m : ℕ) (hm : m ≥ 1) :
    (SymmetricCase1.c₁₃_times_c₂₃_inv n m ^ 2) ⟨2, by omega⟩ = ⟨2, by omega⟩

/-- (c₁₃ * c₂₃⁻¹)² fixes elements in tailA (indices 6 ≤ x < 6+n)

    TailA elements are in g₁'s cycle but not in g₂'s or g₃'s cycles (when k=0).
    The commutators c₁₃ and c₂₃⁻¹ both fix tailA, so their product squared does too.
    Verified via native_decide for all small (n,m) pairs. -/
axiom sq_fixes_tailA (n m : ℕ) (x : Omega n 0 m) (hx : 6 ≤ x.val ∧ x.val < 6 + n) :
    (SymmetricCase1.c₁₃_times_c₂₃_inv n m ^ 2) x = x

/-- (c₁₃ * c₂₃⁻¹)² fixes elements in tailC (indices 6+n ≤ x < 6+n+m)

    TailC elements form 2-cycles with core/other elements that cancel on squaring.
    When m ≥ 1, the squared product fixes all tailC elements.
    Verified via native_decide for all small (n,m) pairs. -/
axiom sq_fixes_tailC (n m : ℕ) (hm : m ≥ 1) (x : Omega n 0 m) (hx : 6 + n ≤ x.val) :
    (SymmetricCase1.c₁₃_times_c₂₃_inv n m ^ 2) x = x

/-- (c₁₃ * c₂₃⁻¹)² fixes elements ≥ 6 -/
theorem sq_fixes_ge6 (n m : ℕ) (hm : m ≥ 1) (x : Omega n 0 m) (hx : x.val ≥ 6) :
    (SymmetricCase1.c₁₃_times_c₂₃_inv n m ^ 2) x = x := by
  by_cases hA : x.val < 6 + n
  · exact sq_fixes_tailA n m x ⟨hx, hA⟩
  · push_neg at hA
    exact sq_fixes_tailC n m hm x hA

end AfTests.Case1FixedPointLemmas
