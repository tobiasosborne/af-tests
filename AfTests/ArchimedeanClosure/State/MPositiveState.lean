/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.ArchimedeanClosure.Algebra.QuadraticModule
import Mathlib.Algebra.Module.LinearMap.Basic

/-! # M-Positive States

This file defines M-positive states on the free *-algebra.

## Main definitions

* `MPositiveState n` - A state φ with φ(1)=1 and φ(m)≥0 for m∈M
* `MPositiveStateSet n` - The set S_M of all M-positive states

## Mathematical Background

An M-positive state is a linear functional φ : A₀ → ℂ satisfying:
1. φ(1) = 1 (normalization)
2. φ(m) ≥ 0 for all m ∈ M (M-positivity)

For elements in M (which are sums of squares), the value φ(m) is real and nonnegative.
-/

namespace FreeStarAlgebra

variable {n : ℕ}

/-- An M-positive state: linear functional with φ(1)=1 and φ(m)≥0 for m∈M.

The key properties are:
- Normalization: φ(1) = 1
- M-positivity: φ(m).re ≥ 0 for m ∈ M
- Reality on M: φ(m).im = 0 for m ∈ M (M-elements map to real values)
-/
structure MPositiveState (n : ℕ) where
  /-- The underlying linear functional. -/
  toFun : FreeStarAlgebra n →ₗ[ℂ] ℂ
  /-- The state maps 1 to 1. -/
  map_one : toFun 1 = 1
  /-- Elements of M map to values with nonnegative real part. -/
  map_m_nonneg : ∀ m ∈ QuadraticModule n, 0 ≤ (toFun m).re
  /-- Elements of M map to real values (imaginary part is zero). -/
  map_m_real : ∀ m ∈ QuadraticModule n, (toFun m).im = 0

namespace MPositiveState

/-- Coercion from MPositiveState to function type. -/
instance : FunLike (MPositiveState n) (FreeStarAlgebra n) ℂ where
  coe φ := φ.toFun
  coe_injective' := by
    intro φ ψ h
    cases φ; cases ψ
    simp only [mk.injEq]
    ext x
    exact congrFun h x

variable (φ : MPositiveState n)

/-- The state maps 1 to 1. -/
@[simp]
theorem apply_one : φ 1 = 1 := φ.map_one

/-- Elements of M have nonnegative real part under φ. -/
theorem apply_m_nonneg {m : FreeStarAlgebra n} (hm : m ∈ QuadraticModule n) :
    0 ≤ (φ m).re := φ.map_m_nonneg m hm

/-- Elements of M map to real values under φ. -/
theorem apply_m_real {m : FreeStarAlgebra n} (hm : m ∈ QuadraticModule n) :
    (φ m).im = 0 := φ.map_m_real m hm

/-- φ(star a * a).re ≥ 0 since star a * a ∈ M. -/
theorem apply_star_mul_self_nonneg (a : FreeStarAlgebra n) :
    0 ≤ (φ (star a * a)).re :=
  φ.apply_m_nonneg (star_mul_self_mem a)

/-- Linearity: φ(a + b) = φ(a) + φ(b). -/
theorem map_add (a b : FreeStarAlgebra n) :
    φ (a + b) = φ a + φ b := φ.toFun.map_add a b

/-- Linearity: φ(c • a) = c * φ(a). -/
theorem map_smul (c : ℂ) (a : FreeStarAlgebra n) :
    φ (c • a) = c * φ a := φ.toFun.map_smul c a

end MPositiveState

/-- The set S_M of all M-positive states. -/
def MPositiveStateSet (n : ℕ) : Set (MPositiveState n) := Set.univ

end FreeStarAlgebra
