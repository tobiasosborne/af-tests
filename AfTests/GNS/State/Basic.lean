/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# States on C*-Algebras

This file defines states on C*-algebras and proves basic properties.

## Main definitions

* `State A` - A state on a C*-algebra A is a continuous linear functional φ : A → ℂ
  that is positive (φ(a*a) ≥ 0 for all a) and normalized (φ(1) = 1).

## Main results

* `State.continuous` - States are continuous
* `State.apply_star_mul_self_nonneg` - φ(a*a) is a non-negative real
* `State.apply_one` - φ(1) = 1
-/

/-- A state on a C*-algebra is a continuous linear functional φ : A → ℂ
    that is positive (φ(a*a) ≥ 0) and normalized (φ(1) = 1). -/
structure State (A : Type*) [CStarAlgebra A] where
  /-- The underlying continuous linear map. -/
  toContinuousLinearMap : A →L[ℂ] ℂ
  /-- A state is positive: φ(a*a) is a non-negative real for all a. -/
  map_star_mul_self_nonneg : ∀ a : A, 0 ≤ (toContinuousLinearMap (star a * a)).re
  /-- A state is normalized: φ(1) = 1. -/
  map_one : toContinuousLinearMap 1 = 1

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)

instance instFunLike : FunLike (State A) A ℂ where
  coe φ := φ.toContinuousLinearMap
  coe_injective' φ ψ h := by
    cases φ; cases ψ; congr
    exact ContinuousLinearMap.ext (fun x => congrFun h x)

@[simp] theorem coe_mk (f : A →L[ℂ] ℂ) (h1 h2) (a : A) : (⟨f, h1, h2⟩ : State A) a = f a := rfl

/-- Coercion to ContinuousLinearMap. -/
instance instCoe : CoeOut (State A) (A →L[ℂ] ℂ) := ⟨toContinuousLinearMap⟩

/-- States are continuous. -/
theorem continuous : Continuous φ := φ.toContinuousLinearMap.continuous

/-- φ(a*a) is a non-negative real. -/
theorem apply_star_mul_self_nonneg (a : A) : 0 ≤ (φ (star a * a)).re :=
  φ.map_star_mul_self_nonneg a

/-- φ(1) = 1. -/
@[simp] theorem apply_one : φ 1 = 1 := φ.map_one

/-- States are linear: φ(a + b) = φ(a) + φ(b). -/
theorem map_add (a b : A) : φ (a + b) = φ a + φ b := φ.toContinuousLinearMap.map_add a b

/-- States respect scalar multiplication: φ(c • a) = c * φ(a). -/
theorem map_smul (c : ℂ) (a : A) : φ (c • a) = c * φ a := φ.toContinuousLinearMap.map_smul c a

/-- States map zero to zero. -/
@[simp] theorem map_zero : φ 0 = 0 := φ.toContinuousLinearMap.map_zero

/-- States respect subtraction. -/
theorem map_sub (a b : A) : φ (a - b) = φ a - φ b := φ.toContinuousLinearMap.map_sub a b

/-- States respect negation. -/
theorem map_neg (a : A) : φ (-a) = -φ a := φ.toContinuousLinearMap.map_neg a

end State
