/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.ArchimedeanClosure.GNS.NullSpace
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # GNS Quotient Space for M-Positive States

This file constructs the quotient A₀/N_φ with ℝ-module structure.

## Main definitions

* `MPositiveState.gnsQuotient` - The quotient FreeStarAlgebra n ⧸ N_φ
* `MPositiveState.gnsQuotientMk` - The quotient map A₀ →ₗ[ℝ] A₀ ⧸ N_φ

## Mathematical Background

The quotient by the null space N_φ = {a : φ(star a * a) = 0} gives a pre-Hilbert space
structure. The inner product on the quotient is ⟨[a], [b]⟩ = φ(star b * a).
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ} (φ : MPositiveState n)

/-! ### The quotient space -/

/-- The GNS quotient space A₀ ⧸ N_φ. -/
abbrev gnsQuotient := FreeStarAlgebra n ⧸ φ.gnsNullIdeal

/-- The quotient map A₀ →ₗ[ℝ] A₀ ⧸ N_φ. -/
def gnsQuotientMk : FreeStarAlgebra n →ₗ[ℝ] φ.gnsQuotient := φ.gnsNullIdeal.mkQ

/-- Apply the quotient map. -/
theorem gnsQuotientMk_apply (a : FreeStarAlgebra n) :
    φ.gnsQuotientMk a = Submodule.Quotient.mk a := rfl

/-- Surjectivity of the quotient map. -/
theorem gnsQuotient_mk_surjective :
    Function.Surjective (Submodule.Quotient.mk (p := φ.gnsNullIdeal)) :=
  Submodule.Quotient.mk_surjective φ.gnsNullIdeal

/-! ### Well-definedness lemmas for inner product -/

/-- If a₁ - a₂ ∈ N_φ, then φ(star b * a₁) = φ(star b * a₂). -/
theorem sesqForm_eq_of_sub_mem_left {a₁ a₂ : FreeStarAlgebra n}
    (ha : a₁ - a₂ ∈ φ.gnsNullIdeal) (b : FreeStarAlgebra n) :
    φ (star b * a₁) = φ (star b * a₂) := by
  have h_null : φ (star (a₁ - a₂) * (a₁ - a₂)) = 0 := ha
  have h_zero : φ (star b * (a₁ - a₂)) = 0 :=
    apply_star_mul_eq_zero_of_apply_star_self_eq_zero φ h_null b
  -- φ(star b * a₁) = φ(star b * a₂ + star b * (a₁ - a₂)) = φ(star b * a₂) + 0 = φ(star b * a₂)
  have hexp : star b * a₁ = star b * a₂ + star b * (a₁ - a₂) := by
    rw [mul_sub, add_sub_cancel]
  rw [hexp, φ.map_add, h_zero, add_zero]

/-- If b₁ - b₂ ∈ N_φ, then φ(star b₁ * a) = φ(star b₂ * a). -/
theorem sesqForm_eq_of_sub_mem_right {b₁ b₂ : FreeStarAlgebra n}
    (hb : b₁ - b₂ ∈ φ.gnsNullIdeal) (a : FreeStarAlgebra n) :
    φ (star b₁ * a) = φ (star b₂ * a) := by
  have h_null : φ (star (b₁ - b₂) * (b₁ - b₂)) = 0 := hb
  -- φ(star a * (b₁ - b₂)) = 0 by Cauchy-Schwarz
  have h_left : φ (star a * (b₁ - b₂)) = 0 :=
    apply_star_mul_eq_zero_of_apply_star_self_eq_zero φ h_null a
  -- φ(star(b₁ - b₂) * a) = φ(star a * (b₁ - b₂)) by sesqForm_symm
  have h_right : φ (star (b₁ - b₂) * a) = 0 := by
    rw [sesqForm_symm φ (b₁ - b₂) a, h_left]
  -- φ(star b₁ * a) = φ(star b₂ * a + star(b₁-b₂) * a) = φ(star b₂ * a) + 0 = φ(star b₂ * a)
  have hexp : star b₁ * a = star b₂ * a + star (b₁ - b₂) * a := by
    rw [star_sub, sub_mul, add_sub_cancel]
  rw [hexp, φ.map_add, h_right, add_zero]

/-- Combined well-definedness: the sesquilinear form descends to the quotient. -/
theorem sesqForm_eq_of_sub_mem {a₁ a₂ b₁ b₂ : FreeStarAlgebra n}
    (ha : a₁ - a₂ ∈ φ.gnsNullIdeal) (hb : b₁ - b₂ ∈ φ.gnsNullIdeal) :
    φ (star b₁ * a₁) = φ (star b₂ * a₂) :=
  calc φ (star b₁ * a₁) = φ (star b₁ * a₂) := sesqForm_eq_of_sub_mem_left φ ha b₁
    _ = φ (star b₂ * a₂) := sesqForm_eq_of_sub_mem_right φ hb a₂

/-! ### The inner product definition -/

/-- Helper: convert from quotient relation to submodule membership. -/
private theorem quotient_rel_to_mem {a b : FreeStarAlgebra n}
    (h : φ.gnsNullIdeal.quotientRel a b) : a - b ∈ φ.gnsNullIdeal := by
  have h1 : -a + b ∈ φ.gnsNullIdeal := QuotientAddGroup.leftRel_apply.mp h
  have h2 : b - a ∈ φ.gnsNullIdeal := by convert h1 using 1; abel
  simpa only [neg_sub] using φ.gnsNullIdeal.neg_mem h2

/-- The inner product on the GNS quotient: ⟨[a], [b]⟩ = φ(star b * a).
    This is ℝ-valued since MPositiveState maps to ℝ. -/
def gnsInner : φ.gnsQuotient → φ.gnsQuotient → ℝ := fun x y =>
  Quotient.liftOn₂ x y (fun a b => φ (star b * a)) <| by
    intro a₁ a₂ b₁ b₂ ha hb
    exact sesqForm_eq_of_sub_mem φ (quotient_rel_to_mem φ ha) (quotient_rel_to_mem φ hb)

/-- The inner product on representatives. -/
@[simp]
theorem gnsInner_mk (a b : FreeStarAlgebra n) :
    φ.gnsInner (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = φ (star b * a) := rfl

end MPositiveState

end FreeStarAlgebra
