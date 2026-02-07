/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Macdonald.FreeSpecialJordan
import Mathlib.Algebra.Star.Free
import Mathlib.Algebra.Star.Module
import Mathlib.Data.Real.Star
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor Product Setup for Macdonald's Theorem (Steps 14-17)

Sets up the infrastructure for the tensor product embedding used in Steps 14-17
of the Macdonald theorem proof (Hanche-Olsen 2.4).

## Main definitions

* `FA` - The associative free algebra `FreeAlgebra ℝ (Fin 2)` on two generators
* `FA2` - The tensor product `FA ⊗ FA`, which has a natural algebra structure
* `symTensor` - The submodule of symmetric tensors `{t | comm(t) = t}`
* `evalFA` - Evaluation map `FreeJordanAlg → FA` (canonical surjection)
* `gamma_elem` - The gamma map on `FA`: `γ(a) = a ⊗ 1 + 1 ⊗ a`
* `gamma` - The gamma map on `FreeJordanAlg`: composition of `evalFA` and `gamma_elem`

## Main results

* `gamma_elem_symmetric` - `γ(a)` lies in the symmetric part of `FA ⊗ FA`
* `gamma_elem_add`, `gamma_elem_smul` - `gamma_elem` is ℝ-linear
* `gamma_jordan_product` - `γ(u ∘ v) = ½(γ(u)·γ(v) + γ(v)·γ(u))` (sorry'd)

## Design notes

We use Mathlib's `FreeAlgebra ℝ (Fin 2)` as the associative free algebra, connected
to the project's `FreeJordanAlg` via `evalAssoc`. The star (anti-involution) from
`Mathlib.Algebra.Star.Free` reverses words; generators are self-adjoint (`star_ι`).
The gamma map `γ(a) = a ⊗ 1 + 1 ⊗ a` lands in symmetric tensors (invariant under
`TensorProduct.comm`), which is the key structural property for Macdonald's theorem.
-/

/-! ### Free algebra FA = FreeAlgebra ℝ (Fin 2) -/

/-- The associative free ℝ-algebra on two generators. -/
abbrev FA := FreeAlgebra ℝ (Fin 2)

/-- Generator x of the associative free algebra. -/
noncomputable def FA.x : FA := FreeAlgebra.ι ℝ (0 : Fin 2)

/-- Generator y of the associative free algebra. -/
noncomputable def FA.y : FA := FreeAlgebra.ι ℝ (1 : Fin 2)

@[simp] theorem FA.star_x : star FA.x = FA.x := FreeAlgebra.star_ι (0 : Fin 2)
@[simp] theorem FA.star_y : star FA.y = FA.y := FreeAlgebra.star_ι (1 : Fin 2)

/-- `StarModule ℝ FA`: star commutes with real scalar multiplication. -/
instance : StarModule ℝ FA where
  star_smul r a := by
    simp only [Algebra.smul_def, star_mul, FreeAlgebra.star_algebraMap, star_trivial]
    rw [Algebra.commutes]

/-! ### Tensor product FA ⊗ FA -/

/-- The tensor product `FA ⊗ FA`, which inherits `Ring` and `Algebra ℝ` structure. -/
abbrev FA2 := TensorProduct ℝ FA FA

/-- Symmetric tensors: the submodule of `FA ⊗ FA` fixed by the swap map.
    An element `t` is symmetric iff `comm(t) = t` where `comm` swaps tensor factors. -/
noncomputable def symTensor : Submodule ℝ FA2 :=
  LinearMap.eqLocus LinearMap.id (TensorProduct.comm ℝ FA FA).toLinearMap

/-! ### Evaluation map: FreeJordanAlg → FA -/

/-- The canonical evaluation map sending `FreeJordanAlg` into `FA`, mapping
    generators to generators and using the Jordan (symmetrized) product `½(ab+ba)`. -/
noncomputable def evalFA : FreeJordanAlg → FA :=
  FreeJordanAlg.evalAssoc FA.x FA.y

@[simp] theorem evalFA_x : evalFA FreeJordanAlg.x = FA.x := by
  unfold evalFA; simp [FA.x]

@[simp] theorem evalFA_y : evalFA FreeJordanAlg.y = FA.y := by
  unfold evalFA; simp [FA.y]

theorem evalFA_add (u v : FreeJordanAlg) :
    evalFA (u + v) = evalFA u + evalFA v :=
  FreeJordanAlg.evalAssoc_add FA.x FA.y u v

theorem evalFA_smul (r : ℝ) (u : FreeJordanAlg) :
    evalFA (r • u) = r • evalFA u :=
  FreeJordanAlg.evalAssoc_smul FA.x FA.y r u

theorem evalFA_mul (u v : FreeJordanAlg) :
    evalFA (FreeJordanAlg.mul u v) =
    (1/2 : ℝ) • (evalFA u * evalFA v + evalFA v * evalFA u) :=
  FreeJordanAlg.evalAssoc_mul FA.x FA.y u v

/-! ### Gamma map -/

/-- The gamma map on `FA` elements: `γ(a) = a ⊗ 1 + 1 ⊗ a`.
    This maps into symmetric tensors and is the key embedding for Macdonald's theorem. -/
noncomputable def gamma_elem (a : FA) : FA2 :=
  a ⊗ₜ[ℝ] 1 + 1 ⊗ₜ[ℝ] a

/-- The gamma map on `FreeJordanAlg`: composition of `evalFA` and `gamma_elem`. -/
noncomputable def gamma (u : FreeJordanAlg) : FA2 :=
  gamma_elem (evalFA u)

@[simp] theorem gamma_x :
    gamma FreeJordanAlg.x = FA.x ⊗ₜ[ℝ] 1 + 1 ⊗ₜ[ℝ] FA.x := by
  simp [gamma, gamma_elem]

@[simp] theorem gamma_y :
    gamma FreeJordanAlg.y = FA.y ⊗ₜ[ℝ] 1 + 1 ⊗ₜ[ℝ] FA.y := by
  simp [gamma, gamma_elem]

/-! ### Properties of gamma_elem -/

/-- `γ(a)` is a symmetric tensor: swapping factors leaves it invariant. -/
theorem gamma_elem_symmetric (a : FA) : gamma_elem a ∈ symTensor := by
  change LinearMap.id (gamma_elem a) = (TensorProduct.comm ℝ FA FA).toLinearMap (gamma_elem a)
  unfold gamma_elem
  simp [map_add, TensorProduct.comm_tmul]
  abel

/-- `gamma_elem` is additive. -/
theorem gamma_elem_add (a b : FA) :
    gamma_elem (a + b) = gamma_elem a + gamma_elem b := by
  unfold gamma_elem
  rw [TensorProduct.add_tmul, TensorProduct.tmul_add]
  abel

/-- `gamma_elem` respects scalar multiplication. -/
theorem gamma_elem_smul (r : ℝ) (a : FA) :
    gamma_elem (r • a) = r • gamma_elem a := by
  unfold gamma_elem
  simp only [smul_add, TensorProduct.smul_tmul', TensorProduct.tmul_smul]

/-! ### Properties of gamma -/

/-- `γ(u)` is a symmetric tensor for any `u : FreeJordanAlg`. -/
theorem gamma_symmetric (u : FreeJordanAlg) : gamma u ∈ symTensor :=
  gamma_elem_symmetric (evalFA u)

/-- Key property: gamma maps the Jordan product to the symmetrized product in `FA ⊗ FA`.
    `γ(u ∘ v) = ½(γ(u)·γ(v) + γ(v)·γ(u))` where `·` is the tensor algebra product.
    This is the core structural lemma needed for Macdonald's theorem (Step 15). -/
theorem gamma_jordan_product (u v : FreeJordanAlg) :
    gamma (FreeJordanAlg.mul u v) =
    (1/2 : ℝ) • (gamma u * gamma v + gamma v * gamma u) := by sorry
