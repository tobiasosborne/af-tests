/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Macdonald.TensorSetup
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.FreeAlgebra
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Gamma Injectivity for Macdonald's Theorem (Step 15)

Proves that `gamma_mac` is injective on symmetric tensors of `FA ⊗ FA`.

## Strategy

1. Define `full_gamma_bilin(p, q) = FA_to_FA3(p) * z * star(FA_to_FA3(q))` (unsymmetrized)
2. Lift to `full_gamma_tensor : FA ⊗ FA →ₗ[ℝ] FA3` via `TensorProduct.lift`
3. Show `full_gamma_tensor` is injective (monomial separation — sorry'd)
4. On symmetric tensors, `gamma_mac_tensor = full_gamma_tensor`, hence injective

## Main results

* `FA_to_FA3_star` — `FA_to_FA3` commutes with the star (word-reversal) involution
* `full_gamma_tensor` — linear map `FA ⊗ FA → FA3` sending `p ⊗ q ↦ p·z·q*`
* `gamma_mac_tensor` — symmetrized gamma as linear map, agrees with `gamma_mac`
* `gamma_mac_eq_full_on_sym` — on symmetric tensors the two maps coincide
* `full_gamma_tensor_injective` — injectivity of `full_gamma_tensor` (sorry'd)
* `gamma_mac_injective_symTensor` — injectivity of `gamma_mac` on `symTensor`
-/

/-! ### StarModule instance for FA3 -/

instance : StarModule ℝ FA3 where
  star_smul r a := by
    simp only [Algebra.smul_def, star_mul, FreeAlgebra.star_algebraMap, star_trivial]
    rw [Algebra.commutes]

/-! ### FA_to_FA3 commutes with star -/

/-- `FA_to_FA3` commutes with the star (word-reversal) involution.
    Both star operations fix generators, and `FA_to_FA3` maps generators to generators,
    so the two anti-homomorphisms `star ∘ FA_to_FA3` and `FA_to_FA3 ∘ star` agree. -/
theorem FA_to_FA3_star (p : FA) : FA_to_FA3 (star p) = star (FA_to_FA3 p) := by
  induction p using FreeAlgebra.induction with
  | grade0 r => simp [FA_to_FA3, FreeAlgebra.star_algebraMap, AlgHom.commutes]
  | grade1 i => simp [FA_to_FA3, FreeAlgebra.star_ι, FreeAlgebra.lift_ι_apply]
  | mul a b ha hb => simp [star_mul, map_mul, ha, hb]
  | add a b ha hb => simp [star_add, map_add, ha, hb]

/-! ### Unsymmetrized gamma: full_gamma -/

/-- The unsymmetrized gamma: `(p, q) ↦ FA_to_FA3(p) * z * star(FA_to_FA3(q))`.
    This is bilinear over ℝ and lifts to the tensor product. -/
noncomputable def full_gamma_bilin : FA →ₗ[ℝ] FA →ₗ[ℝ] FA3 where
  toFun p := {
    toFun := fun q => FA_to_FA3 p * FA3.z * star (FA_to_FA3 q)
    map_add' := fun q₁ q₂ => by simp only [map_add, star_add, mul_add]
    map_smul' := fun r q => by
      simp only [map_smul, star_smul, star_trivial, mul_smul_comm, RingHom.id_apply]
  }
  map_add' p₁ p₂ := by
    ext q
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_add, add_mul, LinearMap.add_apply]
  map_smul' r p := by
    ext q
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_smul,
               Algebra.smul_mul_assoc, LinearMap.smul_apply, RingHom.id_apply]

/-- Lift of `full_gamma_bilin` to the tensor product `FA ⊗ FA → FA3`. -/
noncomputable def full_gamma_tensor : FA2 →ₗ[ℝ] FA3 :=
  TensorProduct.lift full_gamma_bilin

@[simp] theorem full_gamma_tensor_tmul (p q : FA) :
    full_gamma_tensor (p ⊗ₜ[ℝ] q) = FA_to_FA3 p * FA3.z * star (FA_to_FA3 q) := by
  simp [full_gamma_tensor, full_gamma_bilin, TensorProduct.lift.tmul]

/-! ### Symmetrized gamma as a linear map -/

/-- The symmetrized gamma as a linear map on `FA ⊗ FA`:
    `t ↦ ½(full_gamma(t) + full_gamma(comm(t)))`.
    This agrees with `gamma_mac` on pure tensors. -/
noncomputable def gamma_mac_tensor : FA2 →ₗ[ℝ] FA3 :=
  (1/2 : ℝ) • (full_gamma_tensor +
    full_gamma_tensor ∘ₗ (TensorProduct.comm ℝ FA FA).toLinearMap)

/-- `gamma_mac_tensor` agrees with `gamma_mac` on pure tensors. -/
theorem gamma_mac_tensor_tmul (p q : FA) :
    gamma_mac_tensor (p ⊗ₜ[ℝ] q) = gamma_mac p q := by
  simp only [gamma_mac_tensor, LinearMap.smul_apply, LinearMap.add_apply,
             LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, TensorProduct.comm_tmul,
             full_gamma_tensor_tmul]
  unfold gamma_mac; rfl

/-! ### Key lemma: gamma_mac = full_gamma on symmetric tensors -/

/-- On symmetric tensors, `gamma_mac_tensor = full_gamma_tensor`.
    Since `comm(t) = t` for symmetric `t`, the symmetrization is the identity. -/
theorem gamma_mac_eq_full_on_sym (t : FA2) (ht : t ∈ symTensor) :
    gamma_mac_tensor t = full_gamma_tensor t := by
  have hcomm : (TensorProduct.comm ℝ FA FA).toLinearMap t = t := by
    change LinearMap.id t = (TensorProduct.comm ℝ FA FA).toLinearMap t at ht
    exact ht.symm
  simp only [gamma_mac_tensor, LinearMap.smul_apply, LinearMap.add_apply,
             LinearMap.comp_apply, hcomm]
  rw [← two_smul ℝ (full_gamma_tensor t), smul_smul]; norm_num

/-! ### Injectivity of full_gamma_tensor -/

/-- `full_gamma_tensor` is injective.

**Proof sketch** (sorry'd — this is the hard monomial-separation argument):
The monomials `m₁ · z · reverse(m₂)` in `FA3` are distinct basis elements
for distinct pairs `(m₁, m₂)` of `FreeMonoid (Fin 2)` monomials.

Since `z = ι 2` is not in the image of `FA_to_FA3` (which only uses `ι 0, ι 1`),
each `FA_to_FA3(p) * FA3.z * star(FA_to_FA3(q))` expands uniquely in the
`FreeAlgebra.basisFreeMonoid` basis of `FA3`.

Formally: the map on the basis `(m₁, m₂)` of `FA ⊗ FA` (via `Basis.tensorProduct`
of `FreeAlgebra.basisFreeMonoid ℝ (Fin 2)` with itself) sends each basis vector
`m₁ ⊗ m₂` to the single `FA3`-basis vector `m₁ · [2] · reverse(m₂)` in
`FreeMonoid (Fin 3)`. Different `(m₁, m₂)` give different `FA3`-words because `z`
uniquely separates left and right parts. This establishes linear independence of
the image and hence injectivity. -/
theorem full_gamma_tensor_injective : Function.Injective full_gamma_tensor := by
  sorry

/-! ### Main result: gamma_mac injectivity on symmetric tensors -/

/-- `gamma_mac` is injective on symmetric tensors: if `t ∈ symTensor` and
    `gamma_mac_tensor t = 0`, then `t = 0`.

This is Step 15 of the Macdonald theorem proof (H-O 2.4.25).
The proof reduces to injectivity of `full_gamma_tensor` via `gamma_mac_eq_full_on_sym`. -/
theorem gamma_mac_injective_symTensor :
    Function.Injective (gamma_mac_tensor.domRestrict symTensor) := by
  intro ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ h
  simp only [LinearMap.domRestrict_apply, Subtype.mk.injEq] at h ⊢
  rw [gamma_mac_eq_full_on_sym t₁ ht₁, gamma_mac_eq_full_on_sym t₂ ht₂] at h
  exact full_gamma_tensor_injective h
