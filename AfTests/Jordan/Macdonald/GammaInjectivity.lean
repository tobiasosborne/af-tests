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
3. Show `full_gamma_tensor` is injective (monomial separation via `encode_word`)
4. On symmetric tensors, `gamma_mac_tensor = full_gamma_tensor`, hence injective

## Main results

* `FA_to_FA3_star` — `FA_to_FA3` commutes with the star (word-reversal) involution
* `full_gamma_tensor` — linear map `FA ⊗ FA → FA3` sending `p ⊗ q ↦ p·z·q*`
* `gamma_mac_tensor` — symmetrized gamma as linear map, agrees with `gamma_mac`
* `gamma_mac_eq_full_on_sym` — on symmetric tensors the two maps coincide
* `full_gamma_tensor_injective` — injectivity of `full_gamma_tensor`
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

/-! ### Helper definitions and lemmas for injectivity proof -/

/-- `basisFreeMonoid m` equals `equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.of m)`. -/
private lemma basis_eq_equiv_symm_of (R : Type*) (X : Type*) [CommSemiring R]
    (m : FreeMonoid X) :
    (FreeAlgebra.basisFreeMonoid R X) m =
    FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.of R _ m) := by
  simp [FreeAlgebra.basisFreeMonoid, Module.Basis.map_apply,
        MonoidAlgebra.of_apply]; rfl

/-- `basisFreeMonoid` is multiplicative. -/
theorem basisFreeMonoid_mul (R : Type*) (X : Type*) [CommSemiring R]
    (m₁ m₂ : FreeMonoid X) :
    (FreeAlgebra.basisFreeMonoid R X) (m₁ * m₂) =
    (FreeAlgebra.basisFreeMonoid R X) m₁ *
    (FreeAlgebra.basisFreeMonoid R X) m₂ := by
  simp only [basis_eq_equiv_symm_of, ← map_mul, ← map_mul]

/-- `basisFreeMonoid (of i)` equals `ι i`. -/
lemma basisFreeMonoid_of (R : Type*) (X : Type*) [CommSemiring R]
    (i : X) :
    (FreeAlgebra.basisFreeMonoid R X) (FreeMonoid.of i) =
    FreeAlgebra.ι R i := by
  rw [basis_eq_equiv_symm_of]
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]

/-- `basisFreeMonoid 1` equals `1`. -/
lemma basisFreeMonoid_one (R : Type*) (X : Type*) [CommSemiring R] :
    (FreeAlgebra.basisFreeMonoid R X) 1 = 1 := by
  rw [basis_eq_equiv_symm_of]; simp [map_one]

/-- Star reverses the monoid word in `basisFreeMonoid`. -/
theorem star_basisFreeMonoid (X : Type*)
    (m : FreeMonoid X) :
    star ((FreeAlgebra.basisFreeMonoid ℝ X) m) =
    (FreeAlgebra.basisFreeMonoid ℝ X) m.reverse := by
  induction m using FreeMonoid.recOn with
  | h0 =>
    simp only [basisFreeMonoid_one, star_one]
    change 1 = (FreeAlgebra.basisFreeMonoid ℝ X) (FreeMonoid.reverse 1)
    rw [show (FreeMonoid.reverse (1 : FreeMonoid X) = 1) from rfl,
        basisFreeMonoid_one]
  | ih x xs ih =>
    rw [basisFreeMonoid_mul, star_mul, ih]
    rw [basisFreeMonoid_of, FreeAlgebra.star_ι,
        ← basisFreeMonoid_of ℝ X x, ← basisFreeMonoid_mul]
    rw [FreeMonoid.reverse_mul, FreeMonoid.reverse_of]

/-- `FA_to_FA3` maps `basisFreeMonoid m` to
    `basisFreeMonoid (FreeMonoid.map Fin.castSucc m)`. -/
theorem FA_to_FA3_basisFreeMonoid (m : FreeMonoid (Fin 2)) :
    FA_to_FA3 ((FreeAlgebra.basisFreeMonoid ℝ (Fin 2)) m) =
    (FreeAlgebra.basisFreeMonoid ℝ (Fin 3))
      (FreeMonoid.map Fin.castSucc m) := by
  induction m using FreeMonoid.recOn with
  | h0 =>
    rw [basisFreeMonoid_one, map_one]
    change 1 = (FreeAlgebra.basisFreeMonoid ℝ (Fin 3))
      (FreeMonoid.map Fin.castSucc 1)
    rw [map_one, basisFreeMonoid_one]
  | ih x xs ih =>
    rw [basisFreeMonoid_mul, map_mul, ih]
    rw [basisFreeMonoid_of, FA_to_FA3, FreeAlgebra.lift_ι_apply]
    rw [← basisFreeMonoid_of ℝ (Fin 3) (Fin.castSucc x)]
    rw [← basisFreeMonoid_mul]
    rfl

/-- Encode a pair of FA-monomials as a single FA3-monomial
    with z as separator. -/
noncomputable def encode_word
    (p : FreeMonoid (Fin 2) × FreeMonoid (Fin 2)) :
    FreeMonoid (Fin 3) :=
  FreeMonoid.map Fin.castSucc p.1 * FreeMonoid.of (2 : Fin 3) *
    (FreeMonoid.map Fin.castSucc p.2).reverse

private lemma castSucc_ne_two (x : Fin 2) :
    Fin.castSucc x ≠ (2 : Fin 3) := by
  intro h
  have h2 : (Fin.castSucc x).val = (2 : Fin 3).val :=
    congrArg Fin.val h
  simp [Fin.castSucc] at h2; omega

private lemma two_not_mem_map_castSucc (m : FreeMonoid (Fin 2)) :
    (2 : Fin 3) ∉
    (FreeMonoid.toList (FreeMonoid.map Fin.castSucc m)) := by
  rw [FreeMonoid.toList_map]
  intro h; obtain ⟨x, _, hx⟩ := List.mem_map.mp h
  exact castSucc_ne_two x hx

private lemma list_split_at_unique_sep {α : Type*} {sep : α}
    {L₁ R₁ L₂ R₂ : List α}
    (hL₁ : sep ∉ L₁) (hL₂ : sep ∉ L₂)
    (h : L₁ ++ [sep] ++ R₁ = L₂ ++ [sep] ++ R₂) :
    L₁ = L₂ ∧ R₁ = R₂ := by
  induction L₁ generalizing L₂ with
  | nil =>
    simp at h; cases L₂ with
    | nil => simp at h; exact ⟨rfl, h⟩
    | cons a L₂ =>
      simp at h hL₂
      exact absurd h.1.symm (Ne.symm hL₂.1)
  | cons a L₁ ih =>
    cases L₂ with
    | nil =>
      simp at h hL₁
      exact absurd h.1 (Ne.symm hL₁.1)
    | cons b L₂ =>
      simp only [List.cons_append, List.cons.injEq] at h
      simp only [List.mem_cons, not_or] at hL₁ hL₂
      obtain ⟨hab, htail⟩ := h
      have := ih hL₁.2 hL₂.2 htail
      exact ⟨by rw [hab, this.1], this.2⟩

private lemma castSucc_injective :
    Function.Injective (Fin.castSucc : Fin 2 → Fin 3) := by
  intro a b h
  simp [Fin.castSucc, Fin.ext_iff] at h
  exact Fin.ext h

private lemma freeMonoid_map_injective {α β : Type*}
    (f : α → β) (hf : Function.Injective f) :
    Function.Injective (FreeMonoid.map f) := by
  intro m₁ m₂ h
  have : FreeMonoid.toList ((FreeMonoid.map f) m₁) =
         FreeMonoid.toList ((FreeMonoid.map f) m₂) :=
    congrArg FreeMonoid.toList h
  rw [FreeMonoid.toList_map, FreeMonoid.toList_map] at this
  exact FreeMonoid.toList.injective
    (List.map_injective_iff.mpr hf this)

/-- `encode_word` is injective: distinct monomial pairs produce
    distinct FA3-words because `z` uniquely separates them. -/
theorem encode_word_injective :
    Function.Injective encode_word := by
  intro ⟨m₁, m₂⟩ ⟨n₁, n₂⟩ h
  simp only [encode_word] at h
  have hlist :
      FreeMonoid.toList (FreeMonoid.map Fin.castSucc m₁) ++
      [(2 : Fin 3)] ++
      FreeMonoid.toList
        (FreeMonoid.map Fin.castSucc m₂).reverse =
      FreeMonoid.toList (FreeMonoid.map Fin.castSucc n₁) ++
      [(2 : Fin 3)] ++
      FreeMonoid.toList
        (FreeMonoid.map Fin.castSucc n₂).reverse := by
    have := congrArg FreeMonoid.toList h
    simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of] at this
    exact this
  have ⟨hleft, hright⟩ := list_split_at_unique_sep
    (two_not_mem_map_castSucc m₁) (two_not_mem_map_castSucc n₁)
    hlist
  have hm₁ : m₁ = n₁ := freeMonoid_map_injective _
    castSucc_injective (FreeMonoid.toList.injective hleft)
  have hm₂ : m₂ = n₂ := by
    have hrev := List.reverse_injective (α := Fin 3) hright
    exact freeMonoid_map_injective _ castSucc_injective
      (FreeMonoid.toList.injective hrev)
  exact Prod.ext hm₁ hm₂

/-- `full_gamma_tensor` maps basis vectors to basis vectors
    via `encode_word`. -/
theorem full_gamma_tensor_on_basis
    (m₁ m₂ : FreeMonoid (Fin 2)) :
    full_gamma_tensor
      ((FreeAlgebra.basisFreeMonoid ℝ (Fin 2)) m₁ ⊗ₜ[ℝ]
       (FreeAlgebra.basisFreeMonoid ℝ (Fin 2)) m₂) =
    (FreeAlgebra.basisFreeMonoid ℝ (Fin 3))
      (encode_word (m₁, m₂)) := by
  rw [full_gamma_tensor_tmul]
  rw [FA_to_FA3_basisFreeMonoid, FA_to_FA3_basisFreeMonoid]
  rw [star_basisFreeMonoid]
  rw [show FA3.z = (FreeAlgebra.basisFreeMonoid ℝ (Fin 3))
    (FreeMonoid.of (2 : Fin 3))
    from (basisFreeMonoid_of ℝ (Fin 3) (2 : Fin 3)).symm]
  rw [← basisFreeMonoid_mul, ← basisFreeMonoid_mul]; rfl

/-- Generic injectivity: if `f` sends a basis to a linearly
    independent family, then `f` is injective. -/
lemma injective_of_basis_image_linIndep {ι : Type*}
    {R : Type*} {M N : Type*}
    [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (b : Module.Basis ι R M) (f : M →ₗ[R] N)
    (hli : LinearIndependent R (f ∘ b)) :
    Function.Injective f := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx; rw [LinearMap.mem_ker] at hx
  have hrepr := (b.linearCombination_repr x).symm
  rw [hrepr, LinearMap.map_finsupp_linearCombination] at hx
  have hzero : b.repr x = 0 := by
    have h0 :
        (Finsupp.linearCombination R (⇑f ∘ ⇑b)) (b.repr x) =
        (Finsupp.linearCombination R (⇑f ∘ ⇑b)) 0 := by
      rw [hx, map_zero]
    exact hli h0
  rw [hrepr, hzero, map_zero]

/-! ### Injectivity of full_gamma_tensor -/

/-- `full_gamma_tensor` is injective.

The map on the basis `(m₁, m₂)` of `FA ⊗ FA` sends each basis
vector `m₁ ⊗ m₂` to the single `FA3`-basis vector
`m₁ · [2] · reverse(m₂)` in `FreeMonoid (Fin 3)`. Different
`(m₁, m₂)` give different `FA3`-words because `z` uniquely
separates left and right parts. -/
theorem full_gamma_tensor_injective :
    Function.Injective full_gamma_tensor := by
  set b := (FreeAlgebra.basisFreeMonoid ℝ (Fin 2)).tensorProduct
            (FreeAlgebra.basisFreeMonoid ℝ (Fin 2))
  set b3 := FreeAlgebra.basisFreeMonoid ℝ (Fin 3)
  apply injective_of_basis_image_linIndep b
  have hfb : ∀ p, (full_gamma_tensor ∘ b) p =
      (b3 ∘ encode_word) p := by
    intro ⟨m₁, m₂⟩
    simp only [Function.comp]
    change full_gamma_tensor (b (m₁, m₂)) =
      b3 (encode_word (m₁, m₂))
    rw [show b (m₁, m₂) =
      (FreeAlgebra.basisFreeMonoid ℝ (Fin 2)) m₁ ⊗ₜ[ℝ]
      (FreeAlgebra.basisFreeMonoid ℝ (Fin 2)) m₂
      from Module.Basis.tensorProduct_apply _ _ m₁ m₂]
    exact full_gamma_tensor_on_basis m₁ m₂
  rw [show (full_gamma_tensor ∘ ⇑b) = (⇑b3 ∘ encode_word)
    from funext hfb]
  exact b3.linearIndependent.comp _ encode_word_injective

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
