/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.FormallyReal.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Finite-Dimensional Jordan Algebras

This file provides infrastructure for finite-dimensional Jordan algebras,
including rank, basis existence, and bounds on idempotent systems.

## Main definitions

* `FinDimJordanAlgebra` - Class for finite-dimensional Jordan algebras
* `jordanRank` - The dimension as a real vector space

## Main results

* `exists_basis` - Finite-dimensional Jordan algebras have finite bases
* `csoi_card_le_rank` - A CSOI has at most `jordanRank` elements
-/

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-! ### Finite-Dimensional Class -/

/-- A finite-dimensional Jordan algebra over ℝ. -/
class FinDimJordanAlgebra (J : Type*) [JordanAlgebra J] where
  finDim : FiniteDimensional ℝ J

attribute [instance] FinDimJordanAlgebra.finDim

/-! ### Rank -/

/-- The rank (dimension) of a finite-dimensional Jordan algebra. -/
noncomputable def jordanRank (J : Type*) [JordanAlgebra J] [FinDimJordanAlgebra J] : ℕ :=
  Module.finrank ℝ J

theorem jordanRank_pos [FinDimJordanAlgebra J] [Nontrivial J] : 0 < jordanRank J :=
  Module.finrank_pos

/-! ### Basis Existence -/

/-- A finite-dimensional Jordan algebra has a finite basis. -/
theorem exists_basis [FinDimJordanAlgebra J] :
    ∃ (n : ℕ) (b : Fin n → J), LinearIndependent ℝ b ∧ Submodule.span ℝ (Set.range b) = ⊤ := by
  let basis := Module.finBasis ℝ J
  exact ⟨jordanRank J, basis, basis.linearIndependent, basis.span_eq⟩

/-- The canonical basis of a finite-dimensional Jordan algebra. -/
noncomputable def finBasis [FinDimJordanAlgebra J] : Module.Basis (Fin (jordanRank J)) ℝ J :=
  Module.finBasis ℝ J

/-! ### Linear Independence of Orthogonal Idempotents -/

/-- Helper: jmul distributes over finite sums with scalars. -/
theorem jmul_sum {ι : Type*} (s : Finset ι) (e : J) (r : ι → ℝ) (f : ι → J) :
    jmul e (∑ i ∈ s, r i • f i) = ∑ i ∈ s, r i • jmul e (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jmul_zero]
  | insert x s' hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    rw [jmul_add, smul_jmul, ih]

/-- Nonzero pairwise orthogonal idempotents are linearly independent.

The proof: If ∑ rᵢ eᵢ = 0, multiply both sides by eⱼ.
Since eᵢ ∘ eⱼ = 0 for i ≠ j and eⱼ² = eⱼ, we get rⱼ eⱼ = 0.
If eⱼ ≠ 0, then rⱼ = 0. -/
theorem linearIndependent_orthog_idem {n : ℕ} {e : Fin n → J}
    (h_idem : ∀ i, IsIdempotent (e i))
    (h_orth : PairwiseOrthogonal e)
    (h_ne : ∀ i, e i ≠ 0) :
    LinearIndependent ℝ e := by
  rw [linearIndependent_iff']
  intro s r hr i hi
  -- Multiply hr by e i using left multiplication
  have hmul : jmul (e i) (∑ j ∈ s, r j • e j) = jmul (e i) 0 := congrArg (jmul (e i)) hr
  rw [jmul_zero] at hmul
  -- Expand left side: jmul distributes over sums and commutes with scalars
  rw [jmul_sum] at hmul
  -- Split sum: terms where j = i and j ≠ i
  have hsum : ∑ j ∈ s, r j • jmul (e i) (e j) =
      r i • jmul (e i) (e i) + ∑ j ∈ s.erase i, r j • jmul (e i) (e j) := by
    rw [← Finset.add_sum_erase s _ hi]
  rw [hsum] at hmul
  -- Terms with j ≠ i vanish by orthogonality
  have horth_sum : ∑ j ∈ s.erase i, r j • jmul (e i) (e j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hne : j ≠ i := Finset.ne_of_mem_erase hj
    have horth : AreOrthogonal (e i) (e j) := h_orth i j (Ne.symm hne)
    rw [horth, smul_zero]
  rw [horth_sum, add_zero] at hmul
  -- Use idempotency: e i ∘ e i = e i
  have hidem : jmul (e i) (e i) = e i := (h_idem i)
  rw [hidem] at hmul
  -- Now r i • e i = 0, and e i ≠ 0, so r i = 0
  by_contra hri
  have hsmul : r i • e i = 0 := hmul
  -- If r i ≠ 0, then e i = (r i)⁻¹ • (r i • e i) = (r i)⁻¹ • 0 = 0
  have : e i = 0 := by
    calc e i = 1 • e i := (one_smul ℝ _).symm
      _ = ((r i)⁻¹ * r i) • e i := by rw [inv_mul_cancel₀ hri]
      _ = (r i)⁻¹ • (r i • e i) := (smul_smul _ _ _).symm
      _ = (r i)⁻¹ • 0 := by rw [hsmul]
      _ = 0 := smul_zero _
  exact h_ne i this

/-! ### CSOI Cardinality Bound -/

/-- A CSOI with nonzero idempotents has cardinality at most the Jordan rank. -/
theorem csoi_card_le_rank_of_nonzero [FinDimJordanAlgebra J] {n : ℕ} (c : CSOI J n)
    (h_ne : ∀ i, c.idem i ≠ 0) :
    n ≤ jordanRank J := by
  have hli := linearIndependent_orthog_idem c.is_idem c.orthog h_ne
  have hcard := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  exact hcard

/-- The unit element is nonzero in a nontrivial Jordan algebra. -/
theorem jone_ne_zero [Nontrivial J] : (jone : J) ≠ 0 := by
  intro h
  -- If jone = 0, then for any a, a = jone ∘ a = 0 ∘ a = 0
  have hall : ∀ a : J, a = 0 := fun a => by
    calc a = jmul jone a := (jone_jmul a).symm
      _ = jmul 0 a := by rw [h]
      _ = 0 := zero_jmul a
  -- But J is nontrivial, so there exists a ≠ 0
  obtain ⟨a, b, hab⟩ := exists_pair_ne (α := J)
  exact hab (hall a ▸ hall b ▸ rfl)

/-- For a CSOI where n ≥ 1, at least one idempotent is nonzero (since they sum to 1). -/
theorem csoi_exists_nonzero [Nontrivial J] {n : ℕ} (c : CSOI J n) (_hn : 0 < n) :
    ∃ i, c.idem i ≠ 0 := by
  by_contra hall
  push_neg at hall
  have hsum : ∑ i, c.idem i = 0 := Finset.sum_eq_zero (fun i _ => hall i)
  rw [c.complete] at hsum
  exact jone_ne_zero hsum

end JordanAlgebra
