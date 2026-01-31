/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.FiniteDimensional
import AfTests.Jordan.Trace
import AfTests.Jordan.Peirce
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Artinian.Module

/-!
# Primitive Idempotents in Jordan Algebras

A primitive idempotent is a nonzero idempotent that cannot be decomposed as a sum of
orthogonal idempotents. This file develops the theory of primitive idempotents.

## Main definitions

* `IsPrimitive` - Predicate for primitive idempotents
* `IsStronglyConnected` - Two orthogonal idempotents are strongly connected
* `exists_primitive_decomp` - Every nonzero idempotent decomposes into primitives

## Main results

* `isPrimitive_of_minimal` - Minimal idempotents are primitive
* `orthogonal_primitive_structure` - H-O 2.9.4(iv): orthogonal primitives are
  either in disjoint subalgebras or strongly connected

## References

* Hanche-Olsen & Størmer, *Jordan Operator Algebras*, Section 2.9
-/

open Finset BigOperators

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-! ### Primitive Idempotent Definition -/

/-- An idempotent is primitive if it cannot be decomposed into orthogonal idempotents.
Equivalently, e is primitive if whenever f is an idempotent with e ∘ f = f, then f = 0 or f = e. -/
def IsPrimitive (e : J) : Prop :=
  IsIdempotent e ∧ e ≠ 0 ∧ ∀ f, IsIdempotent f → jmul e f = f → f = 0 ∨ f = e

theorem IsPrimitive.isIdempotent {e : J} (h : IsPrimitive e) : IsIdempotent e := h.1

theorem IsPrimitive.ne_zero {e : J} (h : IsPrimitive e) : e ≠ 0 := h.2.1

theorem IsPrimitive.sub_eq_zero {e : J} (h : IsPrimitive e) (f : J) (hf : IsIdempotent f)
    (hef : jmul e f = f) : f = 0 ∨ f = e := h.2.2 f hf hef

/-- Constructor for primitive idempotents from minimality condition. -/
theorem isPrimitive_of_minimal {e : J} (he : IsIdempotent e) (hne : e ≠ 0)
    (hmin : ∀ f, IsIdempotent f → f ≠ 0 → jmul e f = f → f = e) : IsPrimitive e := by
  refine ⟨he, hne, fun f hf hef => ?_⟩
  rcases eq_or_ne f 0 with rfl | hfne
  · left; rfl
  · right; exact hmin f hf hfne hef

/-! ### Properties of Primitive Idempotents -/

/-- If e is primitive and f is an idempotent orthogonal to e, then e and f are disjoint. -/
theorem IsPrimitive.orthog_of_ne {e f : J} (he : IsPrimitive e) (hf : IsIdempotent f)
    (hef : jmul e f = f) (hne : f ≠ e) : f = 0 :=
  (he.sub_eq_zero f hf hef).resolve_right hne

/-- Primitive idempotents are absorbed by their complements. -/
theorem IsPrimitive.jmul_complement {e : J} (he : IsPrimitive e) :
    jmul e (jone - e) = 0 :=
  jone_sub_idempotent_orthogonal he.isIdempotent

/-! ### Field Classification Results (H-O 2.2.6) -/

/-- Frobenius theorem: A finite-dimensional field over ℝ is isomorphic to ℝ or ℂ.
This is H-O 2.2.6. The proof uses that finite-dimensional implies algebraic,
then applies `Real.nonempty_algEquiv_or` from mathlib. -/
theorem finite_dim_field_over_real (F : Type*) [Field F] [Algebra ℝ F]
    [FiniteDimensional ℝ F] :
    Nonempty (F ≃ₐ[ℝ] ℝ) ∨ Nonempty (F ≃ₐ[ℝ] ℂ) :=
  Real.nonempty_algEquiv_or F

/-- ℂ is not formally real: i² + 1² = 0 but i ≠ 0. -/
theorem complex_not_formally_real :
    ∃ (n : ℕ) (a : Fin n → ℂ), (∑ i, a i ^ 2) = 0 ∧ ∃ i, a i ≠ 0 := by
  use 2, ![Complex.I, 1]
  constructor
  · simp [Fin.sum_univ_two, Complex.I_sq]
  · use 0; simp [Complex.I_ne_zero]

/-- A formally real finite-dimensional field over ℝ is isomorphic to ℝ.
This is used in the proof of H-O 2.9.4(ii): since ℂ is not formally real
(i² + 1² = 0), any formally real field must be ℝ. -/
theorem formallyReal_field_is_real (F : Type*) [Field F] [Algebra ℝ F]
    [FiniteDimensional ℝ F]
    (hfr : ∀ (n : ℕ) (a : Fin n → F), (∑ i, a i ^ 2) = 0 → ∀ i, a i = 0) :
    Nonempty (F ≃ₐ[ℝ] ℝ) := by
  cases Real.nonempty_algEquiv_or F with
  | inl h => exact h
  | inr h =>
    -- F ≅ ℂ, contradiction with formal reality
    exfalso
    obtain ⟨e⟩ := h
    obtain ⟨n, a, hsum, i, hi⟩ := complex_not_formally_real
    -- Transfer to F via the isomorphism
    let a' : Fin n → F := fun j => e.symm (a j)
    have hsum' : ∑ j, a' j ^ 2 = 0 := by
      have heq : e (∑ j, a' j ^ 2) = 0 := by
        simp only [map_sum, map_pow, a', AlgEquiv.apply_symm_apply, hsum]
      exact e.injective (by simp [heq])
    have ha'i : a' i ≠ 0 := by
      intro h
      apply hi
      have : e (a' i) = 0 := by simp only [h, map_zero]
      simp only [a', AlgEquiv.apply_symm_apply] at this
      exact this
    exact ha'i (hfr n a' hsum' i)

/-! ### Artinian Ring Structure Theorem (H-O 2.9.3) -/

/-- An Artinian reduced commutative ring decomposes as a product of fields.
This is H-O Lemma 2.9.3. The proof uses mathlib's `IsArtinianRing.equivPi`. -/
noncomputable def artinian_reduced_is_product_of_fields (R : Type*) [CommRing R]
    [IsArtinianRing R] [IsReduced R] :
    R ≃+* ((I : MaximalSpectrum R) → R ⧸ I.asIdeal) :=
  IsArtinianRing.equivPi R

/-- Each factor in the decomposition of an Artinian reduced ring is a field. -/
noncomputable instance artinian_reduced_factor_field (R : Type*) [CommRing R]
    [IsArtinianRing R] [IsReduced R] (I : MaximalSpectrum R) : Field (R ⧸ I.asIdeal) :=
  IsArtinianRing.fieldOfSubtypeIsMaximal R I

/-! ### Strongly Connected Idempotents -/

/-- Two orthogonal idempotents are strongly connected if there exists v in the Peirce ½
space between them such that v² = e + f. This is the key structure in Jordan algebras
that enables the coordinatization theorem. (H-O Definition 2.8.1) -/
def IsStronglyConnected (e f : J) : Prop :=
  AreOrthogonal e f ∧ ∃ v : J,
    jmul e v = (1 / 2 : ℝ) • v ∧ jmul f v = (1 / 2 : ℝ) • v ∧ jsq v = e + f

/-! ### Structure of Orthogonal Primitives (H-O 2.9.4(iv)) -/

/-- For a primitive idempotent e, every element x in PeirceSpace e 1 satisfies x = r • e.
This is H-O 2.9.4(ii): primitivity is equivalent to {eAe} = ℝe.
The proof uses finite-dimensionality: if PeirceSpace e 1 has dimension > 1,
there would exist a non-trivial idempotent contradicting primitivity. -/
theorem primitive_peirce_one_scalar [FinDimJordanAlgebra J] [FormallyRealJordan J]
    {e : J} (he : IsPrimitive e) {x : J} (hx : x ∈ PeirceSpace e 1) :
    ∃ r : ℝ, x = r • e := by
  -- In a finite-dimensional formally real Jordan algebra, if e is primitive,
  -- then PeirceSpace e 1 = ℝ • e (one-dimensional).
  -- The proof requires showing that higher-dimensional Peirce-1 spaces contain
  -- non-trivial idempotents, contradicting primitivity.
  sorry

/-- In a formally real finite-dimensional Jordan algebra, for orthogonal minimal
idempotents p, q, the element a² (where a ∈ {pAq}) satisfies a² = μ(p+q) for some μ ≥ 0.
This is H-O Lemma 2.9.4(iv). -/
theorem orthogonal_primitive_peirce_sq [FinDimJordanAlgebra J] [FormallyRealJordan J] {e f : J}
    (he : IsPrimitive e) (hf : IsPrimitive f) (horth : AreOrthogonal e f)
    {a : J} (ha_peirce : jmul e a = (1 / 2 : ℝ) • a ∧ jmul f a = (1 / 2 : ℝ) • a) :
    ∃ μ : ℝ, 0 ≤ μ ∧ jsq a = μ • (e + f) := by
  -- Step 1: By peirce_mult_P12_P12, a² ∈ P₀(e) ⊕ P₁(e) and a² ∈ P₀(f) ⊕ P₁(f)
  have ha_in_P12_e : a ∈ PeirceSpace e (1/2) := by rw [mem_peirceSpace_iff]; exact ha_peirce.1
  have ha_in_P12_f : a ∈ PeirceSpace f (1/2) := by rw [mem_peirceSpace_iff]; exact ha_peirce.2
  have h_sq_e := peirce_mult_P12_P12 he.isIdempotent ha_in_P12_e ha_in_P12_e
  have h_sq_f := peirce_mult_P12_P12 hf.isIdempotent ha_in_P12_f ha_in_P12_f
  -- Step 2: Decompose a² w.r.t. e: a² = c₀ + c₁ where c₀ ∈ P₀(e), c₁ ∈ P₁(e)
  rw [Submodule.mem_sup] at h_sq_e h_sq_f
  obtain ⟨c₀e, hc₀e, c₁e, hc₁e, heq_e⟩ := h_sq_e
  obtain ⟨c₀f, hc₀f, c₁f, hc₁f, heq_f⟩ := h_sq_f
  -- Step 3: By primitivity, c₁e = r₁ • e and c₁f = r₂ • f
  obtain ⟨r₁, hr₁⟩ := primitive_peirce_one_scalar he hc₁e
  obtain ⟨r₂, hr₂⟩ := primitive_peirce_one_scalar hf hc₁f
  -- Step 4: Show r₁ = r₂ using symmetry of the setup
  -- Key observation: e and f are symmetric in the hypotheses, so the coefficients must be equal
  -- This follows from examining: jmul e (jsq a) vs jmul f (jsq a)
  -- Step 5: Show c₀e = r₂ • f and c₀f = r₁ • e
  -- Since e ∈ P₀(f) and f ∈ P₀(e), we need orthogonality analysis
  -- The full proof requires showing that the cross-terms align
  sorry

/-- For orthogonal primitive idempotents in a formally real Jordan algebra,
either their Peirce ½ space is trivial or they are strongly connected.
This is the key dichotomy from H-O 2.9.4(iv). -/
theorem orthogonal_primitive_structure [FinDimJordanAlgebra J] [FormallyRealJordan J] {e f : J}
    (he : IsPrimitive e) (hf : IsPrimitive f) (horth : AreOrthogonal e f) :
    (∀ a : J, jmul e a = (1 / 2 : ℝ) • a → jmul f a = (1 / 2 : ℝ) • a → a = 0) ∨
    IsStronglyConnected e f := by
  -- If there exists nonzero a in the Peirce ½ space, then by orthogonal_primitive_peirce_sq,
  -- a² = μ(e+f) with μ > 0 (μ = 0 would mean a² = 0, hence a = 0 by formal reality).
  -- Then (μ^{-1/2} a)² = e + f, so e and f are strongly connected.
  sorry

/-! ### Note on "Primitive Dichotomy"

The naive statement "two primitives are orthogonal or equal" is FALSE.

**Counterexample (H-O 2.9.8):** In 2×2 symmetric matrices over ℝ:
- e = diag(1,0)
- f = [[1/2,1/2],[1/2,1/2]]

Both are primitive (rank-1 projections), but:
- jmul e f ≠ 0 (not orthogonal)
- e ≠ f

The correct theory (H-O Section 2.9):
1. Every element lies in a maximal associative subalgebra (H-O 2.9.4(iii))
2. Such subalgebras decompose as ℝp₁ ⊕ ... ⊕ ℝpₙ with pairwise orthogonal primitives
3. For orthogonal primitives, either {pAq} = 0 or they're strongly connected (H-O 2.9.4(iv))

The decomposition results below use *orthogonal* families of primitives.
-/

/-! ### Decomposition into Primitives -/

/-- In a finite-dimensional formally real Jordan algebra, every nonzero idempotent
decomposes as a sum of primitive idempotents. -/
theorem exists_primitive_decomp [FinDimJordanAlgebra J] [FormallyRealJordan J]
    {e : J} (he : IsIdempotent e) (hne : e ≠ 0) :
    ∃ (k : ℕ) (p : Fin k → J),
      (∀ i, IsPrimitive (p i)) ∧ PairwiseOrthogonal p ∧ e = ∑ i, p i := by
  -- Proof by strong induction on dimension:
  -- Either e is primitive, or it decomposes as e = f + g with f, g orthogonal idempotents
  -- In the latter case, apply induction to f and g
  sorry

/-- A CSOI can be refined to a primitive CSOI. -/
theorem csoi_refine_primitive [FinDimJordanAlgebra J] [FormallyRealJordan J]
    (c : CSOI J n) :
    ∃ (m : ℕ) (p : CSOI J m), m ≥ n ∧ ∀ i, IsPrimitive (p.idem i) := by
  -- Refine each idempotent in c to primitives
  sorry

end JordanAlgebra
