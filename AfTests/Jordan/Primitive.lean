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
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Span.Basic

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

/-- Powers of an element in P₁(e) stay in P₁(e) (for n ≥ 1). -/
theorem jpow_succ_mem_peirce_one {e : J} (he : IsIdempotent e) {a : J}
    (ha : a ∈ PeirceSpace e 1) (n : ℕ) : jpow a (n + 1) ∈ PeirceSpace e 1 := by
  induction n with
  | zero =>
    convert ha using 1
    exact jpow_one a
  | succ n ih =>
    rw [jpow_succ]
    exact peirce_mult_P1_P1 he ha ih

/-- Key lemma: Any idempotent in P₁(e) that satisfies jmul e f = f must be 0 or e.
This follows directly from the definition of primitive. -/
theorem primitive_idempotent_in_P1 {e : J}
    (he : IsPrimitive e) {f : J} (hf_idem : IsIdempotent f)
    (hf_in_P1 : f ∈ PeirceSpace e 1) : f = 0 ∨ f = e := by
  -- f ∈ P₁(e) means jmul e f = f
  rw [mem_peirceSpace_iff, one_smul] at hf_in_P1
  -- By primitivity: f idempotent with jmul e f = f implies f = 0 or f = e
  exact he.sub_eq_zero f hf_idem hf_in_P1

/-- Key lemma: If x ∈ P₁(e) satisfies x² = c • e for some c ≤ 0, then x = 0.
This uses formal reality: c < 0 contradicts sum of squares = 0, and c = 0 gives x² = 0 → x = 0. -/
theorem peirce_one_sq_nonpos_imp_zero [FormallyRealJordan J]
    {e : J} (he : IsIdempotent e) (he_ne : e ≠ 0) {x : J} (_hx : x ∈ PeirceSpace e 1)
    {c : ℝ} (hc : c ≤ 0) (hsq : jsq x = c • e) : x = 0 := by
  rcases hc.lt_or_eq with hc_neg | hc_zero
  · -- Case c < 0: violates formal reality
    exfalso
    -- jsq x = c • e with c < 0 means jsq x is "negative"
    -- We have jsq (√(-c) • e) = (-c) • e (since e² = e by jsq_smul_idem)
    -- So jsq x + jsq (√(-c) • e) = c • e + (-c) • e = 0
    have habs : -c > 0 := neg_pos.mpr hc_neg
    have hsqrt_ne : Real.sqrt (-c) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr habs)
    have hsum : jsq x + jsq (Real.sqrt (-c) • e) = 0 := by
      rw [hsq, jsq_smul_idem he, Real.sq_sqrt (le_of_lt habs)]
      rw [← add_smul, add_neg_cancel, zero_smul]
    -- By formal reality, both x and √(-c) • e must be zero
    have h := FormallyRealJordan.sum_sq_eq_zero 2 ![x, Real.sqrt (-c) • e]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have hcontra := h hsum 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Fin.isValue] at hcontra
    -- hcontra : √(-c) • e = 0, but √(-c) ≠ 0 and e ≠ 0
    rw [smul_eq_zero] at hcontra
    rcases hcontra with hsqrt_zero | he_zero
    · exact hsqrt_ne hsqrt_zero
    · exact he_ne he_zero
  · -- Case c = 0: x² = 0 implies x = 0 by formal reality
    rw [hc_zero, zero_smul] at hsq
    exact FormallyRealJordan.sq_eq_zero_imp_zero hsq

/-! ### H-O 2.9.4(ii): Primitive Idempotent Peirce Space Structure

The key theorem is that for a primitive idempotent e, the Peirce 1-space P₁(e) = ℝ·e.

**H-O Proof Strategy (NOT discriminant analysis!):**

For any x ∈ P₁(e), consider ℝ[x] = subalgebra generated by {e, x, x², ...}:
1. ℝ[x] is commutative (Jordan algebras)
2. ℝ[x] is associative (jpow_assoc: power-associativity)
3. ℝ[x] is finite-dimensional (subspace of finite-dim J)
4. ℝ[x] has no nilpotents (no_nilpotent_of_formallyReal)
5. By Artinian reduced ring theorem: ℝ[x] ≅ F₁ ⊕ ... ⊕ Fₙ (product of fields)
6. Identity e = e₁ + ... + eₙ (sum of field identities)
7. Primitivity of e forces n = 1 (otherwise eᵢ would be non-trivial sub-idempotent)
8. So ℝ[x] is a single field F
9. F is formally real and finite-dim over ℝ, hence F = ℝ (formallyReal_field_is_real)
10. Therefore x ∈ ℝ·e
-/

/-! ### Bilinear Structure for Jordan Multiplication -/

/-- jmul as a bilinear map. This is used to prove closure properties of spans. -/
def jmulBilin : J →ₗ[ℝ] J →ₗ[ℝ] J where
  toFun a := L a
  map_add' a b := by ext c; simp only [L_apply, add_jmul, LinearMap.add_apply]
  map_smul' r a := by ext c; simp only [L_apply, jmul_smul, LinearMap.smul_apply, RingHom.id_apply]

@[simp] theorem jmulBilin_apply (a b : J) : jmulBilin a b = jmul a b := rfl

/-! ### PowerSubmodule: The subalgebra generated by a single element

For x ∈ P₁(e), the algebra ℝ[x] = span{x⁰, x¹, x², ...} is the key object in
the H-O 2.9.4(ii) proof. We define it as a Submodule. -/

/-- The power submodule generated by x: span{x⁰, x¹, x², ...}.
This is the underlying ℝ-module of the subalgebra generated by x. -/
def PowerSubmodule (x : J) : Submodule ℝ J :=
  Submodule.span ℝ (Set.range (jpow x))

theorem mem_powerSubmodule_iff {x y : J} :
    y ∈ PowerSubmodule x ↔ y ∈ Submodule.span ℝ (Set.range (jpow x)) := Iff.rfl

/-- x^n is in PowerSubmodule x for all n. -/
theorem jpow_mem_powerSubmodule (x : J) (n : ℕ) : jpow x n ∈ PowerSubmodule x :=
  Submodule.subset_span ⟨n, rfl⟩

/-- x is in its power submodule (x = x^1). -/
theorem self_mem_powerSubmodule (x : J) : x ∈ PowerSubmodule x := by
  convert jpow_mem_powerSubmodule x 1 using 1
  exact (jpow_one x).symm

/-- jone is in PowerSubmodule x (jone = x^0). -/
theorem jone_mem_powerSubmodule (x : J) : jone ∈ PowerSubmodule x := by
  convert jpow_mem_powerSubmodule x 0 using 1

/-- PowerSubmodule x is closed under Jordan multiplication.
This follows from jpow_add: x^m ∘ x^n = x^{m+n}. -/
theorem powerSubmodule_mul_closed (x : J) {a b : J}
    (ha : a ∈ PowerSubmodule x) (hb : b ∈ PowerSubmodule x) :
    jmul a b ∈ PowerSubmodule x := by
  rw [mem_powerSubmodule_iff] at ha hb ⊢
  -- Key: for basis elements, jmul (x^m) (x^n) = x^{m+n} ∈ span
  have hbasis : ∀ y ∈ Set.range (jpow x), ∀ z ∈ Set.range (jpow x),
      jmulBilin y z ∈ Submodule.span ℝ (Set.range (jpow x)) := by
    intro y hy z hz
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    simp only [← hm, ← hn, jmulBilin_apply, jpow_add]
    exact Submodule.subset_span ⟨m + n, rfl⟩
  -- Apply the bilinear induction lemma
  exact LinearMap.BilinMap.apply_apply_mem_of_mem_span
    (Submodule.span ℝ (Set.range (jpow x)))
    (Set.range (jpow x)) (Set.range (jpow x))
    jmulBilin hbasis a b ha hb

/-- Associativity for PowerSubmodule: (a ∘ b) ∘ c = a ∘ (b ∘ c).
This extends jpow_assoc from generators to the full span using trilinearity. -/
theorem powerSubmodule_assoc (x : J) {a b c : J}
    (ha : a ∈ PowerSubmodule x) (hb : b ∈ PowerSubmodule x) (hc : c ∈ PowerSubmodule x) :
    jmul (jmul a b) c = jmul a (jmul b c) := by
  rw [mem_powerSubmodule_iff] at ha hb hc
  -- Strategy: use LinearMap.eqOn_span' three times, once for each variable
  -- First extend over a (with b, c fixed as generators), then over b, then over c

  -- Step 1: For fixed generators b = x^n, c = x^p, the maps f(a) = (a ∘ b) ∘ c and
  -- g(a) = a ∘ (b ∘ c) are linear and agree on generators by jpow_assoc
  have step1 : ∀ n p, ∀ a ∈ Submodule.span ℝ (Set.range (jpow x)),
      jmul (jmul a (jpow x n)) (jpow x p) = jmul a (jmul (jpow x n) (jpow x p)) := by
    intro n p a ha'
    -- Define the two linear maps (note: L b a = b ∘ a, so we need to account for commutativity)
    -- We want f(a) = (a ∘ x^n) ∘ x^p and g(a) = a ∘ (x^n ∘ x^p)
    -- Using commutativity: (a ∘ x^n) ∘ x^p = x^p ∘ (a ∘ x^n) = x^p ∘ (x^n ∘ a)
    -- So f = (L x^p) ∘ (L x^n) gives f(a) = x^p ∘ (x^n ∘ a)
    -- And g = L (x^n ∘ x^p) gives g(a) = (x^n ∘ x^p) ∘ a
    let f : J →ₗ[ℝ] J := (L (jpow x p)).comp (L (jpow x n))
    let g : J →ₗ[ℝ] J := L (jmul (jpow x n) (jpow x p))
    -- They agree on generators: f(x^m) = x^p ∘ (x^n ∘ x^m), g(x^m) = (x^n ∘ x^p) ∘ x^m
    -- By commutativity and jpow_assoc: both equal x^{m+n+p}
    have heq : Set.EqOn f g (Set.range (jpow x)) := by
      intro y hy
      obtain ⟨m, hm⟩ := hy
      simp only [f, g, LinearMap.comp_apply, L_apply, ← hm]
      -- x^p ∘ (x^n ∘ x^m) = (x^n ∘ x^p) ∘ x^m
      rw [jpow_add, jpow_add, jpow_add, jpow_add]
      ring
    -- Use eqOn_span' to extend
    have h := LinearMap.eqOn_span' heq ha'
    simp only [f, g, LinearMap.comp_apply, L_apply] at h
    -- h says: x^p ∘ (x^n ∘ a) = (x^n ∘ x^p) ∘ a
    -- We need: (a ∘ x^n) ∘ x^p = a ∘ (x^n ∘ x^p)
    -- By commutativity, both sides are equal to what h provides
    calc jmul (jmul a (jpow x n)) (jpow x p)
        = jmul (jpow x p) (jmul a (jpow x n)) := jmul_comm _ _
      _ = jmul (jpow x p) (jmul (jpow x n) a) := by rw [jmul_comm a]
      _ = jmul (jmul (jpow x n) (jpow x p)) a := h
      _ = jmul a (jmul (jpow x n) (jpow x p)) := jmul_comm _ _
  -- Step 2: For fixed generator c = x^p, and any a, b in span,
  -- (a ∘ b) ∘ c = a ∘ (b ∘ c)
  have step2 : ∀ p, ∀ a ∈ Submodule.span ℝ (Set.range (jpow x)),
      ∀ b ∈ Submodule.span ℝ (Set.range (jpow x)),
      jmul (jmul a b) (jpow x p) = jmul a (jmul b (jpow x p)) := by
    intro p a ha' b hb'
    -- For fixed a and c = x^p, we vary b
    -- f(b) = (a ∘ b) ∘ x^p = x^p ∘ (a ∘ b) = x^p ∘ (b ∘ a) by comm
    -- g(b) = a ∘ (b ∘ x^p) = a ∘ (x^p ∘ b) by comm = (x^p ∘ b) ∘ a by comm
    -- These involve nested commutativity - use bilinear approach
    let f : J →ₗ[ℝ] J := (L (jpow x p)).comp (jmulBilin a)
    let g : J →ₗ[ℝ] J := (jmulBilin a).comp (L (jpow x p))
    -- f(b) = x^p ∘ (a ∘ b), g(b) = a ∘ (x^p ∘ b)
    -- On generator b = x^n: f(x^n) = x^p ∘ (a ∘ x^n), g(x^n) = a ∘ (x^p ∘ x^n)
    have heq : Set.EqOn f g (Set.range (jpow x)) := by
      intro y hy
      obtain ⟨n, hn⟩ := hy
      simp only [f, g, LinearMap.comp_apply, L_apply, jmulBilin_apply, ← hn]
      -- x^p ∘ (a ∘ x^n) = a ∘ (x^p ∘ x^n)
      -- By commutativity: x^p ∘ (a ∘ x^n) = (a ∘ x^n) ∘ x^p and x^p ∘ x^n = x^n ∘ x^p
      calc jmul (jpow x p) (jmul a (jpow x n))
          = jmul (jmul a (jpow x n)) (jpow x p) := jmul_comm _ _
        _ = jmul a (jmul (jpow x n) (jpow x p)) := step1 n p a ha'
        _ = jmul a (jmul (jpow x p) (jpow x n)) := by rw [jmul_comm (jpow x n)]
    have h := LinearMap.eqOn_span' heq hb'
    simp only [f, g, LinearMap.comp_apply, L_apply, jmulBilin_apply] at h
    -- h: x^p ∘ (a ∘ b) = a ∘ (x^p ∘ b)
    calc jmul (jmul a b) (jpow x p)
        = jmul (jpow x p) (jmul a b) := jmul_comm _ _
      _ = jmul a (jmul (jpow x p) b) := h
      _ = jmul a (jmul b (jpow x p)) := by rw [jmul_comm (jpow x p)]
  -- Step 3: For any a, b, c in span, (a ∘ b) ∘ c = a ∘ (b ∘ c)
  -- For fixed a, b, we vary c
  let f : J →ₗ[ℝ] J := L (jmul a b)
  let g : J →ₗ[ℝ] J := (jmulBilin a).comp (jmulBilin b)
  -- f(c) = (a ∘ b) ∘ c, g(c) = a ∘ (b ∘ c)
  have heq : Set.EqOn f g (Set.range (jpow x)) := by
    intro y hy
    obtain ⟨p, hp⟩ := hy
    simp only [f, g, LinearMap.comp_apply, jmulBilin_apply, L_apply, ← hp]
    -- step2 gives us exactly: (a ∘ b) ∘ x^p = a ∘ (b ∘ x^p)
    exact step2 p a ha b hb
  have h := LinearMap.eqOn_span' heq hc
  simp only [f, g, LinearMap.comp_apply, jmulBilin_apply, L_apply] at h
  exact h

/-- PowerSubmodule x forms a commutative ring under Jordan multiplication.
The key ingredients are:
- Associativity: `powerSubmodule_assoc`
- Commutativity: `jmul_comm`
- Identity: `jone ∈ PowerSubmodule x`
- Closure: `powerSubmodule_mul_closed` -/
noncomputable instance powerSubmodule_commRing (x : J) : CommRing ↥(PowerSubmodule x) where
  mul := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨jmul a b, powerSubmodule_mul_closed x ha hb⟩
  mul_assoc := fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ =>
    Subtype.ext (powerSubmodule_assoc x ha hb hc)
  mul_comm := fun ⟨a, ha⟩ ⟨b, hb⟩ =>
    Subtype.ext (jmul_comm a b)
  one := ⟨jone, jone_mem_powerSubmodule x⟩
  one_mul := fun ⟨a, ha⟩ =>
    Subtype.ext (jone_jmul a)
  mul_one := fun ⟨a, ha⟩ =>
    Subtype.ext (jmul_jone a)
  left_distrib := fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ =>
    Subtype.ext (jmul_add a b c)
  right_distrib := fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ =>
    Subtype.ext (add_jmul a b c)
  zero_mul := fun ⟨a, ha⟩ =>
    Subtype.ext (zero_jmul a)
  mul_zero := fun ⟨a, ha⟩ =>
    Subtype.ext (jmul_zero a)

/-- Ring power on PowerSubmodule equals Jordan power.
This connects the CommRing structure to Jordan algebra power associativity. -/
theorem powerSubmodule_npow_eq_jpow (x : J) (a : ↥(PowerSubmodule x)) (n : ℕ) :
    (a ^ n : ↥(PowerSubmodule x)).val = jpow a.val n := by
  induction n with
  | zero => simp only [pow_zero, jpow_zero]; rfl
  | succ n ih =>
    change (a ^ n * a).val = jpow a.val (n + 1)
    have hmul : (a ^ n * a).val = jmul (a ^ n).val a.val := rfl
    rw [hmul, ih, jpow_succ, jmul_comm]

/-- PowerSubmodule forms an ℝ-scalar tower with its ring multiplication.
This is needed for IsArtinianRing.of_finite. -/
instance powerSubmodule_isScalarTower (x : J) :
    IsScalarTower ℝ ↥(PowerSubmodule x) ↥(PowerSubmodule x) where
  smul_assoc r a b := by
    have h1 : (a : ↥(PowerSubmodule x)) • b = a * b := rfl
    have h2 : (r • a) • b = (r • a) * b := rfl
    rw [h1, h2]
    ext
    -- Goal: ((r • a) * b).val = (r • (a * b)).val
    -- i.e., jmul (r • a.val) b.val = r • jmul a.val b.val
    simp only [Submodule.coe_smul]
    exact jmul_smul r a.val b.val

/-- PowerSubmodule is Artinian as a ring.
Follows from: ℝ is Artinian (field) and PowerSubmodule is finite-dimensional over ℝ. -/
instance powerSubmodule_isArtinianRing [FinDimJordanAlgebra J] (x : J) :
    IsArtinianRing ↥(PowerSubmodule x) :=
  IsArtinianRing.of_finite ℝ ↥(PowerSubmodule x)

/-- PowerSubmodule is reduced (no nilpotent elements).
This follows from formal reality: if a^n = 0 then a = 0. -/
instance powerSubmodule_isReduced [FormallyRealJordan J] (x : J) :
    IsReduced ↥(PowerSubmodule x) := by
  apply IsReduced.mk
  intro a hnil
  obtain ⟨n, hn⟩ := hnil
  cases n with
  | zero =>
    -- a^0 = 1 = 0 means the ring is trivial
    have h1eq0 : (1 : ↥(PowerSubmodule x)) = 0 := hn
    calc a = a * 1 := (mul_one a).symm
      _ = a * 0 := by rw [h1eq0]
      _ = 0 := mul_zero a
  | succ m =>
    have hpow : jpow a.val (m + 1) = 0 := by
      have := powerSubmodule_npow_eq_jpow x a (m + 1)
      rw [hn] at this; simp at this; exact this.symm
    have ha_zero : a.val = 0 :=
      no_nilpotent_of_formallyReal (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero m)) hpow
    ext; exact ha_zero

/-! ### P₁-Restricted Power Submodule

For x ∈ P₁(e), we need a subalgebra with identity e (not jone).
This is span{e, x, x², ...} where the powers are jpow x (n+1). -/

/-- The P₁-restricted power submodule: span{e, x, x², ...}.
For x ∈ P₁(e), this forms a commutative ring with identity e. -/
def P1PowerSubmodule (e x : J) : Submodule ℝ J :=
  Submodule.span ℝ (Set.insert e (Set.range fun n : ℕ => jpow x (n + 1)))

theorem e_mem_P1PowerSubmodule (e x : J) : e ∈ P1PowerSubmodule e x :=
  Submodule.subset_span (Set.mem_insert e _)

theorem jpow_succ_mem_P1PowerSubmodule (e x : J) (n : ℕ) :
    jpow x (n + 1) ∈ P1PowerSubmodule e x :=
  Submodule.subset_span (Set.mem_insert_of_mem e ⟨n, rfl⟩)

theorem self_mem_P1PowerSubmodule (e x : J) : x ∈ P1PowerSubmodule e x := by
  convert jpow_succ_mem_P1PowerSubmodule e x 0 using 1
  exact (jpow_one x).symm

/-- P1PowerSubmodule is contained in P₁(e) when x ∈ P₁(e). -/
theorem P1PowerSubmodule_le_peirceSpace (e x : J) (he : IsIdempotent e)
    (hx : x ∈ PeirceSpace e 1) : P1PowerSubmodule e x ≤ PeirceSpace e 1 := by
  apply Submodule.span_le.mpr
  intro y hy
  cases hy with
  | inl hy_eq_e => rw [hy_eq_e]; exact idempotent_in_peirce_one he
  | inr hy_pow =>
    obtain ⟨n, rfl⟩ := hy_pow
    exact jpow_succ_mem_peirce_one he hx n

/-- P1PowerSubmodule is closed under Jordan multiplication when x ∈ P₁(e).
Key facts: e ∘ e = e, e ∘ y = y for y ∈ P₁(e), x^m ∘ x^n = x^{m+n}. -/
theorem P1PowerSubmodule_mul_closed (e x : J) (he : IsIdempotent e)
    (hx : x ∈ PeirceSpace e 1) {a b : J}
    (ha : a ∈ P1PowerSubmodule e x) (hb : b ∈ P1PowerSubmodule e x) :
    jmul a b ∈ P1PowerSubmodule e x := by
  -- The generator set S = {e} ∪ {x^{n+1} | n ∈ ℕ}
  let S := Set.insert e (Set.range fun n : ℕ => jpow x (n + 1))
  -- Key: for basis elements, their products are in the span
  have hbasis : ∀ y ∈ S, ∀ z ∈ S, jmulBilin y z ∈ Submodule.span ℝ S := by
    intro y hy z hz
    simp only [jmulBilin_apply]
    cases hy with
    | inl hy_e =>
      -- y = e
      rw [hy_e]
      cases hz with
      | inl hz_e =>
        -- z = e: e ∘ e = e
        rw [hz_e, ← jsq_def, he]  -- he : jsq e = e
        exact Submodule.subset_span (Set.mem_insert e _)
      | inr hz_pow =>
        -- z = x^{n+1}: e ∘ x^{n+1} = x^{n+1} (by peirce_one_left_id)
        obtain ⟨n, hn⟩ := hz_pow
        rw [← hn, peirce_one_left_id (jpow_succ_mem_peirce_one he hx n)]
        exact Submodule.subset_span (Set.mem_insert_of_mem e ⟨n, rfl⟩)
    | inr hy_pow =>
      -- y = x^{m+1}
      obtain ⟨m, hm⟩ := hy_pow
      cases hz with
      | inl hz_e =>
        -- z = e: x^{m+1} ∘ e = e ∘ x^{m+1} = x^{m+1}
        rw [hz_e, jmul_comm, ← hm, peirce_one_left_id (jpow_succ_mem_peirce_one he hx m)]
        exact Submodule.subset_span (Set.mem_insert_of_mem e ⟨m, rfl⟩)
      | inr hz_pow =>
        -- z = x^{n+1}: x^{m+1} ∘ x^{n+1} = x^{m+n+2}
        obtain ⟨n, hn⟩ := hz_pow
        rw [← hm, ← hn, jpow_add]
        -- m+1 + n+1 = (m+n+1) + 1
        have heq : m + 1 + (n + 1) = (m + n + 1) + 1 := by omega
        rw [heq]
        exact Submodule.subset_span (Set.mem_insert_of_mem e ⟨m + n + 1, rfl⟩)
  -- Apply the bilinear induction lemma
  exact LinearMap.BilinMap.apply_apply_mem_of_mem_span
    (Submodule.span ℝ S) S S jmulBilin hbasis a b ha hb

/-- For a primitive idempotent e, the Peirce 1-space is one-dimensional.
This is the key step for H-O 2.9.4(ii).

**Proof (H-O ring-theoretic approach):**
For any x ∈ P₁(e), the subalgebra ℝ[x] generated by x (with identity e) is:
- Commutative and associative (by jpow_assoc)
- Finite-dimensional (subspace of P₁(e))
- Has no nilpotents (by no_nilpotent_of_formallyReal)

By the Artinian reduced ring structure theorem, ℝ[x] ≅ ∏ Fᵢ (product of fields).
The identity e = Σ eᵢ decomposes as a sum of field identities.
By primitivity of e, there can only be one field factor (n = 1).
This field is formally real (no i² = -1) and finite-dimensional over ℝ, hence = ℝ.
Therefore x ∈ ℝ·e, proving P₁(e) = ℝ·e and dim = 1. -/
theorem primitive_peirce_one_dim_one [FinDimJordanAlgebra J] [FormallyRealJordan J]
    {e : J} (he : IsPrimitive e) :
    Module.finrank ℝ (PeirceSpace e 1) = 1 := by
  -- Step 1: Show P₁(e) = span{e} by showing every x ∈ P₁(e) is a scalar multiple of e
  have he_in : e ∈ PeirceSpace e 1 := idempotent_in_peirce_one he.isIdempotent
  have he_ne : e ≠ 0 := he.ne_zero
  -- The span{e} is contained in P₁(e)
  have hspan_le : Submodule.span ℝ {e} ≤ PeirceSpace e 1 := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact he_in
  -- For equality, we show P₁(e) ≤ span{e} using H-O 2.9.4(ii) argument
  have hle_span : (PeirceSpace e 1 : Submodule ℝ J) ≤ Submodule.span ℝ {e} := by
    intro x hx
    rw [Submodule.mem_span_singleton]
    -- For any x ∈ P₁(e), we show ∃ r, x = r • e using the H-O ring-theoretic argument
    --
    -- The key insight (H-O 2.9.4(ii)):
    -- 1. ℝ[x] = span{e, x, x², ...} is a commutative associative subalgebra of P₁(e)
    --    (associativity from jpow_assoc, commutativity from Jordan)
    -- 2. ℝ[x] is finite-dimensional (subspace of finite-dim J)
    -- 3. ℝ[x] has no nilpotents (by no_nilpotent_of_formallyReal)
    -- 4. By artinian_reduced_is_product_of_fields: ℝ[x] ≅ F₁ ⊕ ... ⊕ Fₙ
    -- 5. Identity e = e₁ + ... + eₙ where eᵢ are field identities
    -- 6. Each eᵢ is an idempotent with e ∘ eᵢ = eᵢ (since eᵢ ∈ ℝ[x] ⊆ P₁(e))
    -- 7. By primitivity: each eᵢ = 0 or eᵢ = e
    -- 8. Since e = Σ eᵢ ≠ 0, exactly one eᵢ = e and others are 0
    -- 9. So n = 1, ℝ[x] is a single field F
    -- 10. F is formally real (inherited from J) and finite-dim over ℝ
    -- 11. By formallyReal_field_is_real: F = ℝ
    -- 12. Hence ℝ[x] = ℝ·e, so x ∈ ℝ·e
    --
    -- The construction of ℝ[x] as a CommRing requires packaging jpow_assoc
    -- into a ring structure. This is the main technical work.
    sorry
  -- Now use finrank monotonicity
  apply Nat.le_antisymm
  · -- finrank P₁(e) ≤ 1
    calc Module.finrank ℝ (PeirceSpace e 1)
        ≤ Module.finrank ℝ (Submodule.span ℝ ({e} : Set J)) := by
          apply Submodule.finrank_mono hle_span
      _ = 1 := finrank_span_singleton he_ne
  · -- finrank P₁(e) ≥ 1
    calc 1 = Module.finrank ℝ (Submodule.span ℝ ({e} : Set J)) :=
          (finrank_span_singleton he_ne).symm
      _ ≤ Module.finrank ℝ (PeirceSpace e 1) := by
          apply Submodule.finrank_mono hspan_le

/-- For a primitive idempotent e, every element x in PeirceSpace e 1 satisfies x = r • e.
This is H-O 2.9.4(ii): primitivity is equivalent to {eAe} = ℝe.

The proof: P₁(e) is 1-dimensional by `primitive_peirce_one_dim_one`, and
e ∈ P₁(e) with e ≠ 0, so P₁(e) = ℝ·e. -/
theorem primitive_peirce_one_scalar [FinDimJordanAlgebra J] [FormallyRealJordan J]
    {e : J} (he : IsPrimitive e) {x : J} (hx : x ∈ PeirceSpace e 1) :
    ∃ r : ℝ, x = r • e := by
  -- P₁(e) has dimension 1
  have hdim := primitive_peirce_one_dim_one he
  -- e ∈ P₁(e) and e ≠ 0
  have he_in : e ∈ PeirceSpace e 1 := idempotent_in_peirce_one he.isIdempotent
  have he_ne : e ≠ 0 := he.ne_zero
  -- Since dim P₁(e) = 1 and e ≠ 0 is in P₁(e), we have P₁(e) = span{e}
  -- Use the fact that x ∈ P₁(e) and dim = 1 implies x ∈ span{e}
  have hspan_eq : (PeirceSpace e 1 : Submodule ℝ J) = Submodule.span ℝ {e} := by
    -- span{e} ≤ P₁(e) (since e ∈ P₁(e))
    have hle : Submodule.span ℝ {e} ≤ PeirceSpace e 1 := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact he_in
    -- For equality, use that both have finrank 1
    apply (Submodule.eq_of_le_of_finrank_eq hle _).symm
    rw [hdim]
    exact finrank_span_singleton he_ne
  -- Now x ∈ P₁(e) = span{e}
  rw [hspan_eq, Submodule.mem_span_singleton] at hx
  obtain ⟨r, hr⟩ := hx
  exact ⟨r, hr.symm⟩

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
