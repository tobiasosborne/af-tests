/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.FiniteDimensional
import AfTests.Jordan.Trace

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

/-! ### Strongly Connected Idempotents -/

/-- Two orthogonal idempotents are strongly connected if there exists v in the Peirce ½
space between them such that v² = e + f. This is the key structure in Jordan algebras
that enables the coordinatization theorem. (H-O Definition 2.8.1) -/
def IsStronglyConnected (e f : J) : Prop :=
  AreOrthogonal e f ∧ ∃ v : J,
    jmul e v = (1 / 2 : ℝ) • v ∧ jmul f v = (1 / 2 : ℝ) • v ∧ jsq v = e + f

/-! ### Structure of Orthogonal Primitives (H-O 2.9.4(iv)) -/

/-- In a formally real Jordan algebra, for orthogonal minimal idempotents p, q,
the element a² (where a ∈ {pAq}) satisfies a² = λ(p+q) for some λ ≥ 0.
This is H-O Lemma 2.9.4(iv). -/
theorem orthogonal_primitive_peirce_sq [FormallyRealJordan J] {e f : J}
    (he : IsPrimitive e) (hf : IsPrimitive f) (horth : AreOrthogonal e f)
    {a : J} (ha_peirce : jmul e a = (1 / 2 : ℝ) • a ∧ jmul f a = (1 / 2 : ℝ) • a) :
    ∃ μ : ℝ, 0 ≤ μ ∧ jsq a = μ • (e + f) := by
  -- By Peirce multiplication rules, a² ∈ {eAe} + {fAf} = ℝe + ℝf (primitivity)
  -- So a² = λ₁e + λ₂f. Operator commutation with e+f shows λ₁ = λ₂.
  -- Formal reality shows λ ≥ 0.
  sorry

/-- For orthogonal primitive idempotents in a formally real Jordan algebra,
either their Peirce ½ space is trivial or they are strongly connected.
This is the key dichotomy from H-O 2.9.4(iv). -/
theorem orthogonal_primitive_structure [FormallyRealJordan J] {e f : J}
    (he : IsPrimitive e) (hf : IsPrimitive f) (horth : AreOrthogonal e f) :
    (∀ a : J, jmul e a = (1 / 2 : ℝ) • a → jmul f a = (1 / 2 : ℝ) • a → a = 0) ∨
    IsStronglyConnected e f := by
  -- If there exists nonzero a in the Peirce ½ space, then by orthogonal_primitive_peirce_sq,
  -- a² = λ(e+f) with λ > 0 (λ = 0 would mean a² = 0, hence a = 0 by formal reality).
  -- Then (λ^{-1/2} a)² = e + f, so e and f are strongly connected.
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
