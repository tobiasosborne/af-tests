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
* `exists_primitive_decomp` - Every nonzero idempotent decomposes into primitives

## Main results

* `isPrimitive_of_minimal` - Minimal idempotents are primitive
* `primitive_dichotomy` - Two primitives are either orthogonal or equal
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

/-! ### Dichotomy for Primitive Idempotents -/

/-- Two primitive idempotents are either orthogonal or equal (needs FormallyRealJordan). -/
theorem primitive_dichotomy [FormallyRealJordan J] {e f : J}
    (he : IsPrimitive e) (hf : IsPrimitive f) :
    AreOrthogonal e f ∨ e = f := by
  -- Key insight: Use the formally real property via (e - f)².
  -- If e ≠ f and jmul e f ≠ 0, we derive a contradiction from the structure of primitives.
  by_cases hef : jmul e f = 0
  · left; exact hef
  · right
    -- jmul e f ≠ 0. We show e = f by analyzing the order structure.
    -- For idempotents, e ≤ f (in the Jordan order) iff jmul e f = e.
    by_cases hef_e : jmul e f = e
    · -- jmul e f = e means jmul f e = e, so e ∈ P₁(f)
      -- By primitivity of f applied to idempotent e with jmul f e = e:
      -- e = 0 or e = f. Since e ≠ 0, e = f.
      have he_idem : IsIdempotent e := he.isIdempotent
      have hfe : jmul f e = e := by rw [jmul_comm]; exact hef_e
      rcases hf.sub_eq_zero e he_idem hfe with he0 | hef'
      · exfalso; exact he.ne_zero he0
      · exact hef'
    · -- jmul e f ≠ e. By symmetry, check if jmul e f = f.
      by_cases hef_f : jmul e f = f
      · -- jmul e f = f means f ∈ P₁(e)
        -- By primitivity of e applied to idempotent f with jmul e f = f:
        -- f = 0 or f = e. Since f ≠ 0, f = e.
        have hf_idem : IsIdempotent f := hf.isIdempotent
        rcases he.sub_eq_zero f hf_idem hef_f with hf0 | hfe
        · exfalso; exact hf.ne_zero hf0
        · exact hfe.symm
      · -- jmul e f ≠ 0, jmul e f ≠ e, jmul e f ≠ f
        -- This case requires showing that "incomparable" primitives cannot exist.
        --
        -- ⚠️ POTENTIAL ISSUE: The handoff strategy claims jmul e f ∈ P₁(e) ∩ P₁(f)
        -- when jmul e f ≠ 0, but this requires the P₁₂(e) component of f to be 0.
        -- For arbitrary primitive idempotents, this may not hold!
        --
        -- Example to investigate: In 2×2 symmetric matrices over ℝ,
        -- e = diag(1,0) and f = [[1/2,1/2],[1/2,1/2]] are both primitive
        -- (rank-1 projections), but jmul e f ≠ 0, jmul e f ≠ e, jmul e f ≠ f.
        --
        -- Possible resolutions:
        -- 1. The dichotomy needs additional hypotheses (e.g., same spectral family)
        -- 2. Primitivity in finite-dim formally real JA has stronger consequences
        -- 3. The proof requires JB-algebra completeness (not just formally real)
        --
        -- Standard JB-algebra result: primitives are orthogonal or *equivalent*
        -- (related by inner automorphism), not necessarily equal.
        exfalso
        sorry

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
