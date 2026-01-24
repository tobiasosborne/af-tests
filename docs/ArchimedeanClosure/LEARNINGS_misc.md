# Miscellaneous Learnings

## QuadraticModule Definition Strategy

### Challenge
Defining M requires nonnegative ℝ-scaling, but `FreeAlgebra ℝ (Fin n)` has native ℝ-module.

### Solution
Defined `QuadraticModuleSet` as an `inductive` set with three constructors:
1. `generator_mem` - base generators (squares + generator-weighted squares)
2. `add_mem` - closure under addition
3. `smul_mem` - closure under `c • _` for `0 ≤ c : ℝ`

### Why Not ConvexCone?
Could use `ConvexCone.hull ℝ (generators)` but requires:
- More complex imports
- Instance resolution complexity
- Less direct membership proofs

The inductive definition is simpler.

---

## Section Organization for Variable Scope

### Challenge
When some definitions need `[IsArchimedean n]` and others don't, the auto variable
inclusion triggers linter warnings.

### Solution
Use `section ... end` blocks:

```lean
variable {n : ℕ}

section Embedding
-- No IsArchimedean needed here
def toProductFun (φ : MPositiveState n) : FreeStarAlgebra n → ℝ := fun a => φ a
end Embedding

section Bounded
variable [IsArchimedean n]
-- IsArchimedean needed here
theorem apply_mem_closedBall (φ : MPositiveState n) (a : FreeStarAlgebra n) : ... := ...
end Bounded
```

The `variable` inside `section Bounded` only applies within that section.

---

## FunLike Extensionality

### Challenge
When defining a structure with `FunLike` instance (like `MPositiveState`), `ext`
may not work due to no `@[ext]` attribute.

### Solution 1: Use DFunLike directly
```lean
theorem toProductFun_injective : Function.Injective (toProductFun (n := n)) := by
  intro φ ψ h
  apply DFunLike.coe_injective'
  exact h
```

### Solution 2: Register ext lemma
```lean
@[ext]
theorem ext {φ ψ : MPositiveState n} (h : ∀ a, φ a = ψ a) : φ = ψ :=
  DFunLike.coe_injective' (funext h)
```

---

## Import Notes

### For Star Algebra
```lean
import Mathlib.Algebra.Star.Free          -- FreeAlgebra star instance
import Mathlib.Algebra.Star.SelfAdjoint   -- IsSelfAdjoint
```

### For Bounds
```lean
import Mathlib.Analysis.SpecialFunctions.Pow.Real  -- Real.sqrt, sq_sqrt
```

### For Compactness
```lean
import Mathlib.Topology.Compactness.Compact       -- isCompact_univ_pi
import Mathlib.Topology.MetricSpace.ProperSpace   -- ProperSpace
```

### For Commute Lemmas
```lean
import Mathlib.Algebra.Ring.Commute  -- Commute.mul_self_sub_mul_self_eq
```

(May be transitively imported via other Algebra imports)

---

## MPositiveStateProps: What We Kept

After moving `map_star` to axiom, remaining useful lemmas:
- `apply_self_adjoint_add`: `φ(a + star a) = 2 * φ(a)`
- `apply_self_adjoint_sub`: `φ(a - star a) = 0`
- `apply_isSelfAdjoint`: `φ(star a) = φ(a)` when a is self-adjoint
- `apply_decomposition`: `φ(a) = (1/2) * φ(a + star a)`

These are trivial consequences of `map_star` but convenient to have named.

---

## StarAlgHom: map_star' vs map_star

### Observation
`StarAlgHom` uses `map_star'` (with prime), not `map_star`, to access the star-preserving property.

```lean
-- WRONG: π.toStarAlgHom.map_star a
-- RIGHT: π.toStarAlgHom.map_star' a
```

This is because `map_star` would conflict with the `StarHomClass` instance method.
The prime convention avoids namespace collision.

### Import
```lean
import Mathlib.Algebra.Star.StarAlgHom
```

---

## RCLike.re vs Complex.re

### Challenge
When working with inner products over ℂ, `inner_self_nonneg` gives:
```lean
inner_self_nonneg : 0 ≤ RCLike.re ⟪x, x⟫_ℂ
```
But goals often have `.re` (Complex field accessor):
```lean
⊢ 0 ≤ (⟪v, v⟫_ℂ).re
```
These are definitionally equal, but Lean's pattern matching doesn't unify them.

### Solution
Use `RCLike.re_eq_complex_re` to convert:
```lean
have h : 0 ≤ RCLike.re ⟪v, v⟫_ℂ := inner_self_nonneg
simp only [RCLike.re_eq_complex_re] at h
exact h
```

### Import
```lean
import Mathlib.Analysis.Complex.Basic  -- RCLike.re_eq_complex_re
```

---

## inner_smul_real_right Type Annotation

### Challenge
`inner_smul_real_right` fails to pattern match without explicit types:
```lean
-- Fails: inner_smul_real_right ξ (π.toStarAlgHom a ξ) c
```

### Solution
Provide explicit type annotation on the inner product:
```lean
have h : (⟪ξ, (c : ℂ) • (π.toStarAlgHom a ξ)⟫_ℂ : ℂ) = c • ⟪ξ, (π.toStarAlgHom a ξ)⟫_ℂ :=
  inner_smul_real_right ξ _ c
```

The `(_ : ℂ)` annotation helps Lean resolve the coercion.
