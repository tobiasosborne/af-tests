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

## Tychonoff Theorem Application

### Goal
Prove product of closed balls is compact.

### Key Mathlib Lemmas
- `isCompact_univ_pi`: `(∀ i, IsCompact (s i)) → IsCompact (Set.univ.pi s)`
- `ProperSpace.isCompact_closedBall`: Closed balls compact in proper spaces (ℝ is proper)

### The Trick
Rewrite setOf as `Set.univ.pi`:
```lean
have h_eq : { f | ∀ a, f a ∈ closedBall 0 (bound a) } =
    Set.univ.pi (fun a => closedBall 0 (bound a)) := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
rw [h_eq]
apply isCompact_univ_pi
intro a
exact ProperSpace.isCompact_closedBall 0 (bound a)
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
