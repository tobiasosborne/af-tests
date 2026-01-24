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

---

## Closedness in Product Topology (AC-P4.2)

### Key Insight
Conditions defining M-positive states are closed in the product topology because:
1. Each condition is a preimage of a closed set under a continuous map
2. Evaluation at a point is continuous: `continuous_apply a`
3. Arbitrary intersections of closed sets are closed: `isClosed_iInter`

### Pattern: Equality Conditions
For conditions like `f(a+b) = f(a) + f(b)`:
```lean
have h : {f | f (a+b) = f a + f b} = (fun f => f (a+b) - (f a + f b)) ⁻¹' {0} := by
  ext f; simp [Set.mem_preimage, sub_eq_zero]
rw [h]
apply IsClosed.preimage
· exact continuous_eval (a+b) |>.sub (continuous_eval a |>.add (continuous_eval b))
· exact isClosed_singleton
```

### Pattern: Inequality Conditions
For conditions like `f(m) ≥ 0`:
```lean
have h : {f | 0 ≤ f m} = (fun f => f m) ⁻¹' Set.Ici 0 := by
  ext f; simp [Set.mem_preimage, Set.mem_Ici]
rw [h]
apply IsClosed.preimage (continuous_eval m)
exact isClosed_Ici
```

### Required Imports
```lean
import Mathlib.Topology.Constructions      -- Pi topology, continuous_apply
import Mathlib.Topology.Order.Basic        -- isClosed_Ici
import Mathlib.Topology.Algebra.Ring.Real  -- ContinuousSub ℝ, ContinuousMul ℝ
```

### Constructing MPositiveState from Function (SOLVED)

To prove `Set.range toProductFun` is closed, we show range = stateConditions:
1. Range ⊆ stateConditions: ✅ `range_subset_stateConditions`
2. stateConditions ⊆ Range: ✅ `stateConditions_subset_range`

**Pattern: Build LinearMap from additivity + homogeneity**
```lean
def ofFunction (f : FreeStarAlgebra n → ℝ)
    (hf_add : ∀ a b, f (a + b) = f a + f b)
    (hf_smul : ∀ c a, f (c • a) = c * f a)
    (hf_star : ∀ a, f (star a) = f a)
    (hf_m_nonneg : ∀ m ∈ QuadraticModule n, 0 ≤ f m)
    (hf_one : f 1 = 1) : MPositiveState n where
  toFun := {
    toFun := f
    map_add' := hf_add
    map_smul' := by intro c a; simp only [RingHom.id_apply]; exact hf_smul c a
  }
  map_star := hf_star
  map_one := hf_one
  map_m_nonneg := hf_m_nonneg
```

**Key Mathlib Insight:** `LinearMap.mk` takes an `AddHom` (from additivity) plus smul proof.
The anonymous structure syntax `{ toFun := f, map_add' := hf_add, map_smul' := ... }` builds the LinearMap directly.
