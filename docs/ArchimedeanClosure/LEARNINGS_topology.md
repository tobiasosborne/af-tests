# Topology and Compactness Learnings

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

---

## ciSup Patterns for Seminorm Properties (AC-P5.2)

### Key Lemmas for Supremum Manipulation

```lean
import Mathlib.Data.Real.Pointwise

-- Pull scalar out of supremum (note: returns r * ⨆ i, f i = ⨆ i, r * f i)
#check @Real.mul_iSup_of_nonneg  -- ∀ {r : ℝ}, 0 ≤ r → ∀ f, r * ⨆ i, f i = ⨆ i, r * f i

-- Constant supremum
#check @ciSup_const  -- ⨆ _, c = c (requires Nonempty)
```

### Pattern: Proving ||c • a|| = |c| * ||a||

```lean
theorem stateSeminorm_smul (c : ℝ) (a : FreeStarAlgebra n) :
    stateSeminorm (c • a) = |c| * stateSeminorm a := by
  unfold stateSeminorm
  have h_eq : ∀ φ : MPositiveState n, |φ (c • a)| = |c| * |φ a| := fun φ => by
    change |φ.toFun (c • a)| = |c| * |φ.toFun a|
    simp [φ.toFun.map_smul, abs_mul]
  simp_rw [h_eq]
  -- Use .symm because lemma gives r * ⨆ f = ⨆ (r * f)
  exact (Real.mul_iSup_of_nonneg (abs_nonneg c) _).symm
```

### FunLike Coercion Trick

When `MPositiveState` has `FunLike` instance, `φ a` may not definitionally equal `φ.toFun a`.
Use `change` to expose the underlying structure:

```lean
-- This fails:
-- rw [φ.toFun.map_zero]  -- "Did not find φ.toFun 0 in |φ 0| = 0"

-- This works:
change |φ.toFun 0| = 0
simp [φ.toFun.map_zero]
```

### Import Requirement

```lean
import Mathlib.Data.Real.Pointwise  -- Real.mul_iSup_of_nonneg
```

---

## Seminorm Closure without Topology (AC-P5.3)

### Challenge
Defining closure of M in ||·||_M topology requires a `TopologicalSpace` instance on
`FreeStarAlgebra n`. Setting up topology from seminorm requires `WithSeminorms` machinery.

### Solution
Define closure directly via ε-δ definition:

```lean
def quadraticModuleClosure : Set (FreeStarAlgebra n) :=
  {a | ∀ ε > 0, ∃ m ∈ QuadraticModule n, stateSeminorm (a - m) < ε}
```

This is exactly the standard closure definition for a metric/seminorm topology,
without needing to instantiate `TopologicalSpace`.

### Proving Cone Properties

Use ε/2 trick for addition:
```lean
theorem closure_add_mem {a b} (ha : a ∈ closure) (hb : b ∈ closure) :
    a + b ∈ closure := by
  intro ε hε
  obtain ⟨ma, hma, ha'⟩ := ha (ε / 2) (by linarith)
  obtain ⟨mb, hmb, hb'⟩ := hb (ε / 2) (by linarith)
  refine ⟨ma + mb, QuadraticModule.add_mem hma hmb, ?_⟩
  calc stateSeminorm (a + b - (ma + mb))
      = stateSeminorm ((a - ma) + (b - mb)) := by congr 1; abel
    _ ≤ stateSeminorm (a - ma) + stateSeminorm (b - mb) := stateSeminorm_add _ _
    _ < ε / 2 + ε / 2 := add_lt_add ha' hb'
    _ = ε := by ring
```

For scaling by c > 0, use ε/c:
```lean
obtain ⟨m, hm, hma⟩ := ha (ε / c) (div_pos hε hcpos)
-- Then: c * (ε / c) = ε
```

### Linter: `omit [IsArchimedean n] in`
When a theorem only uses lemmas like `stateSeminorm_zero` that don't require
`IsArchimedean`, the linter complains. Use:
```lean
omit [IsArchimedean n] in
theorem quadraticModule_subset_closure : ... := ...
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
