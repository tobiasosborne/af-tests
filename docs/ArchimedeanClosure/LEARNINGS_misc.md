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

## Span Intersection for Riesz Extension (AC-P6.2)

### Key Insight: Only Positive Scalars Matter

For Riesz extension, we define a separating functional ψ₀(λA) = -λε on span{A}.
We need ψ₀ ≥ 0 on M ∩ span{A}. The key observation:

1. **λ > 0 case**: If λA ∈ M, then A = (1/λ)(λA) ∈ M by cone property → A ∈ M̄.
   Contradiction. So this case never occurs.
2. **λ ≤ 0 case**: ψ₀(λA) = -λε ≥ 0 automatically (since -λ ≥ 0 and ε > 0).

### We Don't Need Full M ∩ span{A} = {0}

The FILE_PLAN specified proving M ∩ span{A} = {0}, but this is **stronger than needed**.
The λ < 0 case (negative multiples of A in M) doesn't cause problems for the
separating functional—it's automatically nonneg.

### What We Actually Proved

```lean
-- If A ∉ M̄ and c > 0, then c • A ∉ M
theorem positive_smul_not_in_M {A} (hA_not : A ∉ quadraticModuleClosure)
    {c : ℝ} (hc : 0 < c) : c • A ∉ QuadraticModule n

-- The separating functional is nonneg on M ∩ span{A}
theorem separating_nonneg_on_span_cap_M {A} (hA_not : A ∉ quadraticModuleClosure)
    {ε : ℝ} (hε : 0 < ε) {x} (hx_in_M : x ∈ QuadraticModule n)
    {coeff : ℝ} (hx_eq : x = coeff • A) : 0 ≤ -coeff * ε

-- Coefficients of M ∩ span{A} elements are ≤ 0
theorem span_cap_M_nonpos_coeff {A} (hA_not : A ∉ quadraticModuleClosure)
    {coeff : ℝ} (hcoeff_smul_in_M : coeff • A ∈ QuadraticModule n) : coeff ≤ 0
```

### Proof Pattern

The core argument is beautifully simple:
```lean
theorem positive_smul_not_in_M ... := by
  intro h_cA_in_M
  have h_A_in_M : A ∈ QuadraticModule n := by
    have h_eq : A = c⁻¹ • (c • A) := by rw [smul_smul, inv_mul_cancel₀ _, one_smul]
    rw [h_eq]
    exact QuadraticModule.smul_mem (le_of_lt (inv_pos.mpr hc)) h_cA_in_M
  exact hA_not (quadraticModule_subset_closure h_A_in_M)
```
