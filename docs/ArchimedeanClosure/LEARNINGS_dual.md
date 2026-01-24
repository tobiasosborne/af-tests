# Dual Characterization Learnings

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

---

## LinearPMap.mkSpanSingleton Pattern (AC-P6.3)

### Challenge
Need to define a linear map on `Submodule.span ℝ {A}` for some nonzero A.

### Solution
Use `LinearPMap.mkSpanSingleton`:
```lean
import Mathlib.LinearAlgebra.LinearPMap

noncomputable def myMap (hA : A ≠ 0) : Submodule.span ℝ {A} →ₗ[ℝ] ℝ :=
  (LinearPMap.mkSpanSingleton (K := ℝ) A targetValue hA).toFun
```

### Key Lemmas
- `LinearPMap.mkSpanSingleton_apply`: `f ⟨A, _⟩ = targetValue`
- `Submodule.mem_span_singleton`: `x ∈ span{A} ↔ ∃ c, c • A = x`

### Working with Submodule Subtypes
Elements `⟨c • A, _⟩ : Submodule.span ℝ {A}` equal `c • ⟨A, _⟩`:
```lean
have h : (⟨c • A, Submodule.mem_span_singleton.mpr ⟨c, rfl⟩⟩ : Submodule.span ℝ {A}) =
         c • ⟨A, Submodule.mem_span_singleton_self A⟩ := rfl
rw [h, LinearMap.map_smul]
-- Now: myMap (c • ⟨A, _⟩) = c • myMap ⟨A, _⟩ = c * targetValue
```

### Import
```lean
import Mathlib.LinearAlgebra.LinearPMap
```

---

## Riesz Extension Generating Condition Challenge (AC-P6.4)

### Mathlib's `riesz_extension` Theorem

```lean
riesz_extension :
  (s : ConvexCone ℝ E) (f : E →ₗ.[ℝ] ℝ) →
  (∀ (x : ↥f.domain), ↑x ∈ s → 0 ≤ ↑f x) →       -- f ≥ 0 on s ∩ domain
  (∀ (y : E), ∃ x ∈ f.domain, ↑x + y ∈ s) →      -- generating condition
  ∃ g, (∀ (x : ↥f.domain), g ↑x = ↑f x) ∧ ∀ x ∈ s, 0 ≤ g x
```

### The Challenge

For extending from `span{A}` (1-dimensional) with cone `M = QuadraticModule`:
- Condition 1 ✓: `separatingOnSpan_nonneg_on_M_cap_span` gives f ≥ 0 on M ∩ span{A}
- Condition 2 ✗: `∀ y, ∃ c, cA + y ∈ M` is **NOT** generally true

The generating condition requires every y can be "shifted" by some domain element into the cone.
For a 1-dimensional domain, this essentially asks whether M + span{A} = E, which is false.

### What We Have vs What We Need

**We proved** (`quadraticModule_selfAdjoint_generating`):
- M ∩ (A₀)_sa generates (A₀)_sa as differences: ∀ x, x = (1/4)m₁ - (1/4)m₂

**Mathlib needs**:
- `∀ y, ∃ x ∈ domain, x + y ∈ M`

These are related (both about "generating") but not identical.

### Alternative Approaches

1. **Hahn-Banach Separation** (RECOMMENDED):
   Use `RCLike.geometric_hahn_banach_closed_point` from `Mathlib.Analysis.NormedSpace.HahnBanach.Separation`:
   ```lean
   -- If s is convex and closed, x ∉ s, then ∃ f, u such that:
   -- ∀ a ∈ s, re(f(a)) < u and u < re(f(x))
   ```
   Requires: `TopologicalSpace E`, `LocallyConvexSpace ℝ E`, `IsClosed s`, `IsTopologicalAddGroup E`, `ContinuousSMul ℝ E`

2. **Custom Zorn's lemma proof**: Build extension step-by-step using generating property

3. **Inner product separation**: `ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem`
   requires `InnerProductSpace ℝ E` (not natural for FreeStarAlgebra)

### Status

File `Dual/RieszApplication.lean` created with:
- Structure and theorem statements
- `riesz_extension_exists`: main result (sorry)
- Clear documentation of the mathematical challenge

To complete: Either set up TopologicalSpace infrastructure for Hahn-Banach, or use custom Zorn argument.

### Import
```lean
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation  -- for geometric_hahn_banach
```

---

## Deep Dive: Why Standard Extension Theorems Don't Directly Apply (AC-P6.4)

### The Sublinear Extension Theorem

```lean
-- exists_extension_of_le_sublinear from Mathlib.Analysis.Convex.Cone.Extension
theorem exists_extension_of_le_sublinear (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)  -- positive homogeneous
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)                -- subadditive
    (hf : ∀ x : f.domain, f x ≤ N x) :                    -- f ≤ N on domain
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x  -- extension g ≤ N
```

### Why It Doesn't Work for Cone Nonnegativity

**What we need**: g ≥ 0 on M (cone)
**What this gives**: g ≤ N everywhere (upper bound)

These are **different constraints**:
- `g ≤ N` is an upper bound
- `g ≥ 0 on M` is a lower bound on a specific set

Even if N(m) ≥ 0 for m ∈ M (which holds for stateSeminorm), we only get:
- 0 ≤ N(m) and g(m) ≤ N(m)
- This does NOT imply g(m) ≥ 0

### How `exists_extension_of_le_sublinear` Uses `riesz_extension`

The proof cleverly lifts to E × ℝ with cone s = {(x, y) : N(x) ≤ y} (epigraph of N):

```lean
let s : ConvexCone ℝ (E × ℝ) :=
  { carrier := { p : E × ℝ | N p.1 ≤ p.2 }, ... }
```

The generating condition becomes trivial in this lifted space:
```lean
have hf'_dense : ∀ y : E × ℝ, ∃ x : f'.domain, ↑x + y ∈ s := by
  rintro ⟨x, y⟩
  refine ⟨⟨(0, N x - y), ...⟩, ?_⟩
  -- (0, N x - y) + (x, y) = (x, N x) ∈ s since N(x) ≤ N(x) ✓
```

**Key insight**: The domain must contain (0, r) for all r ∈ ℝ, which the coprod construction provides.

### ProperCone.hyperplane_separation_point (Best Path Forward)

```lean
-- From Mathlib.Analysis.Convex.Cone.Dual
theorem ProperCone.hyperplane_separation_point
  [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  [Module Real E] [ContinuousSMul Real E] [LocallyConvexSpace Real E]
  {x₀ : E} (C : ProperCone Real E) (hx₀ : x₀ ∉ C) :
    ∃ f : E →L[ℝ] ℝ, (∀ x ∈ C, 0 ≤ f x) ∧ f x₀ < 0
```

**This is exactly what we need!** Requirements:
1. TopologicalSpace on FreeStarAlgebra (from stateSeminorm)
2. LocallyConvexSpace (seminorm topologies are locally convex)
3. M is a ProperCone (nonempty + closed in seminorm topology)

### Infrastructure Needed for Topology Approach

```lean
-- Step 1: Define topology from seminorm
instance : TopologicalSpace (FreeStarAlgebra n) :=
  seminormTopology (stateSeminorm n)

-- Step 2: Show it's locally convex
instance : LocallyConvexSpace ℝ (FreeStarAlgebra n) := by
  -- Seminorm topologies are always locally convex
  sorry

-- Step 3: Show M is closed (we have this via quadraticModuleClosure definition)
theorem M_isClosed : IsClosed (QuadraticModule n : Set (FreeStarAlgebra n)) := by
  -- Closedness in seminorm topology
  sorry

-- Step 4: Construct ProperCone from M
def M_properCone : ProperCone ℝ (FreeStarAlgebra n) := ⟨QuadraticModule n, M_isClosed, ...⟩
```

### Alternative: Custom Zorn Argument

If topology setup is too heavy, use a direct Zorn argument:

1. Consider all partial extensions ψ of ψ₀ that are ≥ 0 on M ∩ domain
2. Chains have upper bounds (union of domains, consistent values)
3. Maximal element must be total by generating property:
   - If domain D ⊊ E and y ∉ D, pick valid value for ψ(y)
   - Constraint: ψ(d) + c·ψ(y) ≥ 0 for all d + c·y ∈ M
   - This defines an interval for ψ(y); generating property shows it's nonempty

**The generating property** `quadraticModule_selfAdjoint_generating` ensures the constraint interval is nonempty:
- For any y, write y = (1/4)m₁ - (1/4)m₂ where m₁, m₂ ∈ M
- Then (1/4)m₂ + y = (1/4)m₁ ∈ M
- This gives one constraint on ψ(y)

### Current Status and Next Steps

**Current**: RieszApplication.lean has structure but core theorem is sorry'd.

**Recommended path**:
1. Create `Topology/SeminormTopology.lean` (~50 LOC) to set up:
   - TopologicalSpace from stateSeminorm
   - LocallyConvexSpace instance
   - Show M is closed (use existing quadraticModuleClosure work)

2. Use `ProperCone.hyperplane_separation_point` directly

**Alternative**: Custom Zorn proof in `Dual/ZornExtension.lean` (~80 LOC)
