# Extension Theorem Analysis

Deep analysis of why standard Mathlib extension theorems don't directly apply
to the Riesz extension problem (AC-P6.4).

---

## The Sublinear Extension Theorem

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

---

## ProperCone.hyperplane_separation_point (Best Path Forward)

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

---

## Infrastructure Needed for Topology Approach

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

---

## Alternative: Custom Zorn Argument

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

---

## SeminormFamily Pattern for LocallyConvexSpace

To use `WithSeminorms.toLocallyConvexSpace` for a single seminorm:

```lean
import Mathlib.Analysis.LocallyConvex.WithSeminorms

-- 1. Create family indexed by Unit
noncomputable def stateSeminormFamily : SeminormFamily ℝ E Unit :=
  fun _ => mySeminorm

-- 2. Define topology from family
noncomputable def seminormTopology : TopologicalSpace E :=
  stateSeminormFamily.moduleFilterBasis.topology

-- 3. In a section with local instance:
attribute [local instance] seminormTopology

-- 4. Prove WithSeminorms (trivial by definition)
theorem withSeminorms_stateSeminormFamily : WithSeminorms stateSeminormFamily :=
  WithSeminorms.mk rfl

-- 5. Get LocallyConvexSpace
theorem locallyConvexSpace : LocallyConvexSpace ℝ E :=
  WithSeminorms.toLocallyConvexSpace withSeminorms_stateSeminormFamily
```

**Key insight**: The topology is *defined* as the seminorm family topology, so
`WithSeminorms.mk rfl` works directly.

---

## Status: COMPLETE ✓

**All topology and separation infrastructure is complete!**

### Completed Files

- `Topology/SeminormTopology.lean` (116 LOC):
  - `seminormTopology` - TopologicalSpace from stateSeminorm ✓
  - `locallyConvexSpace_seminormTopology` - LocallyConvexSpace instance ✓
  - `quadraticModuleClosure_eq_closure` - ε-δ = topological closure ✓
  - `isClosed_quadraticModuleClosure` - M̄ is closed ✓

- `Dual/RieszApplication.lean` (98 LOC):
  - `quadraticModuleClosureProperCone` - M̄ as ProperCone ✓
  - `riesz_extension_exists` - Main separation theorem ✓

### Key Result

```lean
theorem riesz_extension_exists {A : FreeStarAlgebra n}
    (_hA : IsSelfAdjoint A) (hA_not : A ∉ quadraticModuleClosure) :
    ∃ ψ : FreeStarAlgebra n →ₗ[ℝ] ℝ,
      (∀ m ∈ QuadraticModule n, 0 ≤ ψ m) ∧ ψ A < 0
```

### Proof Strategy

1. Construct `ProperCone ℝ (FreeStarAlgebra n)` from M̄
2. Apply `ProperCone.hyperplane_separation_point` to get continuous f with f ≥ 0 on M̄, f(A) < 0
3. Since M ⊆ M̄, we have f ≥ 0 on M

This elegantly bypasses the "generating condition" requirement of `riesz_extension`.
