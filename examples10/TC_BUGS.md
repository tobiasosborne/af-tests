# TensorCategories.jl Bugs — Debug Report

## Bug 1: Center crash (thread-safety race condition)

**Location**: `Center.jl:1472`, function `hom_by_adjunction`

**Root cause**: The `@threads for` loop writes to a shared `mors` vector:
```julia
mors = [mors; B3]  # RACE: multiple threads read/write mors
```

**Fix applied** (Center.jl): Pre-allocate per-thread result storage:
```julia
thread_results = Vector{Vector{CenterMorphism}}(undef, length(candidate_indices))
@threads for idx ∈ 1:length(candidate_indices)
    ...
    thread_results[idx] = B3
end
mors = vcat(thread_results...)
```

**Status**: Fix applied but center still crashes. The crash may be in a DIFFERENT
`@threads` loop called deeper in the stack (e.g., during `induction()` or
`simple_subobjects()` → `End()` → recursive `hom_by_adjunction` calls).
The single-threaded `hom_by_adjunction` test passed successfully.

## Bug 2: Pentagon axiom failure (summand ordering mismatch)

**Location**: `FusionCategory.jl:317-365`, `associator()` for non-simple SixJObjects

**Symptoms**: 156/4096 pentagon checks fail, all involving the swap element
`(𝟙⊠𝟙, (1,2))` of the G-crossed product `(Fib⊠Fib)⋊S₂`.

**Root cause analysis**:

The non-simple associator decomposes `(X⊗Y)⊗Z` into simple summands
`⊕(x_a⊗y_b)⊗z_c`, applies block-diagonal 6j symbols, then reassembles
into `X⊗(Y⊗Z)`. The summands are ordered by simple index (type 1,3,5,7),
but the tensor product's internal block structure orders by the TYPE of
the intermediate product `x_a⊗y_b`.

When the G-action permutes types (e.g., S₂⊗S₃ = S₆ instead of staying
near type 3), the tensor product's ordering (i=2,4,6,8) differs from
the summand ordering (types 1,3,5,7 → mapped to types 2,6,4,8 by S₂).

This creates a permutation matrix P_{23} in block 8 of the associator
`α(S₂, S₁⊕S₃⊕S₅⊕S₇, S₇)`. The domain and codomain use different
internal orderings, causing the pentagon to fail.

**Concrete evidence** (block 8 of pentagon(2,7,7,7)):
```
LHS[8] = [ϕ+1 ϕ+1 ϕ+1 ϕ+1; -ϕ -ϕ -ϕ-1 -ϕ-1; -ϕ -ϕ-1 -ϕ -ϕ-1; 1 ϕ ϕ ϕ+1]
RHS[8] = [ϕ+1 ϕ+1 ϕ+1 ϕ+1; -ϕ -ϕ-1 -ϕ -ϕ-1; -ϕ -ϕ -ϕ-1 -ϕ-1; 1 ϕ ϕ ϕ+1]
Diff   = [0 0 0 0; 0 1 -1 0; 0 -1 1 0; 0 0 0 0]  ← rows/cols 2,3 swapped
```

**Fixes attempted**:
1. `inv(inclusion-based distribution)` — same result (P_{23} = P_{23}⁻¹)
2. Step-by-step `distribute_left`/`distribute_right` — same result
3. Direct 6j matrix construction — incomplete (too complex)

**Correct fix direction**: The issue is fundamental to how `tensor_product(f,g)`
builds block-diagonal morphisms. The non-simple associator's block ordering
(determined by summand decomposition) doesn't match the tensor product's
block ordering (determined by the (i,j) iteration). A correct fix needs to
either:
- Build the associator matrix DIRECTLY in the tensor product's basis, or
- Track and apply the permutation between summand and tensor-product orderings

This is a non-trivial fix requiring changes to how `tensor_product(f,g)`
or the non-simple associator handles block ordering.

## F-symbols are correct

The stored F-symbols (6j symbols) in the G-crossed product ARE mathematically
correct — verified by independent derivation from the formula:
```
CxG.ass[(i,g),(j,h),(k,l),(m,ghl)] = base.ass[i, T_g(j), T_{gh}(k), m]
```
with 0 differences across all 4096 blocks. The bug is only in the non-simple
associator assembly code, not in the stored data.

## Files modified

- `TensorCategories.jl/src/TensorCategoryFramework/Center/Center.jl` — thread-safety fix
- `TensorCategories.jl/src/TensorCategoryFramework/SixJCategory/FusionCategory.jl` — various attempts

## Debug scripts

- `debug_center.jl` — reproduces center crash, identifies `hom_by_adjunction` @threads
- `debug_center2.jl` — shows crash is thread-related (single-threaded works)
- `debug_pentagon.jl` — identifies exact failing block and diff
- `debug_ordering.jl` — traces block ordering mismatch
- `test_fixes.jl` — quick test for both fixes
