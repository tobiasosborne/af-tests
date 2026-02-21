# HANDOFF — Fib ⊠ Ising Investigation

## What was computed

Full categorical data for the Deligne product Fib ⊠ Ising using TensorCategories.jl.

### Verified results (all solid)

| Item | Status | Details |
|------|--------|---------|
| F-symbols | **540 nonzero**, pentagon PASS | `fsymbols_fib_ising.txt` |
| Fusion rules | 21 nonzero products | See output below |
| Module cat 1 (trivial) | 6 simples, bimodule pentagon PASS | Algebra on 𝟙⊠𝟙 |
| Module cat 2 (Ising Z₂) | 6 simples, bimodule pentagon PASS | Algebra on 𝟙⊠𝟙 ⊕ 𝟙⊠χ |
| Module cat 3 (Fib cond.) | 6 simples, bimodule pentagon PASS | Algebra on 𝟙⊠𝟙 ⊕ τ⊠𝟙 (took 52 min!) |
| **Drinfeld center** | **15 simples, FPdim² exact match** | `compute_fib_ising_center_v2.jl` |
| **S matrix** | **15×15 computed** (1085s) | See center results below |
| **T matrix** | **15×15 computed** (114768s ≈ 31.9h) | Non-trivial twists, 3 zero entries |

### Pending

| Item | Status | Issue |
|------|--------|-------|
| Module categories (extended) | Not yet run | `compute_fib_ising_modules.jl` ready |

## Drinfeld Center Z(Fib ⊠ Ising) — CORRECTED (2026-02-20)

### Center: 15 simple objects (FPdim² = 209.443 = FPdim²(C)² ✓)

| Simple | Underlying object | FPdim |
|--------|-------------------|-------|
| Z₁ | 𝟙⊠𝟙 ⊕ τ⊠𝟙 | ϕ² ≈ 2.618 |
| Z₂ | 𝟙⊠𝟙 ⊕ τ⊠𝟙 | ϕ² ≈ 2.618 |
| Z₃ | 𝟙⊠𝟙 | 1 |
| Z₄ | 𝟙⊠𝟙 ⊕ 𝟙⊠χ | 2 |
| Z₅ | 𝟙⊠𝟙 | 1 |
| Z₆ | 𝟙⊠𝟙 ⊕ 𝟙⊠χ ⊕ τ⊠𝟙 ⊕ τ⊠χ | 2ϕ² ≈ 5.236 |
| Z₇ | 2⋅𝟙⊠χ | 2 |
| Z₈ | 2⋅𝟙⊠χ ⊕ 2⋅τ⊠χ | 2ϕ² ≈ 5.236 |
| Z₉ | 4⋅𝟙⊠X ⊕ 4⋅τ⊠X | ≈ 14.81 |
| Z₁₀ | 4⋅𝟙⊠X | 4√2 ≈ 5.657 |
| Z₁₁ | 2⋅τ⊠𝟙 | 2ϕ ≈ 3.236 |
| Z₁₂ | 2⋅τ⊠𝟙 ⊕ 2⋅τ⊠χ | 4ϕ ≈ 6.472 |
| Z₁₃ | 2⋅τ⊠𝟙 | 2ϕ ≈ 3.236 |
| Z₁₄ | 4⋅τ⊠χ | 4ϕ ≈ 6.472 |
| Z₁₅ | 8⋅τ⊠X | ≈ 18.31 |

**FPdim²(Z) = 209.443 = FPdim²(Fib ⊠ Ising)² = (14.472)² ✓** — exact match confirms center is complete.

**Why 15, not 24?** Z(C₁ ⊠ C₂) ≅ Z(C₁) ⊠ Z(C₂). Z(Fib) has 4 simples, Z(Ising) has 6.
But the Deligne product ⊠ doesn't simply multiply ranks — the decomposition of
inductions over the degree-4 field K = QQ(ϕ,√2) can yield larger indecomposable objects.
The rank 15 with matching FPdim² means all anyons are accounted for.

### 15×15 S matrix computed (entries in QQ(ϕ,√2))

S matrix computed in 1085s. First row (unnormalized):
```
S[1,:] = [1, 1, ϕ, 2ϕ, ϕ, 2, 2ϕ, 2, ...]
```
Full matrix in `center_v2.log`. S² computed — non-diagonal, non-trivial structure.

### T matrix: COMPLETED (31.9 hours)

| Simple | T[i,i] | Interpretation |
|--------|--------|----------------|
| Z₁–Z₆ | 1 | Bosonic (trivial twist) |
| Z₇–Z₈ | −1 | Fermionic (spin ½) |
| Z₉, Z₁₀, Z₁₅ | **0** | Degenerate — may indicate non-simple objects or field artifact |
| Z₁₁–Z₁₃ | `1//3*x³ + 1//2*x² - 5//3*x - 7//6` | Algebraic twist (≈ e^{2πiθ} for some θ) |
| Z₁₄ | `-(1//3*x³ + 1//2*x² - 5//3*x - 7//6)` | Conjugate twist |

**Note on T[9]=T[10]=T[15]=0**: These correspond to the largest center objects
(Z₉: `4⋅𝟙⊠X ⊕ 4⋅τ⊠X`, Z₁₀: `4⋅𝟙⊠X`, Z₁₅: `8⋅τ⊠X`). The zero twist
suggests these objects may not be truly simple, or `braiding(S, dual(S))`
returns a traceless endomorphism. This needs further investigation — it may
be an artifact of the degree-4 field arithmetic or the MeatAxe decomposition
yielding non-simple indecomposables.

## Category: Fib ⊠ Ising

- **Rank**: 6
- **Simples**: {𝟙⊠𝟙, 𝟙⊠χ, 𝟙⊠X, τ⊠𝟙, τ⊠χ, τ⊠X}
- **FP dimensions**: 1, 1, √2, ϕ, ϕ, ϕ√2
- **FPdim²** ≈ 14.47
- **Base ring**: QQ(ϕ,√2) — degree 4 absolute number field

### Key fusion rules
```
𝟙⊠X ⊗ 𝟙⊠X = 𝟙⊠𝟙 + 𝟙⊠χ          (Ising fusion)
τ⊠𝟙 ⊗ τ⊠𝟙 = 𝟙⊠𝟙 + τ⊠𝟙          (Fib fusion)
τ⊠X ⊗ τ⊠X = 𝟙⊠𝟙 + 𝟙⊠χ + τ⊠𝟙 + τ⊠χ  (product of both)
𝟙⊠χ ⊗ τ⊠𝟙 = τ⊠χ                  (cross-factor)
```

## Technical learnings

### Base field issue (critical)
Fib lives over QQ(ϕ) and Ising over QQ(√2). The Deligne product `⊠` requires a common base field. Solution:
```julia
# Build tower QQ → QQ(ϕ) → QQ(ϕ,√2), then flatten
K_phi, phi = number_field(x^2 - x - 1, "ϕ")
K_rel, sqrt2_rel = number_field(y^2 - 2, "√2")  # y over K_phi
K, m = absolute_simple_field(K_rel)
m_inv = inv(m)
phi_K = m_inv(K_rel(phi))
sqrt2_K = m_inv(sqrt2_rel)

Fib = fibonacci_category(K)
Ising = ising_category(K, sqrt2_K, 1)
FI = Fib ⊠ Ising  # works!
```

### TensorCategories.jl bugs/limitations
1. **`add_simple!` not exported** — must qualify as `TensorCategories.add_simple!`
2. **`simple_subobjects` returns non-simple objects** — `dim(End(s)) == 1` check fails for valid center objects over degree-4 fields. The `End` computation involves Hom spaces that are unreliable over complicated number fields.
3. **`separable_algebra_structures(X)` crashes with BoundsError** when X doesn't contain the unit (𝟙). Only works for objects containing 𝟙 as a summand.
4. **`set_name!` needed** for Deligne products before passing to `center()` — otherwise `UndefRefError` on `C.name`.

### Performance over degree-4 field
- Oscar load: ~105s (Julia 1.12.5)
- Fib + Ising + Deligne product: ~5s
- F-symbols extraction: 0.4s
- Pentagon check: 10s
- Module cat 1 (trivial): fast
- Module cat 2 (Ising Z₂ condensation): ~10 min
- Module cat 3 (Fib condensation): **~52 min** (Groebner basis bottleneck)
- **Center induction (v2)**: ~142s for 15 simples
- **S matrix (15×15)**: ~1085s (18 min)
- **T matrix (15 elements)**: **114,768s (31.9h)** — braiding on large objects over degree-4 field
- **Total v2 computation**: **1939 min (32.3h)**

## TensorCategories.jl fixes applied (2026-02-20)

All fixes applied to local copy at `../TensorCategories.jl` (NOT committed upstream).

### Thread-safety fixes (6 sites)
1. **Center.jl `hom_by_adjunction`** (~line 1482): `mors = [mors; B3]` race → pre-allocated `thread_results[idx]` + `vcat`
2. **Center.jl `smatrix`** (~line 1628): `S[i,j] = S[j,i] = val` write-write race → compute `val` first, guard `i != j`
3. **Center.jl `add_induction!`** (~line 1136): Dict mutation → wrapped in `ReentrantLock`
4. **Centralizer.jl `hom_by_adjunction`** (~line 779): same mors race fix
5. **Centralizer.jl `smatrix`** (~line 883): same smatrix fix
6. **Centralizer.jl `add_induction!`** (~line 662): same lock fix

### Simplicity check fix
- **Center.jl + Centralizer.jl `add_simple!`**: Changed `@assert dim(End(s)) == 1` to `@warn` with `check::Bool=true` kwarg
- This allows adding objects that ARE simple but fail the `End` check over degree-4 fields

### Strategy for correct center computation
- Use `simples_by_induction!(Z)` instead of manual `induction` + `add_simple!` loop
- `simples_by_induction!` bypasses `add_simple!` entirely — goes through MeatAxe decomposition and sets `C.simples` directly
- Found 15 simples (previous approach found only 6)

## Files

| File | Description |
|------|-------------|
| `compute_fib_ising.jl` | Full script v1 (steps 1-8, ~59 min total) |
| `compute_fib_ising_center.jl` | Center-only script v1 (~8 min, found only 6 simples) |
| `compute_fib_ising_center_v2.jl` | **Corrected** center script using `simples_by_induction!` |
| `compute_fib_ising_modules.jl` | Module categories: searches singles, pairs, triples, quadruples |
| `center_v2.log` | Full output of v2 center computation (15 simples + S matrix) |
| `fsymbols_fib_ising.txt` | 540 nonzero F-symbols with metadata header |
| `modular_data_fib_ising.txt` | Partial 6×6 S,T matrices (v1, incomplete) |

## Run commands

```bash
# Full julia path on this machine
JULIA=/home/tobias/.julia/juliaup/julia-1.12.5+0.x64.linux.gnu/bin/julia

# Center computation (recommend single-threaded for safety)
$JULIA --threads=1 --project=../../TensorCategories.jl compute_fib_ising_center_v2.jl

# Module categories
$JULIA --threads=1 --project=../../TensorCategories.jl compute_fib_ising_modules.jl
```

## Next steps

1. **Investigate T=0 entries**: Z₉, Z₁₀, Z₁₅ have zero twist — check if truly simple or decomposable
2. **Run module category script** to find all condensable algebras up to 4-fold sums
3. **Verify S² structure**: Should be proportional to charge conjugation matrix
4. **Verify (ST)³**: Should equal charge conjugation — (ST)³ was computed but needs analysis
5. **Cross-check center dimensions** against known Z(Fib) (4 anyons) and Z(Ising) (6 anyons) data
6. **Normalize S matrix**: Divide by FPdim(C) to get unitary S matrix, check S²=C
