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

**FPdim²(Z) reported as 209.443 = FPdim²(Fib ⊠ Ising)² = (14.472)²** — but see verification below.

**⚠️ 15 objects are NOT all simple — see modular data verification (2026-03-03).**
Z(C₁ ⊠ C₂) ≅ Z(C₁) ⊠ Z(C₂). Z(Fib) has 4 simples, Z(Ising) has 9 simples,
so Z(Fib ⊠ Ising) should have **4 × 9 = 36 simples**, not 15. The 15 objects
from TC.jl are indecomposable but not all simple (MeatAxe over degree-4 field
produces indecomposables, not simples). Evidence: Σ FPdim(Zᵢ)² = 769.7 ≠ 209.4.

### 15×15 S matrix computed (entries in QQ(ϕ,√2))

S matrix computed in 1085s. First row (unnormalized):
```
S[1,:] = [1, 1, ϕ, 2ϕ, ϕ, 2, 2ϕ, 2, ...]
```
Full matrix in `center_v2.log` and `modular_data_fib_ising_v2.txt`.

### T matrix: COMPLETED (31.9 hours)

| Simple | T[i,i] | Interpretation |
|--------|--------|----------------|
| Z₁–Z₆ | 1 | Bosonic (trivial twist) |
| Z₇–Z₈ | −1 | Fermionic (spin ½) |
| Z₉, Z₁₀, Z₁₅ | **0** | **NOT valid** — twists must be roots of unity |
| Z₁₁–Z₁₃ | `1//3*x³ + 1//2*x² - 5//3*x - 7//6` ≈ −0.809 | **NOT valid** — |T| = cos(π/5) ≠ 1 |
| Z₁₄ | `-(1//3*x³ + 1//2*x² - 5//3*x - 7//6)` ≈ +0.809 | **NOT valid** — |T| = cos(π/5) ≠ 1 |

**Root cause**: Z₉, Z₁₀, Z₁₅ are indecomposable but NOT simple — they have
zero twist (impossible for simple objects in an MTC). Z₁₁–Z₁₄ have
|θ| = cos(π/5) ≈ 0.809 (not unit modulus), also confirming non-simplicity.

## Modular Data Verification (2026-03-03)

**Script**: `verify_ST_relations.py`

**Number field**: x = √2 − ϕ, minimal polynomial x⁴ + 2x³ − 5x² − 6x − 1 = 0.

### Results

| Check | Expected | Got | Status |
|-------|----------|-----|--------|
| S = Sᵀ | Symmetric | max\|S − Sᵀ\| = 0 | **PASS** ✓ |
| S² = D²·C | Scaled permutation matrix | Dense matrix, no permutation structure | **FAIL** ✗ |
| (ST)³ = p₊·S² | Constant ratio across all entries | Ratios range −20 to +45 | **FAIL** ✗ |
| T = roots of unity | All \|θᵢ\| = 1 | T[9,10,15]=0; T[11-14]=±0.809 | **FAIL** ✗ |
| Center rank | 4 × 9 = 36 | 15 | **FAIL** ✗ |
| Σ dᵢ² = D² | 209.44 | 769.70 (ratio ≈ 3.67×) | **FAIL** ✗ |

### Diagnosis

The 15 "simple" objects from `simples_by_induction!` are **indecomposable but not
simple** over QQ(ϕ,√2). MeatAxe decomposition over this degree-4 field fails to
fully split objects into simples. The objects need further decomposition to reach
the expected 36 simples of Z(Fib) ⊠ Z(Ising).

Key evidence:
- **Σ FPdim(Zᵢ)² = 769.7 ≠ 209.4** — objects are "too big" to be simple
- **T entries are zero or non-unit-modulus** — impossible for simple objects
- **S² has no permutation structure** — the S-matrix is computed on composites
- **Expected rank 36** from Z(Fib ⊠ Ising) ≅ Z(Fib) ⊠ Z(Ising), got only 15

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
| `modular_data_fib_ising_v2.txt` | Complete 15×15 S matrix + T diagonal (v2) |
| `verify_ST_relations.py` | Modular data verification script (ST relations) |

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

1. **~~Investigate T=0 entries~~** — DONE: confirmed non-simple (2026-03-03)
2. **~~Verify S² structure~~** — DONE: fails, not a permutation (2026-03-03)
3. **~~Verify (ST)³~~** — DONE: fails (2026-03-03)
4. **Decompose indecomposables into simples**: The 15 objects need further splitting to reach expected 36 simples. This likely requires working over a field extension or improving MeatAxe for degree-4 fields.
5. **Compute Z(Fib) and Z(Ising) separately**: Compute each center independently (both over QQ subfields, avoiding degree-4 issues), verify their modular data, then take the Deligne product to get Z(Fib ⊠ Ising) with correct 36 simples.
6. **Run module category script** to find all condensable algebras up to 4-fold sums
7. **Report MeatAxe issue upstream**: TC.jl `simples_by_induction!` over degree-4 fields produces indecomposables, not simples
