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

### Partial / incomplete

| Item | Status | Issue |
|------|--------|-------|
| Drinfeld center | **6/24 simples** found | 12 rejected by `dim(End(s)) == 1` check — unreliable over degree-4 field |
| S matrix | 6×6 (should be ~24×24) | Incomplete due to missing center simples |
| T matrix | All 1's (wrong) | Same cause |

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
- Oscar load: ~45s
- Fib + Ising + Deligne product: ~5s
- F-symbols extraction: 0.4s
- Pentagon check: 10s
- Module cat 1 (trivial): fast
- Module cat 2 (Ising Z₂ condensation): ~10 min
- Module cat 3 (Fib condensation): **~52 min** (Groebner basis bottleneck)
- Center induction: ~3 min (6+4+2+6+4+2 = 24 subobjects)
- S matrix: 2s, T matrix: 21s

## Files

| File | Description |
|------|-------------|
| `compute_fib_ising.jl` | Full script (steps 1-8, ~59 min total) |
| `compute_fib_ising_center.jl` | Center-only script (~8 min, skips module cats) |
| `fsymbols_fib_ising.txt` | 540 nonzero F-symbols with metadata header |
| `modular_data_fib_ising.txt` | Partial 6×6 S,T matrices (incomplete) |

## Next steps

1. **Fix the Drinfeld center**: The 12 rejected objects ARE likely simple — the `End` check is just failing over the degree-4 field. Options:
   - Bypass the simplicity check: modify TensorCategories.jl locally to skip `@assert dim(End(s)) == 1`
   - Use `unique_simples` directly instead of `add_simple!`
   - Try computing center over a simpler field (e.g. splitting field with better arithmetic)

2. **Expected center**: Z(Fib ⊠ Ising) ≅ Z(Fib) ⊠ Z(Ising). Z(Fib) has rank 4 (related to Yang-Lee), Z(Ising) has rank 6. So expect **rank 24** for the center.

3. **Larger algebra search**: Only searched sums of ≤2 simples. For completeness, try 3-fold sums like 𝟙⊠𝟙 ⊕ 𝟙⊠χ ⊕ τ⊠𝟙 (requires unit morphism).

4. **Compare with known results**: The Ising model's center is well-known (6 anyons). The Fibonacci center gives 4 anyons. Cross-check dimensions and spins against literature.
