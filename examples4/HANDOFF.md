# HANDOFF: BLM Model Numerical Work

## Status: Phases 1-3 complete, j=11 working

**Completed this session**:
- Phase 3: KrylovKit Lanczos integration for large sectors
- Fast sector dimension computation via DP (instant for j=11+)
- j=11 largest sector (dim=32540) builds in 6s, Lanczos in ~80s

**Next**: Phase 4 (parallel sector diagonalization) for full j=11 spectrum.
See `SYMMETRY_IMPLEMENTATION_PLAN.md` for full plan.

## What's Done

- **Exact diagonalization**: Full spectrum by (n_fermion, J₃) sectors
- **Direct sector construction**: Builds sector H without full Hilbert space
- **KrylovKit Lanczos**: Iterative eigensolver for large sectors (dim > 500)
- **Fast sector sizing**: DP-based all_sector_dimensions() for planning
- **ITensor DMRG**: Ground state finder, MPO construction with (Nf, J₃) QN
- **Validation**: Hermiticity, H≥0, vacuum energy, BPS count = 2×3^j

## Current Scaling

| j | Sites N | Full dim | Largest sector | Build H | Lanczos (10 evals) |
|---|---------|----------|----------------|---------|-------------------|
| 7 | 15 | 32,768 | 289 | 0.2s | (full diag faster) |
| 9 | 19 | 524,288 | 2,934 | 0.5s | ~30s |
| 11 | 23 | 8,388,608 | 32,540 | 6s | ~80s |

## Key Files

| File | What it does |
|------|--------------|
| `numerics/src/fock.jl` | Fock basis, c†/c operators |
| `numerics/src/hamiltonian.jl` | H via Wigner 3j |
| `numerics/src/exact_diag.jl` | Legacy sector-resolved ED |
| `numerics/src/sector_ed.jl` | Direct sector construction + Lanczos (Phase 2-3) |
| `numerics/src/itensor_dmrg.jl` | MPO + DMRG with QN conservation |

## Running

```bash
cd examples4/numerics

# Quick j=5-7 test
julia run_sector_ed_test.jl

# j=11 single sector test
julia -e '
include("src/sector_ed.jl")
j = 11
H, basis = build_sector_hamiltonian(j, 11, 0; wigner_cache=precompute_wigner_cache(j))
evals, _, _ = lowest_eigenvalues_lanczos(H, 10)
println("BPS states: ", count(e -> abs(e) < 1e-6, evals))
'
```

## Next Steps (Phase 4)

### Parallel sector diagonalization
```julia
# In sector_ed.jl or new parallel_ed.jl
function parallel_ground_states(j::Int; J_coupling=1.0)
    sectors = all_sector_dimensions(j)
    wigner_cache = precompute_wigner_cache(j)

    results = Vector{NamedTuple}(undef, length(sectors))
    sector_list = collect(sectors)

    Threads.@threads for i in eachindex(sector_list)
        (n, j3), dim = sector_list[i]
        H, _ = build_sector_hamiltonian(j, n, j3; wigner_cache=wigner_cache)
        if dim < 500
            E_min = eigvals(Hermitian(Matrix(H)))[1]
        else
            E_min, _, _ = lowest_eigenvalues_lanczos(H, 1)
            E_min = E_min[1]
        end
        results[i] = (n=n, j3=j3, dim=dim, E_min=E_min)
    end
    return results
end
```

## Physics Notes

- BPS states at R = ±1/6 (n = j and n = j+1 fermions)
- BPS count 2×3^j confirmed numerically through j=9
- j=11 BPS sector (n=11, j3=0): ~5 BPS states found in first 10 eigenvalues
- Spectrum has only 4 distinct energy levels for j=3 (single Haldane pseudopotential)

## Dependencies

Julia packages (in global environment):
- `ITensors`, `ITensorMPS` — tensor networks
- `WignerSymbols` — 3j symbols
- `KrylovKit` — Lanczos/Arnoldi eigensolvers
- `LinearAlgebra`, `SparseArrays` — stdlib
