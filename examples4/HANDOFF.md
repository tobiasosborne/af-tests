# HANDOFF: BLM Model Numerical Work

## Status: ED + DMRG baseline complete

Ground state comparison working for j=1,3,5. Full Hamiltonian matrix verified (MPO = ED to machine precision).

## What's Done

- **Exact diagonalization**: Full spectrum by (n_fermion, J₃) sectors
- **ITensor DMRG**: Ground state finder, MPO construction
- **Validation**: Hermiticity, H≥0, vacuum energy, BPS count = 2×3^j
- **Matrix comparison**: ‖H_MPO - H_ED‖ ~ 1e-15 for j=1,3

## Current Limitations

1. **j=5 DMRG slow**: E₀ ~ 2e-6 after 30 sweeps (should be 0). High entanglement in BPS manifold.
2. **No QN targeting**: DMRG runs without conserving (N_psi, J₃), wastes effort.
3. **Ground state only**: No excited states, correlations, or dynamics.

## Next Steps (prioritized)

### P1: Fix j=5 convergence
```julia
# In itensor_dmrg.jl: use QN conservation to target specific sector
sites = siteinds("Fermion", N; conserve_nf=true)  # conserve fermion number
# Initialize MPS in correct sector (n=j or n=j+1 for BPS)
```

### P2: Add correlation functions
```julia
# Two-point correlator ⟨c†_m c_n⟩
function correlation_matrix(psi, sites, j)
    N = length(sites)
    C = zeros(ComplexF64, N, N)
    for i in 1:N, k in 1:N
        C[i,k] = correlation_matrix(psi, "Cdag", "C")[i,k]
    end
    return C
end
```

### P3: Add entanglement entropy
```julia
# von Neumann entropy at bond b
function entanglement_entropy(psi, b)
    orthogonalize!(psi, b)
    U, S, V = svd(psi[b], (linkind(psi, b-1), siteind(psi, b)))
    return -sum(p -> p > 0 ? p * log(p) : 0, diag(S).^2)
end
```

### P4: Excited states
```julia
# Use weight penalty: dmrg(H, [psi0], psi_init; weight=100.0)
# Returns first excited state orthogonal to psi0
```

### P5: Compare with paper's j=11 data
- File: `examples4/paper/anc/j=11_spectrum.txt`
- Format: `R-charge  Energy  Spin` (103k lines)
- Would need j=11 ED (dim 8M) or sector-targeted Lanczos

## Key Files

| File | What it does |
|------|--------------|
| `numerics/src/fock.jl` | Fock basis, c†/c operators |
| `numerics/src/hamiltonian.jl` | H via Wigner 3j |
| `numerics/src/exact_diag.jl` | Sector-resolved ED |
| `numerics/src/itensor_dmrg.jl` | MPO + DMRG |
| `numerics/src/compare.jl` | Validation driver |
| `numerics/run_comparison.jl` | Main entry point |

## Running

```bash
cd examples4/numerics
julia run_comparison.jl   # ~2 min, tests j=1,3,5
julia run_j1.jl           # detailed j=1
```

## Physics Notes

- BPS states at R = ±1/6 (n = j and n = j+1 fermions)
- BPS count 2×3^j confirmed numerically
- Spectrum has only 4 distinct energy levels for j=3 (single Haldane pseudopotential)
- Vacuum energy E_vac = J(2j+1)/3 at n=0

## Dependencies

Julia packages (already installed):
- `ITensors`, `ITensorMPS` — tensor networks
- `WignerSymbols` — 3j symbols
- `LinearAlgebra`, `SparseArrays` — stdlib
