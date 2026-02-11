# HANDOFF: BLM Model — Numerics + Quantum Group Generalization

## Status: Numerics Phases 1-4 complete; Quantum Group proof tree initialized

**Latest**:
- **Quantum group proof tree**: 23-node `af` proof tree in `quantum_group_proof/`
  - Conjecture: U_q(su(2)) generalization of BLM model
  - 4 main parts: SUSY, melonic dominance, q-BPS, Turaev-Viro
  - 5 definitions, 3 external references, all 23 nodes pending
  - Run `cd quantum_group_proof && af status` to see full tree
- Phase 4: Parallel sector diagonalization via `Threads.@threads`
- `parallel_ground_states(j)` diagonalizes all (n, j3) sectors in parallel
- j=11 with 4 threads: 2048 sectors processed (1042 full diag, 1006 Lanczos)

## ⚠️ CRITICAL: j must be ODD

**The BLM model is only defined for odd j (j = 1, 3, 5, 7, 9, 11, ...).**

From `paper/Draft.tex` (line 948-950), fermion pairs couple to angular momentum:
```
ℓ = 1, 3, ..., 2j-1  (odd values only)
```

The Hamiltonian uses O_{j,m} which projects onto ℓ = j. For fermion antisymmetry,
ℓ must be odd, so **j must be odd**. Even j values give unphysical negative energies.

**Next**: Phase 5 (symmetry exploitation) - see `SYMMETRY_IMPLEMENTATION_PLAN.md`.

## What's Done

- **Exact diagonalization**: Full spectrum by (n_fermion, J₃) sectors
- **Direct sector construction**: Builds sector H without full Hilbert space
- **KrylovKit Lanczos**: Iterative eigensolver for large sectors (dim > 500)
- **Fast sector sizing**: DP-based all_sector_dimensions() for planning
- **Parallel diagonalization**: `parallel_ground_states(j)` with thread-safe progress
- **ITensor DMRG**: Ground state finder, MPO construction with (Nf, J₃) QN
- **Validation**: Hermiticity, H≥0, vacuum energy, BPS count = 2×3^j (odd j only)

## Current Scaling

| j | Sites N | Full dim | Largest sector | Build H | Lanczos (10 evals) |
|---|---------|----------|----------------|---------|-------------------|
| 7 | 15 | 32,768 | 289 | 0.2s | (full diag faster) |
| 9 | 19 | 524,288 | 2,934 | 0.5s | ~30s |
| 11 | 23 | 8,388,608 | 32,540 | 6s | ~80s |

## Key Files

| File | What it does |
|------|--------------|
| `paper/Draft.tex` | **Theory paper** — Hamiltonian derivation, BPS states |
| `numerics/src/fock.jl` | Fock basis, c†/c operators |
| `numerics/src/hamiltonian.jl` | H via Wigner 3j |
| `numerics/src/exact_diag.jl` | Legacy sector-resolved ED |
| `numerics/src/sector_ed.jl` | Direct sector + Lanczos + parallel (Phase 2-4) |
| `numerics/src/itensor_dmrg.jl` | MPO + DMRG with QN conservation |
| `numerics/run_parallel_ed.jl` | Phase 4 test script |
| `quantum_group_proof/` | **af proof tree** — 23-node quantum group generalization |
| `quantum_group_proof/README.md` | Proof tree overview, structure, next steps |
| `quantum_group_proof/proof_tree.md` | Exported full proof in markdown |

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

## Next Steps

### Quantum Group Generalization (NEW — priority)
1. **Verifier pass**: Run adversarial verification on the 23-node proof tree
   - `cd quantum_group_proof && af jobs --role verifier`
   - Priority targets: 1.1.1 (q-3j antisymmetry), 1.2.1 (q-bubble identity), 1.3.1 (q-Witten index)
2. **q-deformed numerics**: Modify Julia ED code to use quantum 3j symbols
   - Replace `wigner3j(j,j,j,m1,m2,m3)` with `q_wigner3j(j,j,j,m1,m2,m3,q)`
   - Validate: q→1 limit recovers original spectrum
   - Test BPS count stability under q-deformation
3. **Root-of-unity investigation**: Implement truncated model at q = exp(2πi/r)
4. **Deeper leaf refinement**: Nodes 1.2.3-1.2.5 need explicit asymptotic calculations

### Phase 5 - SU(2) symmetry exploitation
Use J² block decomposition for additional speedup (see SYMMETRY_IMPLEMENTATION_PLAN.md).

### Usage (Phase 4)
```julia
include("src/sector_ed.jl")

# Full j=7 spectrum
results = parallel_ground_states(7; full_diag_threshold=500, nev=10)
print_spectrum_summary(results)

# j=11 ground state search (4+ threads recommended)
results = parallel_ground_states(11; full_diag_threshold=500, nev=10)
```

## Physics Notes

**Reference**: `paper/Draft.tex` — full theory and derivations

- BPS states at R = ±1/6 (n = j and n = j+1 fermions)
- BPS count = 2×3^j confirmed numerically for odd j (j=3,5,7,9,11)
- Hamiltonian: H = (J/3)[(2j+1) - 3(N_ψ + j + ½) + 3 Σ_m O†_{j,m} O_{j,m}]
- O_{ℓ,m} projects fermion pairs onto angular momentum ℓ (odd ℓ only for fermions)
- Single Haldane pseudopotential model (ℓ = j channel only)

## Dependencies

Julia packages (in global environment):
- `ITensors`, `ITensorMPS` — tensor networks
- `WignerSymbols` — 3j symbols
- `KrylovKit` — Lanczos/Arnoldi eigensolvers
- `LinearAlgebra`, `SparseArrays` — stdlib
