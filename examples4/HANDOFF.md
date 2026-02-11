# HANDOFF: BLM Model — Numerics + Quantum Group Generalization

## Status: v1 proof tree fully verified (5/23 validated, 18/23 challenged); v2 revised conjecture initialized

**Latest**:
- **v1 proof tree COMPLETE** (`quantum_group_proof/`): 23/23 nodes verified
  - **5 validated**: 1.1 (SUSY), 1.1.2, 1.1.4, 1.2.1 (q-bubble), 1.2.4 (q-9j vanishing)
  - **18 challenged**: Parts 2-4 fundamentally broken
  - **Key finding**: quantum 6j symbols have EXPONENTIAL asymptotics for fixed q>0 q≠1
    (Taylor-Woodward 2005, Costantino 2007, Belletti-Yang 2025), NOT polynomial 1/√j.
    This destroys melonic dominance at generic q — a qualitative change, not a deformation.
- **v2 revised conjecture** (`quantum_group_proof_v2/`): 12-node tree, 3 geometric regimes
  - Part 0 (1.1): Well-definedness & SUSY (ESTABLISHED from v1)
    - 1.1.1: Braided fermion / U_q covariance open problem (from v1 node 1.1.3)
    - 1.1.2: Correct q-melonic self-energy / vertex normalization (from v1 node 1.2.2)
  - Part I (1.2): Euclidean regime q=1 (KNOWN — original BLM paper)
  - Part II (1.3): **Hyperbolic regime** q>0 q≠1 (NEW — Volume Conjecture connection)
    - 1.3.1-1.3.4: Exponential asymptotics, melonic breakdown, phase transition, Volume Conjecture
    - 1.3.5: BPS survival at q≠1 — OPEN (from v1 nodes 1.3.2, 1.3.3)
  - Part III (1.4): Topological regime q=root of unity (Turaev-Viro/Chern-Simons)
  - v1 tree retained as archive (challenge ledger = evidence trail for v2)
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
| `quantum_group_proof/` | **af proof tree v1** — 23-node original conjecture (5 validated, 18 challenged) |
| `quantum_group_proof_v2/` | **af proof tree v2** — 9-node revised conjecture (3 geometric regimes) |
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

### Revised Conjecture v2 (priority)
1. **Verify v2 proof tree**: Run adversarial verification on `quantum_group_proof_v2/`
   - Part 0 (1.1): should validate quickly (results established in v1)
   - Part I (1.2): review node citing BLM paper
   - Part II (1.3): key new claims — verify 1.3.1 (exponential asymptotics),
     1.3.2 (melonic breakdown), 1.3.3 (phase transition), 1.3.4 (Volume Conjecture)
   - Part III (1.4): verify Turaev-Viro formula (corrected from v1)
2. **q-deformed numerics**: Modify Julia ED code to use quantum 3j symbols
   - Replace `wigner3j(j,j,j,m1,m2,m3)` with `q_wigner3j(j,j,j,m1,m2,m3,q)`
   - Validate: q→1 limit recovers original spectrum
   - Test BPS count stability under q-deformation
   - **NEW**: Compute non-melonic diagram ratios at q≠1 to check exponential growth
3. **Root-of-unity investigation**: Implement truncated model at q = exp(2πi/r)
4. **Resolve v1 challenges**: 3 prover jobs on v1 tree (1.1.1, 1.1.3, 1.2.2) could be
   refined with corrected statements

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
