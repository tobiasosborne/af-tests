# BLM Model Numerical Implementation Report

## Overview

Implemented exact diagonalization (ED) and DMRG for the Biggs-Lin-Maldacena Hamiltonian H = {Q, Q†} for j=1,3,5 (N=3,7,11 fermion modes).

Code location: `examples4/numerics/`

## Hamiltonian Verification

### MPO vs ED Matrix Comparison

**Yes, the full Hamiltonian matrices were compared**, not just ground state energies.

For j=1 (8×8 matrix) and j=3 (128×128 matrix), the ITensor MPO was converted to a dense matrix and compared element-by-element against the ED sparse matrix:

| j | dim | Frobenius norm ‖H_MPO - H_ED‖ | Status |
|---|-----|-------------------------------|--------|
| 1 | 8 | 1.37e-15 | ✓ identical |
| 3 | 128 | 6.72e-15 | ✓ identical |

The `mpo_to_matrix()` function computes ⟨f|H|i⟩ for all 2^N × 2^N basis pairs, giving a complete matrix comparison.

### Other Hamiltonian Checks

1. **Hermiticity**: ‖H - H†‖ < 1e-12 for all j ✓
2. **Positive semi-definite**: λ_min > -1e-15 for all j ✓
3. **Vacuum energy**: H[vacuum] = J(2j+1)/3 exact ✓
4. **Commutators**: [H, N_op] = [H, J₃] = 0 verified numerically ✓

## Ground State Results

| j | N | Hilbert dim | E₀(ED) | E₀(DMRG) | ΔE | Status |
|---|---|-------------|--------|----------|-----|--------|
| 1 | 3 | 8 | 0 | ~1e-16 | 2e-16 | ✓ PASS |
| 3 | 7 | 128 | 0 | ~1e-16 | 1e-15 | ✓ PASS |
| 5 | 11 | 2048 | 0 | 2e-6 | 2e-6 | slow convergence |

## BPS State Count

| j | Observed | Predicted 2×3^j | Match |
|---|----------|-----------------|-------|
| 1 | 6 | 6 | ✓ |
| 3 | 54 | 54 | ✓ |
| 5 | 486 | 486 | ✓ |

Factor of 2 comes from charge conjugation: BPS states appear at both n=j and n=j+1 fermions (R = ∓1/6).

## Full Spectrum Structure (j=3)

```
Energy        Degeneracy
--------------------------
0.000000      54          (BPS)
0.333333      28
1.333333      42
2.333333      4           (includes vacuum)
```

## j=5 Convergence Issue

DMRG converges slowly for j=5:
- After 15 sweeps (χ=200): E ≈ 4e-5
- After 30 sweeps (χ=400): E ≈ 2e-6

The BPS ground state has high entanglement across the 54-fold degenerate manifold. Options to improve:
1. Use QN conservation to target specific (N_psi, J₃) sector
2. Increase bond dimension beyond χ=400
3. Use subspace expansion or different noise schedule

## Running the Code

```bash
cd examples4/numerics
julia run_comparison.jl    # Full comparison for j=1,3,5
julia run_j1.jl            # Detailed j=1 analysis
julia run_j3.jl            # Detailed j=3 analysis
```

## Files

| File | LOC | Description |
|------|-----|-------------|
| src/fock.jl | 95 | Fock basis, fermion operators |
| src/hamiltonian.jl | 75 | H construction via 3j symbols |
| src/exact_diag.jl | 95 | Sector-resolved ED |
| src/itensor_dmrg.jl | 115 | MPO + DMRG |
| src/compare.jl | 130 | Validation driver |
| run_*.jl | 3×50 | Run scripts |

Total: ~760 LOC
