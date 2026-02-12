# HANDOFF: BLM Model — Numerics + Quantum Group Generalization

## Status: v5 wave — 13 validated, 4 pending, 2 archived — 78% complete

**Latest (v5 session — 2 prover waves + 1 verifier wave)**:
- **Node 1.4.4 AMENDED x2** (prover-144-v5, prover-144-v6):
  - Fixed admissibility r≥2j+3 → r≥3j+2 throughout (preamble, OP2(b), OP3, L1)
  - Fixed false 1/[2j+1]_q divergence → correct boundary mechanism [r]_q=0
  - Fixed OP2(a) false equation [2j+1]_q=[r-1]_q → correct [(2r-1)/3]_q computation
  - Added OP3 two-regime analysis + clarification that Regime II is vacuous under Racah bound
  - Fixed L1 "generic q" → classical q=1 theory
  - Formal deps: CLI limitation documented (no dep-add for existing nodes)
  - **KNOWN ISSUE**: OP2(d) still claims q-3j symbols are "complex" — they are REAL for admissible j. Not yet challenged on 1.4.4 (only caught on 1.4.4.1).
  - Only open challenges: 1 note (verification record)
- **Node 1.4.4.1 AMENDED x2** (prover-1441-v5, prover-1441-v6):
  - Fixed preamble admissibility to r≥3j+2 with two-condition structure (A vs B)
  - Fixed OP2(d): q-3j symbols are REAL (not complex) for admissible j — proved rigorously via Racah formula analysis
  - Fixed Ben Geloun-Bonzom reference (bosonic, not fermionic); added Ben Geloun-Rivasseau 2017
  - OP3 two-regime analysis clarified (BLM/TV bounds coincide, Regime II vacuous)
  - Only open challenges: 1 note (verification record)
- **Verifier findings (v5)**: Key discovery that q-3j symbols at root of unity are REAL for admissible j (all [n]_q positive real for 1≤n≤3j+1<r). This invalidates OP2(d)'s premise on both nodes.
- **Critical path**: 1 → 1.4 → 1.4.4 → 1.4.4.1 (depth 4)

**Current tree (19 nodes + 1 archived child 1.4.4.2)**:
- **13 validated**: 1.1, 1.1.1, 1.1.2, 1.2, 1.3, 1.3.1, 1.3.2, 1.3.3, 1.3.4, 1.3.5, 1.4.1, 1.4.2, **1.4.3**
- **4 pending**: 1 (root), 1.4, 1.4.4, 1.4.4.1
- **3 archived**: 1.3.1.1, 1.4.5, 1.4.4.2 (duplicates/accidental)

**Previous discoveries (still valid)**:
- SUSY: {Q,Q†} ≥ 0 tautological for any operator Q (original obstruction was wrong)
- q↔q⁻¹ symmetry constraint, Taylor-Woodward root-of-unity only
- Epistemic labels: I=established, II=conjectural, III=mixed
- Part III no longer claims TV/CS equivalence

**v1 proof tree** (`quantum_group_proof/`): archived (23/23 verified, 5 validated, 18 challenged)

**Tree structure**:
- Part 0 (1.1): Well-definedness & SUSY (ESTABLISHED from v1)
    - 1.1.1: Braided fermion / U_q covariance open problem
    - 1.1.2: Correct q-melonic self-energy / vertex normalization
  - Part I (1.2): Euclidean regime q=1 (KNOWN — original BLM paper)
  - Part II (1.3): Hyperbolic regime q>0 q≠1 — CONJECTURAL
    - 1.3.1: 6j asymptotics — root-of-unity proven, fixed-real-q conjectural, q↔q⁻¹ constraint
    - 1.3.2: Non-melonic scaling — classical established, q-deformed conjectural
    - 1.3.3: Qualitative change at q=1 — conjectural, conditional on 1.3.1/1.3.2
    - 1.3.4: Volume Conjecture — motivating analogy, NOT mathematical equivalence
    - 1.3.5: BPS survival at q≠1 — OPEN (VALIDATED)
  - Part III (1.4): Root-of-unity regime — 4 children + 1 grandchild
    - 1.4.1: Turaev-Viro state sum (established math, VALIDATED)
    - 1.4.2: Boulatov GFT analogy (structural, not equivalence, VALIDATED)
    - 1.4.3: SUSY preserved + representation-theoretic constraints (refined, pending re-verification)
    - 1.4.4: Open problems and r→∞ limit (refined, pending re-verification)
      - 1.4.4.1: Detailed open problems (new child from prover, pending verification)
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
| `quantum_group_proof_v2/` | **af proof tree v2** — 19-node conjecture, 73% validated (3 geometric regimes) |
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

### Proof tree v2 — next wave (priority)
1. **Prover for 1.4.4 OP2(d)**: KNOWN BUG — OP2(d) still claims q-3j symbols are "complex"; they are REAL for admissible j. Needs prover to amend (same fix already applied to 1.4.4.1).
2. **Verifier for 1.4.4**: Re-verify after v6 amendment (will likely catch OP2(d))
3. **Verifier for 1.4.4.1**: Re-verify after v6 amendment (only notes remain)
4. **Re-verify 1.4**: amended in v4, needs fresh verifier pass
5. **Root node 1**: synthesis check + update admissibility in root statement (still says r≥2j+3)
6. **Admissibility consistency**: Root node 1 still uses r≥2j+3 — needs prover amendment to match children
3. **q-deformed numerics**: Modify Julia ED code to use quantum 3j symbols
   - Replace `wigner3j(j,j,j,m1,m2,m3)` with `q_wigner3j(j,j,j,m1,m2,m3,q)`
   - Validate: q→1 limit recovers original spectrum
   - Test BPS count stability under q-deformation
4. **Root-of-unity investigation**: Implement truncated model at q = exp(2πi/r)

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
