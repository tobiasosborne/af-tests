# Symmetry Implementation Plan for BLM Numerics

## Goal

Scale BLM model calculations from j=5 (current limit) to j=11+ by exploiting conserved quantum numbers:
- **Fermion number N** (already partially used)
- **Angular momentum J₃** (not yet used)
- **Particle-hole symmetry** (future optimization)

## Current State

### ED (`exact_diag.jl`)
- ✅ `sector_indices()` groups states by (N, J₃)
- ❌ `diag_by_sector()` builds full H first, then extracts sectors
- ❌ Uses `eigvals()` (O(dim³)) instead of Lanczos
- ❌ Sequential sector processing
- **Bottleneck**: j=5 already slow; j=7+ infeasible

### DMRG (`itensor_dmrg.jl`)
- ✅ Uses `siteinds("Fermion", N; conserve_qns=true)` — conserves Nf
- ❌ No J₃ conservation — DMRG explores all J₃ sectors
- ❌ Random initial state — not sector-targeted
- **Symptom**: j=5 converges to E₀ ~ 2e-6 instead of 0 (wanders in degenerate manifold)

### Scaling Estimates

| j | Sites N | Total dim | Largest sector | Memory (full H) |
|---|---------|-----------|----------------|-----------------|
| 5 | 11 | 2,048 | ~460 | ~30 MB |
| 7 | 15 | 32,768 | ~6,400 | ~8 GB |
| 9 | 19 | 524,288 | ~92,000 | ~2 TB |
| 11 | 23 | 8,388,608 | ~1,350,000 | ~500 TB |

With sector-direct construction + Lanczos, j=11 becomes feasible (~1-10 GB per sector).

---

## Implementation Phases

### Phase 1: ITensor (Nf, J₃) Conservation [Priority: HIGH]
**Goal**: Fix j=5 DMRG convergence, enable j=7-9

**Files to modify**: `numerics/src/itensor_dmrg.jl`

**Tasks**:
1. Define custom `BLMFermion` site type with (Nf, J₃) QN
2. Implement `build_blm_sites(j)` that assigns per-site m values
3. Add `find_sector_state(j, target_n, target_j3)` for initialization
4. Update `build_blm_mpo()` to use custom sites
5. Add `run_dmrg_sector()` with sector targeting
6. Validate: j=5 should converge to E₀ < 1e-12

**New code structure**:
```julia
# Site type definition
function ITensors.space(::SiteType"BLMFermion"; conserve_qns=true, m_value::Int=0)
    if conserve_qns
        return [
            QN(("Nf", 0, -1), ("J3", 0)) => 1,           # Empty
            QN(("Nf", 1, -1), ("J3", m_value)) => 1      # Occupied
        ]
    end
    return 2
end

# Per-site m assignment
function build_blm_sites(j::Int; conserve_qns::Bool=true)
    N = 2j + 1
    sites = [siteind("BLMFermion", s; conserve_qns, m_value=s-j-1) for s in 1:N]
    return sites
end

# Sector-targeted initialization
function find_sector_state(j::Int, target_n::Int, target_j3::Int)
    # Enumerate configurations with (n, j3) = (target_n, target_j3)
    # Return first valid product state
end
```

**Validation criteria**:
- j=5, sector (n=5, J₃=0): E₀ < 1e-12
- j=7, sector (n=7, J₃=0): converges in <50 sweeps
- Measured (N, J₃) matches target throughout DMRG

**Estimated effort**: 1 session

---

### Phase 2: ED Direct Sector Construction [Priority: HIGH]
**Goal**: Build sector Hamiltonians without full H; reach j=9

**Files to modify**: `numerics/src/exact_diag.jl`, new `numerics/src/sector_ed.jl`

**Tasks**:
1. Implement combinatorial number system (rank/unrank)
2. Create `build_sector_basis(j, n, j3)` → Vector of Fock states
3. Create `build_sector_hamiltonian(j, n, j3)` → sparse matrix
4. Cache Wigner 3j symbols (they repeat across sectors)
5. Validate: sector H matches extracted from full H for j=3,5

**New code structure**:
```julia
# Combinadics for efficient basis enumeration
function rank_combination(bits::Int, n::Int, N::Int)::Int
    # Map Fock state → index in C(N,n) ordered basis
end

function unrank_combination(rank::Int, n::Int, N::Int)::Int
    # Map index → Fock state
end

# Direct sector construction
function build_sector_hamiltonian(j::Int, n::Int, j3::Float64; J_coupling=1.0)
    basis = build_sector_basis(j, n, j3)
    state_to_idx = Dict(s => i for (i, s) in enumerate(basis))

    rows, cols, vals = Int[], Int[], Float64[]
    # Apply H terms directly in sector basis
    # ...
    return sparse(rows, cols, vals, length(basis), length(basis))
end
```

**Validation criteria**:
- `build_sector_hamiltonian(j, n, j3)` ≈ `H_full[sector_indices, sector_indices]` for j=3,5
- Memory usage O(sector_dim²) not O(2^N)

**Estimated effort**: 1-2 sessions

---

### Phase 3: Lanczos Eigensolvers [Priority: HIGH]
**Goal**: Replace full diagonalization with iterative methods

**Files to modify**: `numerics/src/sector_ed.jl`

**Dependencies**: KrylovKit.jl (add to Project.toml)

**Tasks**:
1. Add KrylovKit.jl dependency
2. Implement `lowest_eigenvalues(H, nev)` using `eigsolve`
3. Implement `eigenvalues_near_zero(H, nev)` with shift-invert for BPS
4. Add fallback to full diag for small sectors (dim < 500)
5. Benchmark: time vs accuracy tradeoff

**New code structure**:
```julia
using KrylovKit

function lowest_eigenvalues(H::SparseMatrixCSC, nev::Int; tol=1e-12)
    vals, vecs, info = eigsolve(H, nev, :SR; ishermitian=true, tol=tol)
    return real.(vals[1:info.converged]), vecs
end

function diag_sector_smart(H_sector)
    dim = size(H_sector, 1)
    if dim <= 500
        return eigvals(Hermitian(Matrix(H_sector)))
    else
        return lowest_eigenvalues(H_sector, min(50, dim))[1]
    end
end
```

**Validation criteria**:
- Ground state matches full diag for j=5
- j=7 largest sector (~6400 dim) completes in <10 seconds
- j=9 largest sector (~92k dim) completes in <5 minutes

**Estimated effort**: 1 session

---

### Phase 4: Parallelization [Priority: MEDIUM]
**Goal**: Utilize multiple cores for sector-by-sector diagonalization

**Files to modify**: `numerics/src/sector_ed.jl`, new `numerics/src/parallel_ed.jl`

**Tasks**:
1. Enumerate all (n, j3) sectors upfront
2. Parallelize with `Threads.@threads` or `Distributed.pmap`
3. Aggregate results (ground state per sector → global ground state)
4. Memory management: process one sector at a time per thread

**New code structure**:
```julia
function parallel_ground_state(j::Int; J_coupling=1.0)
    sectors = enumerate_sectors(j)
    results = Vector{NamedTuple}(undef, length(sectors))

    Threads.@threads for i in eachindex(sectors)
        n, j3 = sectors[i]
        H = build_sector_hamiltonian(j, n, j3; J_coupling)
        E_min = diag_sector_smart(H)[1]
        results[i] = (n=n, j3=j3, E=E_min)
    end

    return results
end
```

**Validation criteria**:
- Correct results match sequential version
- Near-linear speedup with core count (up to sector count)
- j=9 full spectrum in <30 minutes on 8 cores

**Estimated effort**: 1 session

---

### Phase 5: On-the-Fly H*v [Priority: LOW]
**Goal**: Handle largest sectors (dim > 100k) without storing H

**Files to modify**: `numerics/src/sector_ed.jl`

**Tasks**:
1. Define `OnTheFlyHamiltonian` struct with basis + Wigner cache
2. Implement `LinearAlgebra.mul!(y, H, x)` for matrix-free multiply
3. Interface with KrylovKit (accepts callable)
4. Benchmark memory vs speed tradeoff

**New code structure**:
```julia
struct OnTheFlyHamiltonian
    j::Int
    basis::Vector{Int}
    state_to_idx::Dict{Int,Int}
    wigner_cache::Dict{NTuple{6,Int}, Float64}
end

function LinearAlgebra.mul!(y::Vector{T}, H::OnTheFlyHamiltonian, x::Vector{T}) where T
    fill!(y, zero(T))
    for (col_idx, state) in enumerate(H.basis)
        # Apply H to state, accumulate in y
    end
    return y
end

# Use with KrylovKit
vals, vecs, _ = eigsolve(x -> H * x, dim, nev, :SR; ishermitian=true)
```

**Validation criteria**:
- Results match stored-matrix version
- j=11 sector (1.3M dim) runs without OOM
- Acceptable slowdown (<10x vs stored matrix)

**Estimated effort**: 1-2 sessions

---

### Phase 6: Non-Abelian SU(2) with TensorKit [Priority: LOW]
**Goal**: Exploit full SO(3) rotation symmetry for exponential speedup

**Files**: New `numerics/src/tensorkit_dmrg.jl`

**Dependencies**: TensorKit.jl, MPSKit.jl

**Tasks**:
1. Learn TensorKit API for SU₂ symmetric tensors
2. Rewrite BLM Hamiltonian in TensorKit formalism
3. Implement DMRG via MPSKit
4. Compare performance vs ITensor (Nf, J₃) version

**Estimated effort**: 2-3 sessions (exploratory)

---

## File Structure After Implementation

```
numerics/
├── Project.toml              # Add KrylovKit, (TensorKit, MPSKit)
├── src/
│   ├── fock.jl               # [unchanged] Fock basis utilities
│   ├── hamiltonian.jl        # [unchanged] Full H construction
│   ├── exact_diag.jl         # [minor] Keep for reference/validation
│   ├── sector_ed.jl          # [NEW] Direct sector construction + Lanczos
│   ├── parallel_ed.jl        # [NEW] Parallel sector diagonalization
│   ├── itensor_dmrg.jl       # [MAJOR] Add BLMFermion site type, sector targeting
│   ├── blm_site_type.jl      # [NEW] Custom ITensor site type definition
│   └── tensorkit_dmrg.jl     # [FUTURE] SU(2) symmetric TN
├── run_comparison.jl         # [update] Use new sector methods
├── run_j7.jl                 # [NEW] Test j=7
├── run_j9.jl                 # [NEW] Test j=9
└── run_j11.jl                # [NEW] Test j=11 (Lanczos only)
```

---

## Validation Plan

### Unit Tests
- `sector_basis(j, n, j3)` returns correct states
- `rank_combination` / `unrank_combination` are inverses
- `build_sector_hamiltonian` matches extracted sector for j=3,5
- BLMFermion site type has correct QN structure
- MPS in (n, j3) sector maintains flux throughout DMRG

### Integration Tests
- j=5 ED sector spectrum matches full diag
- j=5 DMRG with (Nf, J₃) reaches E₀ < 1e-12
- j=7 DMRG completes in reasonable time
- BPS count matches 2×3^j for all j

### Regression Tests
- Existing `run_comparison.jl` still passes
- No change to physics results for j=1,3,5

---

## Success Criteria

| Milestone | Criterion |
|-----------|-----------|
| Phase 1 complete | j=5 DMRG E₀ < 1e-12, j=7 converges |
| Phase 2 complete | j=7 ED sector matches j=7 full (via extraction from smaller test) |
| Phase 3 complete | j=9 largest sector diagonalized in <5 min |
| Phase 4 complete | j=9 full spectrum in <30 min (8 cores) |
| Phase 5 complete | j=11 BPS sector found |
| Phase 6 complete | TensorKit reproduces ITensor results |

---

## Dependencies to Add

```toml
# In numerics/Project.toml
[deps]
KrylovKit = "0b1a1467-8014-51b9-945f-bf0ae24f4b77"

# Optional (Phase 6)
TensorKit = "07d1fe3e-3e46-537d-9b1f-1b38f0a6a0c8"
MPSKit = "bb6a7f4a-6eb4-11e9-379e-7d6f65b1db84"
```

---

## Notes

### Why (Nf, J₃) before SU(2)?
- ITensor (Nf, J₃) is straightforward, well-documented
- Already provides 4-10x speedup
- TensorKit has steeper learning curve
- Can compare ITensor vs TensorKit results

### Memory Budget
- Laptop: ~16 GB → j=9 feasible with Lanczos
- Workstation: ~64 GB → j=11 sectors feasible
- Cluster: distributed → j=13+ possible

### Wigner Symbol Caching
Critical optimization: precompute all 3j symbols for given j once, reuse across sectors.
```julia
function precompute_wigner_cache(j::Int)
    cache = Dict{NTuple{6,Int}, Float64}()
    for m1 in -j:j, m2 in -j:j, m3 in -j:j
        if m1 + m2 + m3 == 0
            cache[(j,j,j,m1,m2,m3)] = Float64(wigner3j(j,j,j,m1,m2,m3))
        end
    end
    return cache
end
```

---

## Session Checklist

Before ending any session working on this plan:
```
[ ] Code compiles (`lake build` equivalent for Julia: `using BLMNumerics`)
[ ] Tests pass for completed phases
[ ] HANDOFF.md updated with progress
[ ] Relevant beads issues updated/created
[ ] git commit + push
[ ] bd sync
```
