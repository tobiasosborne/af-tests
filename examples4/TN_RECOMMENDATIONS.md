# Tensor Network Package Recommendations

## For: MPO-DMRG simulation of the Biggs-Lin-Maldacena model (arXiv:2601.08908)

**Problem characteristics:**
- Quartic fermionic Hamiltonian with long-range couplings (3j symbols connect all pairs)
- N = 2j+1 sites, j odd, system sizes ~25-50
- Conserved U(1) charges: particle number N_psi and J_3
- Jordan-Wigner transformation to spin chain
- Dense interaction tensor (not nearest-neighbor)

---

## Primary Recommendation: ITensor (Julia)

**Package:** `ITensors.jl` + `ITensorMPS.jl`

```julia
using Pkg
Pkg.add("ITensors")
Pkg.add("ITensorMPS")
```

**Why ITensor is the best fit:**

1. **OpSum MPO construction**: Write the Hamiltonian term-by-term as operator strings;
   ITensor automatically compresses into an efficient MPO. No manual MPO building needed
   for the dense quartic interaction with 3j-symbol coefficients.

2. **QN conservation**: Native U(1) quantum number support. Enforce fixed particle number
   (N_psi) and fixed J_3 per DMRG run, giving automatic block-diagonalization.

3. **Jordan-Wigner is built in**: The `"Fermion"` site type handles JW strings
   transparently. Write psi^dag_m psi^dag_n psi_p psi_q and the JW tails are inserted
   automatically.

4. **Speed**: Julia compiles to native code. For bond dimensions chi ~ 100-500 this
   matters significantly.

5. **Ecosystem**: TDVP for time evolution, DMRG excited states (via weight penalties),
   finite-temperature methods (purification), all available.

6. **Documentation**: Extensive tutorials, active community, well-maintained.

**Schematic Hamiltonian construction:**

```julia
using ITensors, ITensorMPS

function build_hamiltonian(j::Int, J_coupling::Float64)
    N = 2*j + 1
    sites = siteinds("Fermion", N; conserve_qns=true)

    # Site index mapping: m in {-j,...,j} -> site s in {1,...,N}
    s(m) = m + j + 1

    os = OpSum()

    # --- Quadratic part: -(J/3) * 3 * (N_psi + j + 1/2) ---
    for m in -j:j
        os += -J_coupling, "N", s(m)
    end

    # --- Quartic part: (J/3) * 3 * sum_m O^dag_{j,m} O_{j,m} ---
    # Expand O^dag O into quartic fermion terms using 3j symbols.
    # Each term: coeff * c^dag_{m1} c^dag_{m2} c_{m4} c_{m3}
    # with coeff = 2*(2j+1) * (j j j; m1 m2 -(m1+m2)) * (j j j; m3 m4 -(m3+m4))
    # summed over m = m1+m2 = m3+m4
    for m1 in -j:j, m2 in (m1+1):j
        m_total = m1 + m2
        if abs(m_total) > j; continue; end
        c_left = wigner3j(j, j, j, m1, m2, -m_total)
        for m3 in -j:j, m4 in (m3+1):j
            if m3 + m4 != m_total; continue; end
            c_right = wigner3j(j, j, j, m3, m4, -m_total)
            coeff = J_coupling * 2 * (2*j + 1) * c_left * c_right
            if abs(coeff) < 1e-15; continue; end
            # Normal-ordered: c^dag_{m1} c^dag_{m2} c_{m4} c_{m3}
            os += coeff, "Cdag", s(m1), "Cdag", s(m2), "C", s(m4), "C", s(m3)
        end
    end

    # Constant shift
    os += J_coupling * (2*j + 1) / 3.0, "Id", 1

    H = MPO(os, sites)
    return H, sites
end
```

**Notes:**
- The `wigner3j` function can come from `WignerSymbols.jl` (`Pkg.add("WignerSymbols")`)
- OpSum handles all Jordan-Wigner string insertion and MPO compression internally
- For conserving J_3 as well, use `conserve_sz=true` or define custom QN tags

**DMRG run:**

```julia
psi0 = random_mps(sites; linkdims=10)
sweeps = Sweeps(10)
setmaxdim!(sweeps, 50, 100, 200, 400)
setcutoff!(sweeps, 1e-10)
E0, psi = dmrg(H, psi0, sweeps)
```

**What to target first:**
- j=3 (N=7, dim=128): sanity check against exact diag
- j=5 (N=11, dim=2048): compare with paper's exact results
- j=7 (N=15, dim=32768): still tractable by ED, good validation
- j=11 (N=23, dim=8M): match paper's results, push bond dimension
- j=13 (N=27, dim=134M): beyond paper's ED, new territory

---

## Runner-up: TeNPy (Python)

**Package:** `tenpy`

```bash
pip install physics-tenpy
```

**Strengths:**
- Python ecosystem (numpy, scipy, matplotlib integration)
- Excellent documentation and tutorials
- Good conserved charge support (U(1), Z_n)
- Mature DMRG, TEBD, TDVP implementations

**Weakness for this problem:**
- Slower than Julia (factor ~3-10x for large bond dimensions)
- MPO construction for long-range interactions slightly less automatic
- Fermion handling requires more manual care than ITensor

**When to prefer TeNPy:**
- If your existing codebase/workflow is Python-based
- If you want to combine with other Python physics packages
- If you prioritize readable code over raw speed

---

## Other packages (situational)

| Package | Language | Best for | URL |
|---------|----------|----------|-----|
| **Block2** | Python/C++ | Maximum DMRG speed, quantum chemistry problems | github.com/block-hczhai/block2-preview |
| **quimb** | Python | Flexible TN contractions, 2D methods | github.com/jcmgray/quimb |
| **DMRG++** | C++ | Production HPC runs | github.com/g1257/dmrgpp |
| **SyTen** | C++ | SU(2)-symmetric DMRG (non-abelian QN) | sytensor.org |

**Note on SyTen:** If you want to exploit the full non-abelian SU(2) symmetry (not just U(1)
subgroup J_3), SyTen is the only package that does this natively. This would give a
significant speedup for targeting specific spin sectors. However, the learning curve is steep.

---

## Key considerations for this model

1. **MPO bond dimension**: The Hamiltonian has O(N^2) quartic terms. After OpSum
   compression, expect MPO bond dimension ~O(N) to O(N^2). For j=11 (N=23), this
   is manageable.

2. **Entanglement structure**: The ground state (BPS, E=0) may have low entanglement
   and be efficiently representable as MPS. Excited states and thermal states will
   require larger bond dimensions.

3. **Symmetry sectors**: Always run DMRG in fixed (N_psi, J_3) sectors. This reduces
   the effective Hilbert space dramatically and improves convergence.

4. **Validation**: Compare j=3,5,7 against exact diagonalization before pushing to
   larger j. The paper provides detailed spectra for j up to 11.

5. **BPS states**: These are exact ground states (E=0) of H = {Q, Q^dag}. DMRG should
   find them easily. The interesting question is whether DMRG can resolve the 3^j
   near-degeneracy of BPS states at R = +/- 1/6.
