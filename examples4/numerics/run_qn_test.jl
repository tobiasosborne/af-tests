# Test script for QN-conserving DMRG with (Nf, J3) sector targeting
#
# Validates that:
# 1. BLMFermion site type works correctly
# 2. Sector targeting initializes in correct QN sector
# 3. j=5 DMRG converges to E₀ < 1e-10 (BPS ground state)

using Printf

# Load modules
include("src/fock.jl")
include("src/hamiltonian.jl")
include("src/exact_diag.jl")
include("src/itensor_dmrg.jl")

println("="^70)
println("QN-Conserving DMRG Test: (Nf, J3) Sector Targeting")
println("="^70)

#==========================================================================
  Test 1: j=3 comparison with ED (small enough for exact comparison)
==========================================================================#

println("\n[Test 1] j=3: Compare QN-DMRG with ED")
println("-"^50)

j = 3
N = 2j + 1

# ED ground state
evals_ed = diag_full(j)
E0_ed = evals_ed[1]
println("ED ground state energy: $E0_ed")

# QN-DMRG in BPS sector (n=j, j3=0)
E0_qn, psi_qn, sites_qn, H_qn = run_dmrg_sector(j;
    target_n=j, target_j3=0,
    chi_max=100, nsweeps=15, verbose=true)

error_qn = abs(E0_qn - E0_ed)
println("\nQN-DMRG error: |E_DMRG - E_ED| = $error_qn")

if error_qn < 1e-10
    println("✓ Test 1 PASSED: j=3 QN-DMRG matches ED")
else
    println("✗ Test 1 FAILED: error too large")
end

#==========================================================================
  Test 2: j=5 convergence (the problematic case)
==========================================================================#

println("\n" * "="^70)
println("[Test 2] j=5: BPS sector convergence")
println("-"^50)

j = 5
N = 2j + 1

# ED reference for BPS sector
sector_evals = diag_by_sector(j)
bps_sector_key = (j, 0.0)  # n=j, j3=0
E0_ed_sector = sector_evals[bps_sector_key][1]
println("ED ground state in (n=$j, j3=0) sector: $E0_ed_sector")

# QN-DMRG with more sweeps for thorough test
E0_qn, psi_qn, sites_qn, H_qn = run_dmrg_sector(j;
    target_n=j, target_j3=0,
    chi_max=200, nsweeps=25, verbose=true)

error_qn = abs(E0_qn - E0_ed_sector)
println("\nQN-DMRG error: |E_DMRG - E_ED| = $error_qn")

if error_qn < 1e-10
    println("✓ Test 2 PASSED: j=5 QN-DMRG converges to BPS ground state")
elseif error_qn < 1e-6
    println("~ Test 2 PARTIAL: j=5 QN-DMRG close but not converged (error=$error_qn)")
else
    println("✗ Test 2 FAILED: j=5 convergence issue persists")
end

#==========================================================================
  Test 3: j=7 scaling test
==========================================================================#

println("\n" * "="^70)
println("[Test 3] j=7: Scaling test (15 sites, dim=32768)")
println("-"^50)

j = 7
N = 2j + 1

println("Running QN-DMRG for j=$j (N=$N sites)...")
println("Full Hilbert space: 2^$N = $(2^N)")
println("Target sector: (n=$j, j3=0)")

t_start = time()
E0_qn, psi_qn, sites_qn, H_qn = run_dmrg_sector(j;
    target_n=j, target_j3=0,
    chi_max=300, nsweeps=20, verbose=true)
t_elapsed = time() - t_start

println("\nj=7 completed in $(round(t_elapsed, digits=1)) seconds")
println("Ground state energy: $E0_qn")

if abs(E0_qn) < 1e-6
    println("✓ Test 3 PASSED: j=7 converges to BPS ground state")
else
    println("~ Test 3: j=7 energy = $E0_qn (check if BPS)")
end

#==========================================================================
  Test 4: Enumerate sectors for j=3
==========================================================================#

println("\n" * "="^70)
println("[Test 4] j=3: Sector enumeration")
println("-"^50)

j = 3
sectors = enumerate_sectors(j)
println("Found $(length(sectors)) distinct (n, j3) sectors:")
for (n, j3) in sectors[1:min(20, length(sectors))]
    println("  (n=$n, j3=$j3)")
end
if length(sectors) > 20
    println("  ... and $(length(sectors) - 20) more")
end

#==========================================================================
  Summary
==========================================================================#

println("\n" * "="^70)
println("TEST SUMMARY")
println("="^70)
println("QN-conserving DMRG implementation complete.")
println("Next: test j=7 to verify scaling improvement.")
