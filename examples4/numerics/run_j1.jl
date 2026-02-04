#!/usr/bin/env julia
# Detailed analysis for j=1 (N=3, dim=8) — hand-checkable

cd(@__DIR__)

include("src/fock.jl")
include("src/hamiltonian.jl")
include("src/exact_diag.jl")
include("src/itensor_dmrg.jl")
include("src/compare.jl")

j = 1
N = 2j + 1
println("BLM Model: j=$j (N=$N, dim=$(hilbert_dim(j)))")
println("=" ^ 60)

# Full validation
results, passed = validate_j(j; chi_max=50, nsweeps=10)

# Sector-resolved spectrum
println("\n" * "-" ^ 60)
sector_evals = diag_by_sector(j)
print_sector_spectrum(sector_evals, j; max_sectors=20, max_levels=5)

# Full spectrum
println("\n" * "-" ^ 60)
println("Full spectrum:")
evals = diag_full(j)
print_spectrum_table(evals; max_lines=20)

# BPS sectors
println("\n" * "-" ^ 60)
bps = find_bps_sectors(sector_evals)
println("BPS sectors (n_ferm, J₃, count):")
for (n, j3, cnt) in bps
    R = (n - N/2) / 3
    println("  n=$n, J₃=$j3, R=$(round(R, digits=4)), count=$cnt")
end

println("\nDone.")
