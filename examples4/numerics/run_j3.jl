#!/usr/bin/env julia
# Detailed analysis for j=3 (N=7, dim=128)

cd(@__DIR__)

include("src/fock.jl")
include("src/hamiltonian.jl")
include("src/exact_diag.jl")
include("src/itensor_dmrg.jl")
include("src/compare.jl")

j = 3
N = 2j + 1
println("BLM Model: j=$j (N=$N, dim=$(hilbert_dim(j)))")
println("=" ^ 60)

# Full validation
results, passed = validate_j(j; chi_max=100, nsweeps=10)

# Spectrum structure
compare_spectrum_structure(j)

# BPS sectors detail
println("\n" * "-" ^ 60)
sector_evals = diag_by_sector(j)
bps = find_bps_sectors(sector_evals)
println("BPS sectors by J₃:")
for (n, j3, cnt) in sort(bps, by=x->x[2])
    R = (n - N/2) / 3
    println("  n=$n, J₃=$j3, R=$(round(R, digits=4)), count=$cnt")
end

total_bps = sum(x[3] for x in bps)
println("\nTotal BPS: $total_bps (predicted 2×3^$j = $(2*3^j))")

println("\nDone.")
