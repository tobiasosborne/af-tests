#!/usr/bin/env julia
# Run ED vs DMRG comparison for j=1,3,5

cd(@__DIR__)

include("src/fock.jl")
include("src/hamiltonian.jl")
include("src/exact_diag.jl")
include("src/itensor_dmrg.jl")
include("src/compare.jl")

println("BLM Model: ED vs DMRG Comparison")
println("=" ^ 60)
println()

# Validate each j value
for j in [1, 3, 5]
    validate_j(j; chi_max=200, nsweeps=15)
end

# Summary comparison table
results = compare_ground_states([1, 3, 5]; chi_max=200, nsweeps=15)

# Spectrum structure for j=3
compare_spectrum_structure(3)

println("\n" * "=" ^ 60)
println("Done.")
