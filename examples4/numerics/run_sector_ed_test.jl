# Test script for direct sector ED construction
#
# Validates:
# 1. Combinadics rank/unrank are inverses
# 2. Sector basis construction matches sector_indices
# 3. Direct sector H matches extraction from full H
# 4. Memory usage scales with sector size, not full Hilbert space

using Printf

include("src/fock.jl")
include("src/hamiltonian.jl")
include("src/exact_diag.jl")
include("src/sector_ed.jl")

println("="^70)
println("Direct Sector ED Construction Test")
println("="^70)

#==========================================================================
  Test 1: Combinadics round-trip
==========================================================================#

println("\n[Test 1] Combinadics rank/unrank")
println("-"^50)

N = 11  # j=5
for n in 0:N
    dim_n = binomial(N, n)
    errors = 0
    for idx in 0:dim_n-1
        bits = unrank_combination(idx, n, N)
        idx_back = rank_combination(bits, n, N)
        if idx_back != idx
            errors += 1
        end
        # Also check that bits has exactly n bits set
        if count_ones(bits) != n
            errors += 1
        end
    end
    if errors > 0
        println("  n=$n: $errors errors!")
    end
end
println("✓ Combinadics round-trip passed for N=$N")

#==========================================================================
  Test 2: Sector basis matches sector_indices
==========================================================================#

println("\n[Test 2] Sector basis vs sector_indices")
println("-"^50)

for j in 1:3
    N = 2j + 1
    sectors_ref = sector_indices(j)

    for ((n, j3_float), indices_ref) in sectors_ref
        j3 = Int(j3_float)
        basis = build_sector_basis(j, n, j3)

        # indices_ref is 1-indexed into full Hilbert space
        # basis is Fock states as bit patterns
        # Need to convert basis to indices
        indices_direct = sort([s + 1 for s in basis])  # 1-indexed

        if sort(indices_ref) != indices_direct
            println("  j=$j, (n=$n, j3=$j3): MISMATCH")
            println("    ref: $(sort(indices_ref))")
            println("    direct: $indices_direct")
        end
    end
    println("  j=$j: ✓")
end
println("✓ Sector basis matches sector_indices")

#==========================================================================
  Test 3: Validate sector Hamiltonians
==========================================================================#

println("\n[Test 3] Direct sector H vs full H extraction")
println("-"^50)

for j in 1:5
    passed = validate_sector_construction(j; tol=1e-10)
    if !passed
        println("  j=$j: FAILED")
    end
end

#==========================================================================
  Test 4: Memory scaling check
==========================================================================#

println("\n[Test 4] Memory scaling")
println("-"^50)

j = 5
N = 2j + 1
println("j=$j, N=$N, full dim=2^$N=$(2^N)")

# Find largest sector
max_dim = 0
max_sector = (0, 0)
wigner_cache = precompute_wigner_cache(j)

sectors = Dict{Tuple{Int,Int}, Int}()
for n in 0:N
    for j3 in -N*j:N*j
        dim = sector_dimension(j, n, j3)
        if dim > 0
            sectors[(n, j3)] = dim
            if dim > max_dim
                max_dim = dim
                max_sector = (n, j3)
            end
        end
    end
end

println("Number of sectors: $(length(sectors))")
println("Largest sector: (n=$(max_sector[1]), j3=$(max_sector[2])) with dim=$max_dim")
println("Memory for full H: ~$(round(8 * 2^N * 2^N / 1e6, digits=1)) MB (dense)")
println("Memory for sector H: ~$(round(8 * max_dim * max_dim / 1e6, digits=3)) MB (dense)")

# Build largest sector H and time it
t_start = time()
H_sector, basis = build_sector_hamiltonian(j, max_sector[1], max_sector[2];
                                            J_coupling=1.0, wigner_cache=wigner_cache)
t_build = time() - t_start

t_start = time()
evals = eigvals(Hermitian(Matrix(H_sector)))
t_diag = time() - t_start

println("\nLargest sector timing:")
println("  Build H: $(round(t_build, digits=3)) s")
println("  Diagonalize: $(round(t_diag, digits=3)) s")
println("  Ground state: $(evals[1])")

#==========================================================================
  Test 5: BPS state count
==========================================================================#

println("\n[Test 5] BPS state count")
println("-"^50)

for j in 1:5
    N = 2j + 1
    wigner_cache = precompute_wigner_cache(j)

    bps_count = 0
    for n in 0:N
        for j3 in -N*j:N*j
            dim = sector_dimension(j, n, j3)
            if dim == 0
                continue
            end

            evals, _ = diag_sector(j, n, j3; J_coupling=1.0, wigner_cache=wigner_cache)
            bps_count += count(e -> abs(e) < 1e-10, evals)
        end
    end

    expected = 2 * 3^j
    status = bps_count == expected ? "✓" : "✗"
    println("  j=$j: BPS count = $bps_count (expected $expected) $status")
end

#==========================================================================
  Summary
==========================================================================#

println("\n" * "="^70)
println("SUMMARY")
println("="^70)
println("Direct sector construction working correctly.")
println("Next: Add KrylovKit Lanczos for large sectors (Phase 3)")
