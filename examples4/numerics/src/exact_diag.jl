# Exact diagonalization and sector analysis for the BLM model

using LinearAlgebra, Printf

# Group Fock basis states by quantum numbers (n_fermions, J₃)
# Returns Dict{(n, j3) => Vector{Int}} of state indices
function sector_indices(j)
    j = Int(j)
    dim = hilbert_dim(j)
    sectors = Dict{Tuple{Int,Float64}, Vector{Int}}()
    for k in 0:dim-1
        n = fermion_number(k)
        j3 = j3_value(k, j)
        key = (n, j3)
        if !haskey(sectors, key)
            sectors[key] = Int[]
        end
        push!(sectors[key], k + 1)  # 1-indexed
    end
    return sectors
end

# Full diagonalization: return sorted eigenvalues
function diag_full(j; J_coupling=1.0)
    H = build_hamiltonian(j; J_coupling=J_coupling)
    evals = eigvals(Hermitian(Matrix(H)))
    return sort(evals)
end

# Diagonalize by sector: return Dict{(n, j3) => eigenvalues}
function diag_by_sector(j; J_coupling=1.0)
    j = Int(j)
    H_full = build_hamiltonian(j; J_coupling=J_coupling)
    sectors = sector_indices(j)
    result = Dict{Tuple{Int,Float64}, Vector{Float64}}()
    for (key, indices) in sectors
        H_sector = Matrix(H_full[indices, indices])
        evals = eigvals(Hermitian(H_sector))
        result[key] = sort(evals)
    end
    return result
end

# Count BPS states (E ≈ 0)
function count_bps(eigenvalues; tol=1e-10)
    return count(e -> abs(e) < tol, eigenvalues)
end

# Print spectrum table: sorted by energy, grouped by degeneracy
function print_spectrum_table(evals; tol=1e-10, max_lines=20)
    sorted_evals = sort(evals)
    println("Energy          Degeneracy")
    println("-" ^ 30)
    i = 1
    lines = 0
    while i <= length(sorted_evals) && lines < max_lines
        E = sorted_evals[i]
        deg = 1
        while i + deg <= length(sorted_evals) && abs(sorted_evals[i+deg] - E) < tol
            deg += 1
        end
        @printf("%.8f    %d\n", E, deg)
        i += deg
        lines += 1
    end
    if i <= length(sorted_evals)
        println("... $(length(sorted_evals) - i + 1) more levels")
    end
end

# Print sector-resolved spectrum
function print_sector_spectrum(sector_evals, j; max_sectors=10, max_levels=5)
    j = Int(j)
    N = 2j + 1
    println("\nSector-resolved spectrum:")
    println("n_ferm   J₃       R-charge    Dimension   Lowest energies")
    println("-" ^ 70)

    # Sort sectors by (n, j3)
    sorted_keys = sort(collect(keys(sector_evals)))
    count = 0
    for (n, j3) in sorted_keys
        if count >= max_sectors
            println("... $(length(sorted_keys) - count) more sectors")
            break
        end
        evals = sector_evals[(n, j3)]
        R = (n - N / 2) / 3
        low_evals = evals[1:min(max_levels, length(evals))]
        @printf("%3d     %5.1f    %6.3f      %4d        %s\n",
                n, j3, R, length(evals), join([@sprintf("%.4f", e) for e in low_evals], ", "))
        count += 1
    end
end

# Find BPS states by sector
function find_bps_sectors(sector_evals; tol=1e-10)
    bps_sectors = []
    for (key, evals) in sector_evals
        n_bps = count(e -> abs(e) < tol, evals)
        if n_bps > 0
            push!(bps_sectors, (key..., n_bps))
        end
    end
    return sort(bps_sectors)
end

# Summary statistics
function spectrum_summary(evals, j; J_coupling=1.0, tol=1e-10)
    j = Int(j)
    N = 2j + 1

    E_min = minimum(evals)
    E_max = maximum(evals)
    n_bps = count_bps(evals; tol=tol)
    E_vac_pred = J_coupling * N / 3

    println("\n=== Spectrum Summary (j=$j) ===")
    println("Hilbert space dimension: $(length(evals))")
    println("Energy range: [$(round(E_min, digits=8)), $(round(E_max, digits=6))]")
    println("BPS states (E=0): $n_bps")
    println("Predicted BPS count (3^j): $(3^j)")
    println("Vacuum energy E_vac: $(round(E_vac_pred, digits=6))")

    # Check for vacuum energy in spectrum
    vac_idx = findfirst(e -> abs(e - E_vac_pred) < tol, evals)
    if vac_idx !== nothing
        println("Vacuum found at index $vac_idx: E=$(round(evals[vac_idx], digits=8))")
    end
end
