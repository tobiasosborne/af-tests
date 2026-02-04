# Direct sector construction for BLM exact diagonalization
#
# Key optimizations:
# 1. Build sector Hamiltonians directly (not extract from full H)
# 2. Combinatorial number system for efficient basis enumeration
# 3. Cache Wigner 3j symbols (reused across matrix elements)

using LinearAlgebra, SparseArrays, Printf
using WignerSymbols

#==========================================================================
  Combinatorial Number System (Combinadics)

  Maps n-fermion Fock states to sequential indices 0..C(N,n)-1
  More memory-efficient than storing all 2^N states
==========================================================================#

# Rank: map Fock state (bits) to index in C(N,n) co-lexicographic order
function rank_combination(bits::Int, n::Int, N::Int)::Int
    rank = 0
    count = 0
    for i in 0:N-1
        if (bits >> i) & 1 == 1
            rank += binomial(i, count + 1)
            count += 1
        end
    end
    return rank
end

# Unrank: map index to Fock state (bits)
function unrank_combination(rank::Int, n::Int, N::Int)::Int
    bits = 0
    r = rank
    k = n
    for i in N-1:-1:0
        b = binomial(i, k)
        if r >= b
            bits |= (1 << i)
            r -= b
            k -= 1
        end
    end
    return bits
end

#==========================================================================
  Wigner 3j Symbol Caching

  For BLM model, we need (j j j; m1 m2 m3) with m1+m2+m3=0
  Precompute all needed symbols once per j value
==========================================================================#

function precompute_wigner_cache(j::Int)
    cache = Dict{Tuple{Int,Int,Int}, Float64}()
    for m1 in -j:j
        for m2 in -j:j
            m3 = -(m1 + m2)
            if abs(m3) <= j
                val = Float64(wigner3j(j, j, j, m1, m2, m3))
                if abs(val) > 1e-15
                    cache[(m1, m2, m3)] = val
                end
            end
        end
    end
    return cache
end

# Get cached Wigner symbol (returns 0 if not in cache)
function get_wigner(cache::Dict{Tuple{Int,Int,Int}, Float64}, m1::Int, m2::Int, m3::Int)
    return get(cache, (m1, m2, m3), 0.0)
end

#==========================================================================
  Sector Basis Construction
==========================================================================#

# Compute J3 value for a Fock state
function compute_j3(bits::Int, j::Int)::Int
    N = 2j + 1
    j3 = 0
    for s in 1:N
        if (bits >> (s-1)) & 1 == 1
            m = s - j - 1
            j3 += m
        end
    end
    return j3
end

# Build basis for sector (n_fermions, j3)
# Returns vector of Fock states (as bit patterns)
function build_sector_basis(j::Int, n_ferm::Int, j3_target::Int)
    N = 2j + 1
    states = Int[]

    # Iterate over all n-fermion states
    dim_n = binomial(N, n_ferm)
    for idx in 0:dim_n-1
        bits = unrank_combination(idx, n_ferm, N)
        if compute_j3(bits, j) == j3_target
            push!(states, bits)
        end
    end

    return states
end

# Get dimension of sector without building full basis
function sector_dimension(j::Int, n_ferm::Int, j3_target::Int)
    N = 2j + 1
    count = 0
    dim_n = binomial(N, n_ferm)
    for idx in 0:dim_n-1
        bits = unrank_combination(idx, n_ferm, N)
        if compute_j3(bits, j) == j3_target
            count += 1
        end
    end
    return count
end

#==========================================================================
  Direct Sector Hamiltonian Construction
==========================================================================#

# Apply c†_m1 c†_m2 c_m4 c_m3 to state |k⟩, return (coefficient, new_state) or nothing
# Operator order (right-to-left): c_m3 acts first, then c_m4, then c†_m2, then c†_m1
function apply_quartic_term(k::Int, m1::Int, m2::Int, m3::Int, m4::Int, j::Int)
    N = 2j + 1
    s1 = m1 + j + 1  # site index for m1
    s2 = m2 + j + 1
    s3 = m3 + j + 1
    s4 = m4 + j + 1

    # Check if m3 and m4 are occupied
    if (k >> (s3-1)) & 1 == 0 || (k >> (s4-1)) & 1 == 0
        return nothing
    end

    state = k
    sign = 1

    # Step 1: c_m3 annihilates at s3 (rightmost operator acts first)
    # Count fermions to the right of s3 for sign
    for i in 1:s3-1
        if (state >> (i-1)) & 1 == 1
            sign *= -1
        end
    end
    state &= ~(1 << (s3-1))

    # Step 2: c_m4 annihilates at s4
    for i in 1:s4-1
        if (state >> (i-1)) & 1 == 1
            sign *= -1
        end
    end
    state &= ~(1 << (s4-1))

    # Check if m1 and m2 are unoccupied (after annihilation)
    if (state >> (s1-1)) & 1 == 1 || (state >> (s2-1)) & 1 == 1
        return nothing
    end

    # Step 3: c†_m2 creates at s2
    for i in 1:s2-1
        if (state >> (i-1)) & 1 == 1
            sign *= -1
        end
    end
    state |= (1 << (s2-1))

    # Step 4: c†_m1 creates at s1
    for i in 1:s1-1
        if (state >> (i-1)) & 1 == 1
            sign *= -1
        end
    end
    state |= (1 << (s1-1))

    return (sign, state)
end

# Build sector Hamiltonian directly (sparse matrix)
function build_sector_hamiltonian(j::Int, n_ferm::Int, j3_target::Int;
                                   J_coupling::Float64=1.0,
                                   wigner_cache=nothing)
    N = 2j + 1

    # Build basis and lookup table
    basis = build_sector_basis(j, n_ferm, j3_target)
    dim = length(basis)

    if dim == 0
        return spzeros(0, 0), Int[]
    end

    state_to_idx = Dict(s => i for (i, s) in enumerate(basis))

    # Cache Wigner symbols if not provided
    if wigner_cache === nothing
        wigner_cache = precompute_wigner_cache(j)
    end

    # Sparse matrix construction
    rows = Int[]
    cols = Int[]
    vals = Float64[]

    prefactor = 2 * (2j + 1)

    for (col_idx, k) in enumerate(basis)
        # Diagonal: constant + number term
        # H = (J/3)(2j+1) - (J/3)*3*N = (J/3)(2j+1) - J*n_ferm
        diag_val = (J_coupling / 3) * (2j + 1) - J_coupling * n_ferm

        # Quartic terms (O†O)
        for m1 in -j:j
            for m2 in (m1+1):j
                m_total = m1 + m2
                if abs(m_total) > j
                    continue
                end
                c_left = get_wigner(wigner_cache, m1, m2, -m_total)
                if abs(c_left) < 1e-15
                    continue
                end

                for m3 in -j:j
                    for m4 in (m3+1):j
                        if m3 + m4 != m_total
                            continue
                        end
                        c_right = get_wigner(wigner_cache, m3, m4, -m_total)
                        if abs(c_right) < 1e-15
                            continue
                        end

                        coeff = J_coupling * prefactor * c_left * c_right

                        # Apply c†_m1 c†_m2 c_m4 c_m3 to |k⟩
                        result = apply_quartic_term(k, m1, m2, m3, m4, j)
                        if result !== nothing
                            sign, new_state = result
                            row_idx = get(state_to_idx, new_state, 0)
                            if row_idx > 0
                                push!(rows, row_idx)
                                push!(cols, col_idx)
                                push!(vals, coeff * sign)
                            end
                        end
                    end
                end
            end
        end

        # Add diagonal contribution
        push!(rows, col_idx)
        push!(cols, col_idx)
        push!(vals, diag_val)
    end

    H = sparse(rows, cols, vals, dim, dim)

    # Make Hermitian (combine duplicate entries)
    H = (H + H') / 2

    return H, basis
end

#==========================================================================
  Sector Diagonalization
==========================================================================#

# Diagonalize a single sector
function diag_sector(j::Int, n_ferm::Int, j3_target::Int;
                     J_coupling::Float64=1.0,
                     wigner_cache=nothing,
                     full_diag_threshold::Int=500)

    H, basis = build_sector_hamiltonian(j, n_ferm, j3_target;
                                        J_coupling=J_coupling,
                                        wigner_cache=wigner_cache)

    dim = size(H, 1)
    if dim == 0
        return Float64[], basis
    end

    if dim <= full_diag_threshold
        # Full diagonalization for small sectors
        evals = eigvals(Hermitian(Matrix(H)))
        return sort(real.(evals)), basis
    else
        # TODO: Use KrylovKit for large sectors (Phase 3)
        @warn "Sector (n=$n_ferm, j3=$j3_target) has dim=$dim > threshold, using full diag anyway"
        evals = eigvals(Hermitian(Matrix(H)))
        return sort(real.(evals)), basis
    end
end

# Diagonalize all sectors and return results
function diag_all_sectors(j::Int; J_coupling::Float64=1.0, verbose::Bool=true)
    N = 2j + 1
    wigner_cache = precompute_wigner_cache(j)

    results = Dict{Tuple{Int,Int}, Vector{Float64}}()
    total_states = 0

    for n in 0:N
        # Valid J3 range for n fermions
        j3_min = max(-j*n, -(2j+1-n)*j)  # approximate bounds
        j3_max = min(j*n, (2j+1-n)*j)

        for j3 in -N*j:N*j  # conservative range
            dim = sector_dimension(j, n, j3)
            if dim == 0
                continue
            end

            if verbose
                @printf("  Sector (n=%2d, j3=%3d): dim=%5d... ", n, j3, dim)
            end

            evals, _ = diag_sector(j, n, j3;
                                   J_coupling=J_coupling,
                                   wigner_cache=wigner_cache)

            results[(n, j3)] = evals
            total_states += length(evals)

            if verbose
                E_min = isempty(evals) ? NaN : evals[1]
                @printf("E_min = %.6f\n", E_min)
            end
        end
    end

    if verbose
        println("\nTotal states: $total_states (expected: $(2^N))")
    end

    return results
end

#==========================================================================
  Validation: Compare with full H extraction
==========================================================================#

# Compare direct sector construction with extraction from full H
function validate_sector_construction(j::Int; J_coupling::Float64=1.0, tol::Float64=1e-10)
    println("Validating sector construction for j=$j...")

    # Need full H construction from hamiltonian.jl
    # Assuming hilbert_dim, build_hamiltonian, sector_indices are available

    H_full = build_hamiltonian(j; J_coupling=J_coupling)
    sectors_ref = sector_indices(j)
    wigner_cache = precompute_wigner_cache(j)

    max_error = 0.0
    n_checked = 0

    for ((n, j3_float), indices) in sectors_ref
        j3 = Int(j3_float)

        # Direct construction
        H_direct, basis = build_sector_hamiltonian(j, n, j3;
                                                   J_coupling=J_coupling,
                                                   wigner_cache=wigner_cache)

        # Extraction from full H
        H_extract = Matrix(H_full[indices, indices])

        if size(H_direct) != size(H_extract)
            println("  (n=$n, j3=$j3): SIZE MISMATCH! direct=$(size(H_direct)), extract=$(size(H_extract))")
            continue
        end

        # Compare eigenvalues (more robust than matrix comparison)
        evals_direct = sort(eigvals(Hermitian(Matrix(H_direct))))
        evals_extract = sort(eigvals(Hermitian(H_extract)))

        error = maximum(abs.(evals_direct - evals_extract))
        max_error = max(max_error, error)
        n_checked += 1

        if error > tol
            println("  (n=$n, j3=$j3): ERROR = $error")
        end
    end

    println("Checked $n_checked sectors, max eigenvalue error: $max_error")

    if max_error < tol
        println("✓ Validation PASSED")
        return true
    else
        println("✗ Validation FAILED")
        return false
    end
end
