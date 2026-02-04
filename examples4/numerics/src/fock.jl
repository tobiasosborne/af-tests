# Fock basis and fermion operators for the BLM model
# Binary encoding: state k ∈ 0:2^N-1, bit s = occupation of site s

using SparseArrays, LinearAlgebra

# Map angular momentum m ∈ {-j,...,j} to site index s ∈ {1,...,N}
site_index(m::Int, j) = m + Int(j) + 1
m_value(s::Int, j) = s - Int(j) - 1

# Hilbert space dimension
hilbert_dim(j) = 1 << (2*Int(j) + 1)

# Number of occupied sites in Fock state k
occupation(k::Int) = count_ones(k)

# Is site s occupied in state k?  (0-indexed bit position)
is_occupied(k::Int, s::Int) = (k >> (s - 1)) & 1 == 1

# Fermion number: raw count of occupied modes
fermion_number(k::Int) = count_ones(k)

# J₃ quantum number: Σ_m m·n_m
function j3_value(k::Int, j)
    j = Int(j)
    val = 0.0
    for m in -j:j
        s = site_index(m, j)
        if is_occupied(k, s)
            val += m
        end
    end
    return val
end

# R-charge: R = (n - N/2) / 3 where n = fermion count, N = 2j+1
function r_charge(k::Int, j)
    N = 2*Int(j) + 1
    n = fermion_number(k)
    return (n - N / 2) / 3
end

# Apply creation operator c†_s to state k
# Returns (sign, new_state) or (0, -1) if site already occupied
function apply_create(k::Int, s::Int)
    if is_occupied(k, s)
        return (0, -1)
    end
    # JW sign: count occupied sites below s
    mask = (1 << (s - 1)) - 1
    sign = iseven(count_ones(k & mask)) ? 1 : -1
    return (sign, k | (1 << (s - 1)))
end

# Apply annihilation operator c_s to state k
# Returns (sign, new_state) or (0, -1) if site empty
function apply_annihilate(k::Int, s::Int)
    if !is_occupied(k, s)
        return (0, -1)
    end
    mask = (1 << (s - 1)) - 1
    sign = iseven(count_ones(k & mask)) ? 1 : -1
    return (sign, k ⊻ (1 << (s - 1)))
end

# Build sparse creation operator c†_m as dim×dim matrix
# Rows/cols indexed by Fock state integer 0..dim-1
function build_c_dag(j, m::Int)
    j = Int(j)
    s = site_index(m, j)
    dim = hilbert_dim(j)
    rows, cols, vals = Int[], Int[], Float64[]
    for k in 0:dim-1
        sign, k_new = apply_create(k, s)
        if sign != 0
            push!(rows, k_new + 1)  # 1-indexed
            push!(cols, k + 1)
            push!(vals, Float64(sign))
        end
    end
    return sparse(rows, cols, vals, dim, dim)
end

# Annihilation operator c_m = (c†_m)†
build_c(j, m::Int) = transpose(build_c_dag(j, m))

# Build number operator n_m = c†_m c_m
build_n(j, m::Int) = build_c_dag(j, m) * build_c(j, m)

# Verify canonical anticommutation relations for given j
function verify_car(j; verbose=false)
    j = Int(j)
    dim = hilbert_dim(j)
    I_mat = sparse(1.0I, dim, dim)
    all_ok = true
    for m in -j:j
        cd_m = build_c_dag(j, m)
        c_m = build_c(j, m)
        for mp in -j:j
            cd_mp = build_c_dag(j, mp)
            c_mp = build_c(j, mp)
            # {c_m, c†_m'} = δ_{m,m'}
            anti = c_m * cd_mp + cd_mp * c_m
            expected = (m == mp) ? I_mat : spzeros(dim, dim)
            err = norm(anti - expected)
            if err > 1e-12
                all_ok = false
                verbose && println("  CAR fail: {c_$m, c†_$mp} error = $err")
            end
            # {c_m, c_m'} = 0
            anti2 = c_m * c_mp + c_mp * c_m
            err2 = norm(anti2)
            if err2 > 1e-12
                all_ok = false
                verbose && println("  CAR fail: {c_$m, c_$mp} error = $err2")
            end
        end
    end
    return all_ok
end
