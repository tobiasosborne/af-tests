# BLM Hamiltonian construction for exact diagonalization
# H = (J/3)[(2j+1) - 3·N_op - 3(j+1/2) + 3·Σ_m O†_{j,m} O_{j,m}]

using WignerSymbols

# Build the bilinear operator O_{l,m}
# O_{l,m} = √(2(2l+1)) Σ_{m1<m2} (j j l; m1 m2 -m) c_{m1} c_{m2}
function build_O_operator(j, l::Int, m::Int, c_ops::Dict)
    j = Int(j)
    dim = hilbert_dim(j)
    O = spzeros(Float64, dim, dim)
    prefactor = sqrt(2 * (2l + 1))
    for m1 in -j:j
        for m2 in (m1+1):j
            # Selection rule: m1 + m2 + (-m) = 0, so m1 + m2 = m
            if m1 + m2 != m
                continue
            end
            w3j = Float64(wigner3j(j, j, l, m1, m2, -m))
            if abs(w3j) < 1e-15
                continue
            end
            O += prefactor * w3j * (c_ops[m1] * c_ops[m2])
        end
    end
    return O
end

# Build the full BLM Hamiltonian as a sparse matrix
# H = (J/3)[(2j+1) - 3(N_op + j + 1/2) + 3·Σ_m O†_{j,m} O_{j,m}]
function build_hamiltonian(j; J_coupling=1.0)
    j = Int(j)
    N = 2j + 1
    dim = hilbert_dim(j)
    I_mat = sparse(1.0I, dim, dim)

    # Build all annihilation operators
    c_ops = Dict(m => build_c(j, m) for m in -j:j)

    # Number operator N_op = Σ_m c†_m c_m
    N_op = sum(build_n(j, m) for m in -j:j)

    # Build O†O term: Σ_m O†_{j,m} O_{j,m}
    OdagO = spzeros(Float64, dim, dim)
    for m in -j:j
        O_m = build_O_operator(j, j, m, c_ops)
        OdagO += O_m' * O_m
    end

    # Assemble H = (J/3)[(2j+1) - 3·N_op + 3·ΣO†O]
    # Note: the formula uses N_psi (shifted) = N_op - (2j+1)/2.
    # Substituting: (2j+1) - 3(N_psi + j + 1/2) = (2j+1) - 3·N_op.
    H = (J_coupling / 3) * ((2j + 1) * I_mat - 3 * N_op + 3 * OdagO)

    return H
end

# Verify Hamiltonian properties
function verify_hamiltonian(H; label="")
    dim = size(H, 1)
    checks = Dict{String, Any}()

    # Hermiticity
    herm_err = norm(H - H') / max(norm(H), 1e-15)
    checks["Hermitian"] = herm_err < 1e-12

    # Positive semi-definite (full diag for small dim)
    if dim <= 4096
        evals = eigvals(Hermitian(Matrix(H)))
        checks["H ≥ 0"] = minimum(evals) > -1e-10
        checks["min_eig"] = minimum(evals)
        checks["max_eig"] = maximum(evals)
    end

    if !isempty(label)
        println("Hamiltonian verification ($label):")
        println("  dim = $dim")
        println("  Hermitian: $(checks["Hermitian"]) (rel err = $(round(herm_err, sigdigits=3)))")
        if haskey(checks, "min_eig")
            println("  H ≥ 0: $(checks["H ≥ 0"]) (λ_min = $(round(checks["min_eig"], sigdigits=6)))")
            println("  λ_max = $(round(checks["max_eig"], sigdigits=6))")
        end
    end

    return checks
end

# Check vacuum energy: E_vac = J(2j+1)/3
# Vacuum = state with 0 fermions (k=0)
function check_vacuum_energy(H, j; J_coupling=1.0)
    # Vacuum is the k=0 state (all sites empty)
    E_vac_matrix = real(H[1, 1])
    E_vac_predicted = J_coupling * (2*Int(j) + 1) / 3
    err = abs(E_vac_matrix - E_vac_predicted)
    return E_vac_matrix, E_vac_predicted, err
end

# Check that H commutes with N_op and J₃
function check_commutators(H, j)
    j = Int(j)
    dim = hilbert_dim(j)
    N_op = sum(build_n(j, m) for m in -j:j)

    # J₃ operator
    J3_op = spzeros(Float64, dim, dim)
    for m in -j:j
        J3_op += m * build_n(j, m)
    end

    comm_N = norm(H * N_op - N_op * H)
    comm_J3 = norm(H * J3_op - J3_op * H)

    return comm_N, comm_J3
end
