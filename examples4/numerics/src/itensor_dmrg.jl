# ITensor MPO construction and DMRG for the BLM model

using ITensors, ITensorMPS
using WignerSymbols

# Site index mapping: m ∈ {-j,...,j} → site s ∈ {1,...,N}
site_idx(m::Int, j::Int) = m + j + 1

# Build ITensor sites with fermion site type
function build_sites(j::Int; conserve_qns::Bool=true)
    N = 2j + 1
    return siteinds("Fermion", N; conserve_qns=conserve_qns)
end

# Build BLM Hamiltonian as MPO using OpSum
function build_blm_mpo(j::Int; J_coupling::Float64=1.0, conserve_qns::Bool=true)
    j = Int(j)
    N = 2j + 1
    sites = build_sites(j; conserve_qns=conserve_qns)

    os = OpSum()

    # Constant term: (J/3)(2j+1)
    os += J_coupling * (2j + 1) / 3.0, "Id", 1

    # Quadratic term: -(J/3) * 3 * N_op = -J * N_op
    for m in -j:j
        s = site_idx(m, j)
        os += -J_coupling, "N", s
    end

    # Quartic term: (J/3) * 3 * Σ_m O†_{j,m} O_{j,m} = J * Σ_m O†O
    # Expand O†_{j,m} O_{j,m} into c†c†cc terms:
    # O_{j,m} = √(2(2j+1)) Σ_{m1<m2, m1+m2=m} (j j j; m1 m2 -m) c_{m1} c_{m2}
    # O†_{j,m} O_{j,m} → quartic terms with coefficient:
    #   2(2j+1) * (j j j; m1 m2 -m) * (j j j; m3 m4 -m)
    # summed over m1<m2, m3<m4, m1+m2=m3+m4=m

    prefactor = 2 * (2j + 1)
    for m1 in -j:j
        for m2 in (m1+1):j
            m_total = m1 + m2
            if abs(m_total) > j
                continue
            end
            c_left = Float64(wigner3j(j, j, j, m1, m2, -m_total))
            if abs(c_left) < 1e-15
                continue
            end
            for m3 in -j:j
                for m4 in (m3+1):j
                    if m3 + m4 != m_total
                        continue
                    end
                    c_right = Float64(wigner3j(j, j, j, m3, m4, -m_total))
                    if abs(c_right) < 1e-15
                        continue
                    end
                    coeff = J_coupling * prefactor * c_left * c_right
                    # Normal-ordered: c†_{m1} c†_{m2} c_{m4} c_{m3}
                    s1 = site_idx(m1, j)
                    s2 = site_idx(m2, j)
                    s3 = site_idx(m3, j)
                    s4 = site_idx(m4, j)
                    os += coeff, "Cdag", s1, "Cdag", s2, "C", s4, "C", s3
                end
            end
        end
    end

    H_mpo = MPO(os, sites)
    return H_mpo, sites
end

# Get MPO bond dimensions
function mpo_bond_dims(H_mpo::MPO)
    return [dim(linkinds(H_mpo)[i]) for i in 1:length(H_mpo)-1]
end

# Run DMRG to find ground state
function run_dmrg(j::Int; J_coupling::Float64=1.0, chi_max::Int=100, nsweeps::Int=10,
                  cutoff::Float64=1e-10, noise_schedule=nothing, conserve_qns::Bool=true)
    H_mpo, sites = build_blm_mpo(j; J_coupling=J_coupling, conserve_qns=conserve_qns)

    # Random initial state
    psi0 = random_mps(sites; linkdims=10)

    # Sweep schedule
    if noise_schedule === nothing
        noise_schedule = [1e-6, 1e-7, 1e-8, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
    end

    E0, psi = dmrg(H_mpo, psi0; nsweeps=nsweeps, maxdim=chi_max, cutoff=cutoff,
                   noise=noise_schedule[1:min(nsweeps, length(noise_schedule))])

    return E0, psi, sites, H_mpo
end

# Convert MPO to dense matrix (for small systems, to compare with ED)
function mpo_to_matrix(H_mpo::MPO, sites)
    N = length(sites)
    dim = 2^N  # Fermion site has dim 2

    # Use inner product to compute matrix elements
    H_matrix = zeros(ComplexF64, dim, dim)

    for i in 0:dim-1
        for f in 0:dim-1
            # Create basis states as product MPS
            state_i = [isodd((i >> (s-1)) & 1) ? "Occ" : "Emp" for s in 1:N]
            state_f = [isodd((f >> (s-1)) & 1) ? "Occ" : "Emp" for s in 1:N]

            psi_i = MPS(sites, state_i)
            psi_f = MPS(sites, state_f)

            H_matrix[f+1, i+1] = inner(psi_f', H_mpo, psi_i)
        end
    end

    return real.(H_matrix)
end

# Measure fermion number from MPS
function measure_fermion_number(psi::MPS, sites)
    N = length(sites)
    n_total = 0.0
    for s in 1:N
        n_total += expect(psi, "N"; sites=s)
    end
    return n_total
end

# Measure J₃ from MPS
function measure_j3(psi::MPS, sites, j::Int)
    N = length(sites)
    j3 = 0.0
    for s in 1:N
        m = s - j - 1  # inverse of site_idx
        j3 += m * expect(psi, "N"; sites=s)
    end
    return j3
end
