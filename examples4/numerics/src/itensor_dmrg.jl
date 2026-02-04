# ITensor MPO construction and DMRG for the BLM model

using ITensors, ITensorMPS
using WignerSymbols

include("blm_site_type.jl")

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

#==========================================================================
  QN-conserving DMRG with (Nf, J3) sector targeting
==========================================================================#

# Build BLM Hamiltonian MPO using custom BLMFermion sites with (Nf, J3) QN
function build_blm_mpo_qn(j::Int, sites; J_coupling::Float64=1.0)
    N = 2j + 1
    os = OpSum()

    # Constant term: (J/3)(2j+1)
    os += J_coupling * (2j + 1) / 3.0, "Id", 1

    # Quadratic term: -J * N_op
    for m in -j:j
        s = site_idx(m, j)
        os += -J_coupling, "N", s
    end

    # Quartic term: J * Σ_m O†_{j,m} O_{j,m}
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
                    s1 = site_idx(m1, j)
                    s2 = site_idx(m2, j)
                    s3 = site_idx(m3, j)
                    s4 = site_idx(m4, j)
                    os += coeff, "Cdag", s1, "Cdag", s2, "C", s4, "C", s3
                end
            end
        end
    end

    return MPO(os, sites)
end

# Run DMRG targeting a specific (N, J3) sector
function run_dmrg_sector(j::Int;
                         target_n::Int=j,
                         target_j3::Int=0,
                         J_coupling::Float64=1.0,
                         chi_max::Int=200,
                         nsweeps::Int=20,
                         cutoff::Float64=1e-12,
                         noise_schedule=nothing,
                         verbose::Bool=true)

    N = 2j + 1

    if verbose
        println("="^60)
        println("BLM DMRG with (Nf, J3) conservation")
        println("j = $j, N = $N sites")
        println("Target sector: (n=$target_n, J3=$target_j3)")
        println("="^60)
    end

    # Build sites with QN conservation
    sites = build_blm_sites(j; conserve_qns=true)

    # Build Hamiltonian MPO
    H_mpo = build_blm_mpo_qn(j, sites; J_coupling=J_coupling)

    # Initialize MPS in target sector
    init_state = find_sector_state(j, target_n, target_j3)
    psi0 = MPS(sites, init_state)

    if verbose
        println("Initial state flux: ", flux(psi0))
    end

    # Sweep schedule
    if noise_schedule === nothing
        noise_schedule = [1e-5, 1e-6, 1e-7, 1e-8, 1e-9, 1e-10, 0.0, 0.0, 0.0, 0.0,
                         0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
    end

    # Adaptive bond dimension schedule
    maxdims = min.(chi_max, [50, 100, 150, 200, 250, 300, 350, 400, chi_max, chi_max,
                              chi_max, chi_max, chi_max, chi_max, chi_max, chi_max,
                              chi_max, chi_max, chi_max, chi_max])

    E0, psi = dmrg(H_mpo, psi0;
                   nsweeps=nsweeps,
                   maxdim=maxdims[1:min(nsweeps, length(maxdims))],
                   cutoff=cutoff,
                   noise=noise_schedule[1:min(nsweeps, length(noise_schedule))],
                   eigsolve_krylovdim=6,
                   outputlevel=verbose ? 1 : 0)

    if verbose
        println("\nFinal energy: $E0")
        println("Final flux: ", flux(psi))

        # Verify quantum numbers
        n_measured = sum(expect(psi, "N"))
        j3_measured = measure_j3(psi, sites, j)
        println("Measured N: $n_measured (target: $target_n)")
        println("Measured J3: $j3_measured (target: $target_j3)")
    end

    return E0, psi, sites, H_mpo
end

# Scan all (n, j3) sectors to find global ground state
function scan_sectors_dmrg(j::Int;
                           J_coupling::Float64=1.0,
                           chi_max::Int=100,
                           nsweeps::Int=10,
                           cutoff::Float64=1e-10)

    sectors = enumerate_sectors(j)
    results = []

    println("Scanning $(length(sectors)) sectors for j=$j...")

    for (n, j3) in sectors
        try
            E0, _, _, _ = run_dmrg_sector(j;
                                          target_n=n, target_j3=j3,
                                          J_coupling=J_coupling,
                                          chi_max=chi_max, nsweeps=nsweeps,
                                          cutoff=cutoff, verbose=false)
            push!(results, (n=n, j3=j3, E=E0))
            @printf("  (n=%2d, j3=%3d): E = %.10f\n", n, j3, E0)
        catch e
            @warn "Sector (n=$n, j3=$j3) failed: $e"
        end
    end

    # Sort by energy
    sort!(results, by=r -> r.E)

    println("\nLowest energy states:")
    for (i, r) in enumerate(results[1:min(10, length(results))])
        @printf("  %2d. (n=%2d, j3=%3d): E = %.10f\n", i, r.n, r.j3, r.E)
    end

    return results
end
