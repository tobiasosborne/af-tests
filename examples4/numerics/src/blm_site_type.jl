# Custom ITensor site type for BLM model with (Nf, J3) quantum number conservation
#
# Each fermionic site carries its angular momentum quantum number m.
# The QN tracks both fermion number Nf and total angular momentum J3.

using ITensors

# Define the BLMFermion site type
# m_value is the angular momentum quantum number for this site
function ITensors.space(::SiteType"BLMFermion"; conserve_qns::Bool=true, m_value::Int=0)
    if conserve_qns
        return [
            # Empty state: Nf=0, contributes 0 to J3
            QN(("Nf", 0, -1), ("J3", 0)) => 1,
            # Occupied state: Nf=1, contributes m_value to J3
            QN(("Nf", 1, -1), ("J3", m_value)) => 1
        ]
    end
    return 2
end

# State definitions
ITensors.state(::StateName"Emp", ::SiteType"BLMFermion") = [1.0, 0.0]
ITensors.state(::StateName"Occ", ::SiteType"BLMFermion") = [0.0, 1.0]
ITensors.state(::StateName"0", st::SiteType"BLMFermion") = ITensors.state(StateName("Emp"), st)
ITensors.state(::StateName"1", st::SiteType"BLMFermion") = ITensors.state(StateName("Occ"), st)

# Operator definitions
function ITensors.op(::OpName"N", ::SiteType"BLMFermion")
    return [0.0 0.0
            0.0 1.0]
end

function ITensors.op(::OpName"C", ::SiteType"BLMFermion")
    return [0.0 1.0
            0.0 0.0]
end

function ITensors.op(::OpName"Cdag", ::SiteType"BLMFermion")
    return [0.0 0.0
            1.0 0.0]
end

function ITensors.op(::OpName"F", ::SiteType"BLMFermion")
    # Jordan-Wigner string operator
    return [1.0  0.0
            0.0 -1.0]
end

function ITensors.op(::OpName"Id", ::SiteType"BLMFermion")
    return [1.0 0.0
            0.0 1.0]
end

# Mark fermionic operators for automatic Jordan-Wigner string insertion
ITensors.has_fermion_string(::OpName"C", ::SiteType"BLMFermion") = true
ITensors.has_fermion_string(::OpName"Cdag", ::SiteType"BLMFermion") = true

# Build BLM sites with per-site m values
# Site s corresponds to m = s - j - 1, so m ranges from -j to +j
function build_blm_sites(j::Int; conserve_qns::Bool=true)
    N = 2j + 1
    sites = Vector{Index}(undef, N)
    for s in 1:N
        m = s - j - 1  # m value for site s
        sites[s] = siteind("BLMFermion", s; conserve_qns=conserve_qns, m_value=m)
    end
    return sites
end

# Find a product state configuration in a given (n, j3) sector
# Returns a vector of "Emp"/"Occ" strings for MPS initialization
function find_sector_state(j::Int, target_n::Int, target_j3::Int)
    N = 2j + 1

    # Enumerate all configurations with target_n particles
    for k in 0:(2^N - 1)
        if count_ones(k) != target_n
            continue
        end

        # Compute J3 for this configuration
        j3 = 0
        for s in 1:N
            if (k >> (s-1)) & 1 == 1
                m = s - j - 1
                j3 += m
            end
        end

        if j3 == target_j3
            # Found valid configuration
            return [(k >> (s-1)) & 1 == 1 ? "Occ" : "Emp" for s in 1:N]
        end
    end

    error("No configuration found for j=$j, n=$target_n, j3=$target_j3")
end

# List all valid (n, j3) sectors for a given j
function enumerate_sectors(j::Int)
    N = 2j + 1
    sectors = Set{Tuple{Int,Int}}()

    for k in 0:(2^N - 1)
        n = count_ones(k)
        j3 = sum((k >> (s-1)) & 1 == 1 ? (s - j - 1) : 0 for s in 1:N)
        push!(sectors, (n, j3))
    end

    return sort(collect(sectors))
end
