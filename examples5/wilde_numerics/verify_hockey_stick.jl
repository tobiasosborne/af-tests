#!/usr/bin/env julia
#
# verify_hockey_stick.jl
#
# Numerical verification of Wilde's conditional entropy difference via the
# correct Frenkel integral representation (Frenkel 2022, BLT 2024).
#
# The correct Frenkel formula is (natural log):
#   D(ρ||σ) = ∫₁^∞ [E_γ(ρ||σ)/γ + E_γ(σ||ρ)/γ²] dγ
#
# For bipartite τ = 𝟙_A⊗ρ_B with Tr(τ) = d_A:
#   D(ρ||τ) = ∫_{1/dA}^∞ E_β(ρ||τ)/β dβ + ∫_{dA}^∞ E_β(τ||ρ)/β² dβ - log(dA)
#
# The identity verified is H(A|B)_σ - H(A|B)_ρ = -∫₀¹ d/dt D(ρ(t)||τ(t)) dt
# where d/dt D uses the derivative of both hockey-stick terms.
#
# NOTE: The skeleton's formula (FR-1) with kernel 1/[γ(1+γ)] is INCORRECT.
# The correct formula has two terms with kernels 1/γ and 1/γ² respectively.
#
# Dependencies: LinearAlgebra (stdlib), Printf (stdlib), QuadGK (adaptive quadrature)

using LinearAlgebra
using Printf
using Random

try
    @eval using QuadGK
catch
    import Pkg
    Pkg.add("QuadGK")
    @eval using QuadGK
end

# ─── Random state generation ─────────────────────────────────────────────────

"""Wishart-ensemble random density matrix of dimension d (full rank w.p. 1)."""
function random_density_matrix(d::Int)
    G = randn(ComplexF64, d, d)
    W = G * G'
    return W / tr(W)
end

"""Random full-rank bipartite density matrix on H_A ⊗ H_B."""
random_bipartite_state(dA::Int, dB::Int) = random_density_matrix(dA * dB)

# ─── Partial trace ───────────────────────────────────────────────────────────

"""Partial trace over system A: Tr_A[ρ_AB] → ρ_B (dB × dB matrix)."""
function partial_trace_A(rho_AB::AbstractMatrix, dA::Int, dB::Int)
    rho_B = zeros(ComplexF64, dB, dB)
    for k in 1:dA
        rows = (k - 1) * dB + 1 : k * dB
        rho_B .+= @view rho_AB[rows, rows]
    end
    return rho_B
end

# ─── Entropy functions ───────────────────────────────────────────────────────

"""Von Neumann entropy S(ρ) = -Tr[ρ log ρ] (natural log)."""
function von_neumann_entropy(rho::AbstractMatrix)
    evals = eigvals(Hermitian(rho))
    s = 0.0
    for λ in evals
        if λ > 1e-15
            s -= λ * log(λ)
        end
    end
    return s
end

"""Conditional entropy H(A|B)_ρ = S(ρ_AB) - S(ρ_B)."""
function conditional_entropy(rho_AB::AbstractMatrix, dA::Int, dB::Int)
    rho_B = partial_trace_A(rho_AB, dA, dB)
    return von_neumann_entropy(rho_AB) - von_neumann_entropy(rho_B)
end

"""LHS of the identity: H(A|B)_σ - H(A|B)_ρ."""
function compute_LHS(rho_AB, sigma_AB, dA, dB)
    return conditional_entropy(sigma_AB, dA, dB) - conditional_entropy(rho_AB, dA, dB)
end

# ─── Max-relative entropy ────────────────────────────────────────────────────

"""Max-relative entropy M(ρ,τ) = inf{λ ≥ 0 : ρ ≤ λτ}, via generalized eigenvalues."""
function max_relative_entropy(rho::AbstractMatrix, tau::AbstractMatrix)
    evals = eigvals(Hermitian(rho), Hermitian(tau))
    return maximum(real.(evals))
end

# ─── Spectral projector ──────────────────────────────────────────────────────

"""Projector onto the strictly positive eigenspace of Hermitian matrix H."""
function spectral_projector_positive(H::AbstractMatrix)
    F = eigen(Hermitian(H))
    mask = F.values .> 1e-12
    if !any(mask)
        return zeros(ComplexF64, size(H))
    end
    V = F.vectors[:, mask]
    return V * V'
end

# ─── RHS computation (double integral) ───────────────────────────────────────

"""
Hockey-stick divergence E_γ(A||B) = Tr(A - γB)₊
"""
function hockey_stick(A, B, gamma)
    diff = Hermitian(A - gamma * B)
    evals = eigvals(diff)
    return sum(max(0.0, real(λ)) for λ in evals)
end

"""
Compute RHS via the correct Frenkel two-term formula.

The derivative of relative entropy along the interpolation path is:
  d/dt D(ρ(t)||τ(t)) = ∫_{1/dA}^{M_fwd} Tr[P_β · δ_AB^(β)] / β dβ
                      + ∫_{dA}^{M_rev} Tr[Q_β · (𝟙⊗δ_B - β·δ_AB)] / β² dβ

where P_β = 𝟏{ρ(t)-β·τ(t) > 0}, Q_β = 𝟏{τ(t)-β·ρ(t) > 0}.
RHS = -∫₀¹ d/dt D dt.
"""
function compute_RHS(rho_AB, sigma_AB, dA, dB; atol=1e-10, rtol=1e-8)
    d = dA * dB
    delta_AB = sigma_AB - rho_AB
    delta_B = partial_trace_A(delta_AB, dA, dB)
    I_A = Matrix{ComplexF64}(I, dA, dA)
    kron_I_delta_B = kron(I_A, delta_B)

    function outer_integrand(t)
        rho_t = (1 - t) * rho_AB + t * sigma_AB
        rho_t_B = partial_trace_A(rho_t, dA, dB)
        tau_t = kron(I_A, rho_t_B)

        # --- Term 1: forward hockey-stick, kernel 1/β ---
        # Generalized eigenvalues of (ρ(t), τ(t)) give breakpoints for P_β
        fwd_evals = sort(real.(eigvals(Hermitian(rho_t), Hermitian(tau_t))))
        M_fwd = maximum(fwd_evals)
        lo_fwd = 1.0 / dA

        term1 = 0.0
        if M_fwd > lo_fwd + 1e-14
            bps = filter(e -> lo_fwd + 1e-14 < e < M_fwd - 1e-14, fwd_evals)
            segs = vcat([lo_fwd], bps, [M_fwd])
            for i in 1:length(segs)-1
                a, b = segs[i], segs[i+1]
                b - a > 1e-15 || continue
                val, _ = quadgk(a, b; atol=atol/20, rtol=rtol/10) do β
                    P = spectral_projector_positive(rho_t - β * tau_t)
                    δβ = delta_AB - β * kron_I_delta_B
                    real(tr(P * δβ)) / β
                end
                term1 += val
            end
        end

        # --- Term 2: reverse hockey-stick, kernel 1/β² ---
        # Generalized eigenvalues of (τ(t), ρ(t)) give breakpoints for Q_β
        rev_evals = sort(real.(eigvals(Hermitian(tau_t), Hermitian(rho_t))))
        M_rev = maximum(rev_evals)
        lo_rev = Float64(dA)

        term2 = 0.0
        if M_rev > lo_rev + 1e-14
            bps_rev = filter(e -> lo_rev + 1e-14 < e < M_rev - 1e-14, rev_evals)
            segs_rev = vcat([lo_rev], bps_rev, [M_rev])
            for i in 1:length(segs_rev)-1
                a, b = segs_rev[i], segs_rev[i+1]
                b - a > 1e-15 || continue
                val, _ = quadgk(a, b; atol=atol/20, rtol=rtol/10) do β
                    Q = spectral_projector_positive(tau_t - β * rho_t)
                    deriv = kron_I_delta_B - β * delta_AB
                    real(tr(Q * deriv)) / β^2
                end
                term2 += val
            end
        end

        return term1 + term2
    end

    val, _ = quadgk(outer_integrand, 0.0, 1.0; atol=atol, rtol=rtol)
    return -val
end

# ─── Test infrastructure ─────────────────────────────────────────────────────

struct TestResult
    label::String
    dA::Int
    dB::Int
    lhs::Float64
    rhs::Float64
    abs_diff::Float64
    rel_diff::Float64
    pass::Bool
end

const TOLERANCE = 1e-5

function run_single_test(rho_AB, sigma_AB, dA, dB, label; tol=TOLERANCE)
    lhs = compute_LHS(rho_AB, sigma_AB, dA, dB)
    rhs = compute_RHS(rho_AB, sigma_AB, dA, dB)
    abs_diff = abs(lhs - rhs)
    denom = max(abs(lhs), abs(rhs), 1e-15)
    rel_diff = abs_diff / denom
    pass = abs_diff < tol

    status = pass ? "PASS" : "FAIL"
    @printf("  %-30s  LHS=%+.8f  RHS=%+.8f  |Δ|=%.2e  rel=%.2e  %s\n",
            label, lhs, rhs, abs_diff, rel_diff, status)

    return TestResult(label, dA, dB, lhs, rhs, abs_diff, rel_diff, pass)
end

# ─── Hardcoded test cases ────────────────────────────────────────────────────

function test_identical_states(dA, dB)
    rho = random_bipartite_state(dA, dB)
    return run_single_test(rho, rho, dA, dB, "identical (dA=$dA,dB=$dB)")
end

function test_product_states(dA, dB)
    rho_A = random_density_matrix(dA)
    rho_B = random_density_matrix(dB)
    sigma_A = random_density_matrix(dA)
    sigma_B = random_density_matrix(dB)
    rho_AB = kron(rho_A, rho_B)
    sigma_AB = kron(sigma_A, sigma_B)
    return run_single_test(rho_AB, sigma_AB, dA, dB, "product (dA=$dA,dB=$dB)")
end

function test_close_states(dA, dB; eps=0.01)
    rho = random_bipartite_state(dA, dB)
    perturbation = random_bipartite_state(dA, dB)
    sigma = (1 - eps) * rho + eps * perturbation
    return run_single_test(rho, sigma, dA, dB, "close ε=$eps (dA=$dA,dB=$dB)")
end

function test_maximally_mixed(dA, dB)
    d = dA * dB
    rho = Matrix{ComplexF64}(I, d, d) / d
    sigma = Matrix{ComplexF64}(I, d, d) / d
    return run_single_test(rho, sigma, dA, dB, "max-mixed (dA=$dA,dB=$dB)")
end

# ─── Test suite ──────────────────────────────────────────────────────────────

function run_test_suite(; seed=42)
    Random.seed!(seed)
    results = TestResult[]

    println("=" ^ 72)
    println("  Wilde Hockey-Stick Identity: Numerical Verification")
    println("=" ^ 72)
    println()
    println("  Identity: H(A|B)_σ - H(A|B)_ρ = -∫₀¹ d/dt D(ρ(t)||τ(t)) dt")
    println("  Tolerance: $(TOLERANCE)")
    println()

    # Hardcoded tests
    println("─── Hardcoded tests ────────────────────────────────────────────────────")
    for (dA, dB) in [(2, 2), (2, 3), (3, 3)]
        push!(results, test_identical_states(dA, dB))
        push!(results, test_maximally_mixed(dA, dB))
        push!(results, test_product_states(dA, dB))
        push!(results, test_close_states(dA, dB))
    end

    # Random tests
    dims = [(2, 2), (2, 3), (3, 2), (3, 3), (4, 4)]
    n_random = 5

    for (dA, dB) in dims
        println()
        println("─── Random tests: dA=$dA, dB=$dB ──────────────────────────────────────")
        for trial in 1:n_random
            rho = random_bipartite_state(dA, dB)
            sigma = random_bipartite_state(dA, dB)
            label = "random #$trial (dA=$dA,dB=$dB)"
            push!(results, run_single_test(rho, sigma, dA, dB, label))
        end
    end

    # Summary
    n_total = length(results)
    n_pass = count(r -> r.pass, results)
    n_fail = n_total - n_pass
    max_abs = maximum(r -> r.abs_diff, results)
    max_rel = maximum(r -> r.rel_diff, results)

    println()
    println("=" ^ 72)
    println("  SUMMARY")
    println("=" ^ 72)
    @printf("  Total tests:   %d\n", n_total)
    @printf("  Passed:        %d\n", n_pass)
    @printf("  Failed:        %d\n", n_fail)
    @printf("  Max |error|:   %.2e\n", max_abs)
    @printf("  Max relative:  %.2e\n", max_rel)
    println("=" ^ 72)

    if n_fail > 0
        println("\n  FAILED tests:")
        for r in results
            if !r.pass
                @printf("    %-30s  |Δ|=%.2e\n", r.label, r.abs_diff)
            end
        end
    end

    return results
end

# ─── Main ─────────────────────────────────────────────────────────────────────

if abspath(PROGRAM_FILE) == @__FILE__
    run_test_suite()
end
