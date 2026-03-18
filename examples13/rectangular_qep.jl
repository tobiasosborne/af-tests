"""
    RectangularQEP — Solver for rectangular quadratic eigenvalue problems

Solves (A + ωB + ω²C)v = 0 where A,B,C ∈ ℂ^{m×n}, m > n.

Main functions:
  - `solve_rect_qep_all(A, B, C)` — find ALL eigenvalues via SVD compression
  - `solve_rect_qep_region(A, B, C; center, radius)` — find eigenvalues in a region
  - `solve_rect_qep_near(A, B, C, ω₀)` — refine a single eigenvalue near ω₀
"""
module RectangularQEP

using LinearAlgebra
using Printf
using Statistics

export solve_rect_qep_all, solve_rect_qep_region, solve_rect_qep_near,
       qep_residual, validate_eigenvalues

# ─────────────────────────────────────────────────────────────
# Core: SVD Compression → Square QEP → Companion + QZ
# ─────────────────────────────────────────────────────────────

"""
    solve_rect_qep_all(A, B, C; ω₀=0.0, refine=1, blas_threads=8) → eigenvalues

Find ALL eigenvalues of the rectangular QEP (A + ωB + ω²C)v = 0.

Algorithm:
1. Compute SVD of P(ω₀) = A + ω₀B + ω₀²C  (m×n, cost O(mn²))
2. Project to square: Ã = Uₙ'A, B̃ = Uₙ'B, C̃ = Uₙ'C  (n×n)
3. Solve square QEP via companion linearization + QZ  (2n×2n, cost O(n³))
4. Optionally refine by re-projecting at a found eigenvalue

Returns 2n complex eigenvalues (including ∞ for singular C̃).
"""
function solve_rect_qep_all(A::AbstractMatrix, B::AbstractMatrix, C::AbstractMatrix;
                             ω₀::Number=0.0, refine::Int=1, blas_threads::Int=8)
    m, n = size(A)
    @assert size(B) == size(C) == (m, n) "A, B, C must have the same dimensions"
    @assert m >= n "System must be overdetermined (m ≥ n)"

    old_bt = BLAS.get_num_threads()
    BLAS.set_num_threads(blas_threads)

    try
        eigs = _svd_compress_solve(A, B, C, ω₀)

        for _ in 1:refine
            # Re-project at the eigenvalue closest to origin (or centroid)
            finite_eigs = filter(isfinite, eigs)
            isempty(finite_eigs) && break
            ω_ref = finite_eigs[argmin(abs.(finite_eigs))]
            eigs = _svd_compress_solve(A, B, C, ω_ref)
        end

        return eigs
    finally
        BLAS.set_num_threads(old_bt)
    end
end

function _svd_compress_solve(A, B, C, ω₀)
    m, n = size(A)
    P0 = A .+ ω₀ .* B .+ ω₀^2 .* C
    F = svd(P0)
    Un = F.U[:, 1:n]

    Ã = Un' * A
    B̃ = Un' * B
    C̃ = Un' * C

    return _solve_square_qep(Ã, B̃, C̃)
end

function _solve_square_qep(A, B, C)
    n = size(A, 1)
    # First companion linearization:
    # [  0   I ] z = ω [ I  0 ] z
    # [ -A  -B ]       [ 0  C ]
    L0 = zeros(ComplexF64, 2n, 2n)
    L1 = zeros(ComplexF64, 2n, 2n)
    L0[1:n, n+1:2n] .= I(n)
    L0[n+1:2n, 1:n] .= -A
    L0[n+1:2n, n+1:2n] .= -B
    L1[1:n, 1:n] .= I(n)
    L1[n+1:2n, n+1:2n] .= C
    return eigen(L0, L1).values
end

# ─────────────────────────────────────────────────────────────
# Region search: σ_min tracking + Newton
# ─────────────────────────────────────────────────────────────

"""
    solve_rect_qep_region(A, B, C; center, radius, grid_n=50, newton_iters=15) → eigenvalues

Find eigenvalues inside a disk in the complex plane.
Uses σ_min(P(ω)) grid search + Newton refinement.

Slower than `solve_rect_qep_all` but doesn't need companion linearization,
so it works for very large n where QZ is infeasible.
"""
function solve_rect_qep_region(A::AbstractMatrix, B::AbstractMatrix, C::AbstractMatrix;
                                center::Number=0.0+0.0im,
                                radius::Real=5.0,
                                grid_n::Int=50,
                                newton_iters::Int=15,
                                blas_threads::Int=8)
    m, n = size(A)
    old_bt = BLAS.get_num_threads()
    BLAS.set_num_threads(blas_threads)

    try
        # Grid search
        re_lo, re_hi = real(center) - radius, real(center) + radius
        im_lo, im_hi = imag(center) - radius, imag(center) + radius
        re_vals = range(re_lo, re_hi, length=grid_n)
        im_vals = range(im_lo, im_hi, length=grid_n)

        # Compute σ_min on grid (use svdvals — cheaper than full SVD)
        sigma_grid = Matrix{Float64}(undef, grid_n, grid_n)
        for j in 1:grid_n, i in 1:grid_n
            ω = complex(re_vals[i], im_vals[j])
            if abs(ω - center) > radius
                sigma_grid[i, j] = Inf
            else
                P = A .+ ω .* B .+ ω^2 .* C
                sigma_grid[i, j] = svdvals(P)[end]
            end
        end

        # Find local minima
        threshold = quantile(filter(isfinite, vec(sigma_grid)), 0.1)
        candidates = ComplexF64[]
        for i in 2:grid_n-1, j in 2:grid_n-1
            val = sigma_grid[i, j]
            val > threshold && continue
            is_min = true
            for di in -1:1, dj in -1:1
                (di == 0 && dj == 0) && continue
                if sigma_grid[i+di, j+dj] < val
                    is_min = false
                    break
                end
            end
            if is_min
                push!(candidates, complex(re_vals[i], im_vals[j]))
            end
        end

        # Newton refinement
        refined = ComplexF64[]
        for ω0 in candidates
            ω = _newton_refine(A, B, C, ω0, newton_iters)
            if isfinite(ω)
                push!(refined, ω)
            end
        end

        return _deduplicate(refined)
    finally
        BLAS.set_num_threads(old_bt)
    end
end

# ─────────────────────────────────────────────────────────────
# Single eigenvalue refinement
# ─────────────────────────────────────────────────────────────

"""
    solve_rect_qep_near(A, B, C, ω₀; max_iter=20) → ω

Refine a single eigenvalue near initial guess ω₀ using Newton's method
on σ_min(P(ω)).
"""
function solve_rect_qep_near(A::AbstractMatrix, B::AbstractMatrix, C::AbstractMatrix,
                              ω₀::Number; max_iter::Int=20)
    return _newton_refine(A, B, C, ComplexF64(ω₀), max_iter)
end

function _newton_refine(A, B, C, ω::ComplexF64, max_iter::Int)
    for _ in 1:max_iter
        P = A .+ ω .* B .+ ω^2 .* C
        F = svd(P)
        σ = F.S[end]

        # Converged
        σ < 1e-13 * F.S[1] && return ω

        u = F.U[:, end]
        v = F.Vt[end, :]

        # P'(ω) = B + 2ωC
        dP = B .+ 2ω .* C
        deriv = dot(u, dP * v)

        abs(deriv) < 1e-15 && break

        ω -= σ / deriv
    end
    return ω
end

# ─────────────────────────────────────────────────────────────
# Validation utilities
# ─────────────────────────────────────────────────────────────

"""
    qep_residual(A, B, C, ω) → relative_residual

Compute σ_min(P(ω)) / ‖P(ω)‖ as a measure of how well ω solves the QEP.
Values < 1e-10 indicate a good eigenvalue.
"""
function qep_residual(A, B, C, ω::Number)
    P = A .+ ω .* B .+ ω^2 .* C
    svals = svdvals(P)
    nrm = svals[1]
    nrm == 0 && return 0.0
    return svals[end] / nrm
end

"""
    validate_eigenvalues(A, B, C, eigenvalues; tol=1e-8) → (good, bad, residuals)

Check which eigenvalues are genuine (residual < tol).
"""
function validate_eigenvalues(A, B, C, eigenvalues; tol::Real=1e-8)
    residuals = Float64[]
    good = ComplexF64[]
    bad = ComplexF64[]

    for ω in eigenvalues
        if !isfinite(ω)
            push!(bad, ω)
            push!(residuals, Inf)
            continue
        end
        r = qep_residual(A, B, C, ω)
        push!(residuals, r)
        if r < tol
            push!(good, ω)
        else
            push!(bad, ω)
        end
    end

    return (good=good, bad=bad, residuals=residuals)
end

function _deduplicate(eigs; tol=1e-6)
    isempty(eigs) && return eigs
    unique_eigs = [eigs[1]]
    for e in eigs[2:end]
        if all(abs(e - u) > tol for u in unique_eigs)
            push!(unique_eigs, e)
        end
    end
    return unique_eigs
end

end # module

# ─────────────────────────────────────────────────────────────
# Demo / self-test
# ─────────────────────────────────────────────────────────────

if abspath(PROGRAM_FILE) == @__FILE__
    using .RectangularQEP
    using Random, LinearAlgebra

    println("RectangularQEP — Demo")
    println("=" ^ 60)

    # Generate test problem with KNOWN eigenvalues
    # (random rectangular matrices generically have NO eigenvalues —
    #  solutions only exist when the extra rows are consistent constraints,
    #  as in physical problems like Kerr QNMs)
    m, n = 200, 150
    rng = MersenneTwister(42)
    A_sq = randn(rng, ComplexF64, n, n)
    B_sq = randn(rng, ComplexF64, n, n)
    C_sq = randn(rng, ComplexF64, n, n)
    # Embed: extra rows are small perturbations of linear combos of core rows
    R = randn(rng, ComplexF64, m - n, n) * 0.01
    U_embed = vcat(Matrix{ComplexF64}(I, n, n), R)
    A = U_embed * A_sq
    B = U_embed * B_sq
    C = U_embed * C_sq

    println("\nProblem: $m × $n rectangular QEP")
    println("BLAS threads: $(BLAS.get_num_threads())")

    # Method 1: Find all eigenvalues
    println("\n--- solve_rect_qep_all ---")
    t0 = time()
    eigs = solve_rect_qep_all(A, B, C; refine=1, blas_threads=8)
    dt = time() - t0
    result = validate_eigenvalues(A, B, C, eigs)
    println("  Time: $(round(dt, digits=2))s")
    println("  Found: $(length(eigs)) eigenvalues")
    println("  Good (residual < 1e-8): $(length(result.good))")
    println("  Max residual: $(maximum(filter(isfinite, result.residuals)))")

    # Method 2: Find eigenvalues in a region
    println("\n--- solve_rect_qep_region (|ω| < 2) ---")
    t0 = time()
    eigs_region = solve_rect_qep_region(A, B, C; center=0.0, radius=2.0, grid_n=40)
    dt = time() - t0
    result_region = validate_eigenvalues(A, B, C, eigs_region)
    println("  Time: $(round(dt, digits=2))s")
    println("  Found: $(length(eigs_region)) eigenvalues in region")
    println("  Good: $(length(result_region.good))")

    # Method 3: Refine near a known approximate eigenvalue
    if !isempty(result.good)
        ω_approx = result.good[1] + 0.01 * randn(rng, ComplexF64)  # perturb
        println("\n--- solve_rect_qep_near (refine from perturbed guess) ---")
        t0 = time()
        ω_refined = solve_rect_qep_near(A, B, C, ω_approx)
        dt = time() - t0
        println("  Time: $(round(dt * 1000, digits=2))ms")
        println("  Guess:   $ω_approx  (residual $(qep_residual(A, B, C, ω_approx)))")
        println("  Refined: $ω_refined (residual $(qep_residual(A, B, C, ω_refined)))")
    end
end
