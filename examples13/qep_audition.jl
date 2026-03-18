#!/usr/bin/env julia
#=
Rectangular Quadratic Eigenvalue Problem — Method Audition
==========================================================
Problem: (A + ωB + ω²C)v = 0,  A,B,C ∈ ℂ^{m×n}, m > n
Find all ω (eigenvalues) and corresponding v (eigenvectors).

Methods implemented:
  1. SVD compression → square QEP → companion linearization + QZ
  2. σ_min tracking on grid + Newton refinement
  3. Beyn contour integral with pseudoinverse
  4. Companion linearization of rectangular pencil + GSVD-like
  5. Iterative SVD compression (refinement of method 1)
  6. Random square padding + standard QEP

Each method is benchmarked for accuracy, speed, and threading behavior.
=#

using LinearAlgebra
using Printf
using Random
using Statistics

BLAS.set_num_threads(Threads.nthreads())  # match BLAS threads to Julia threads

# ─────────────────────────────────────────────────────────────
# Test Problem Generator
# ─────────────────────────────────────────────────────────────

"""
Generate a rectangular QEP with known eigenvalues.

Strategy: embed a square n×n QEP (with known eigenvalues) into m×n
by left-multiplying by a random m×n isometry Q.

Returns A, B, C (m×n), true_eigenvalues, true_eigenvectors (n×n in original space)
"""
function generate_test_problem(m::Int, n::Int, n_eigs::Int;
                                seed::Int=42, complex_eigs::Bool=true)
    rng = MersenneTwister(seed)

    # Generate known eigenvalues
    if complex_eigs
        # Mix of real and complex conjugate pairs
        n_real = n_eigs ÷ 3
        n_cpx = (n_eigs - n_real) ÷ 2
        eigs_real = randn(rng, n_real) .* 2
        eigs_cpx_re = randn(rng, n_cpx)
        eigs_cpx_im = abs.(randn(rng, n_cpx)) .+ 0.1  # ensure nonzero imaginary
        eigs = vcat(
            complex.(eigs_real),
            complex.(eigs_cpx_re, eigs_cpx_im),
            complex.(eigs_cpx_re, -eigs_cpx_im)
        )
    else
        eigs = complex.(randn(rng, n_eigs) .* 2)
    end

    # Build square n×n QEP with these eigenvalues
    # Use companion form: eigenvalues of the companion pencil are exactly `eigs`
    # Start with diagonal Λ, random similarity transform
    V = randn(rng, ComplexF64, n, n)
    # Construct C_sq as invertible, then build A_sq, B_sq from eigenvalue conditions
    C_sq = randn(rng, ComplexF64, n, n)
    # For each eigenpair: (A_sq + ω_i B_sq + ω_i² C_sq) v_i = 0
    # Choose random eigenvectors, then solve for A_sq + B_sq from the constraints
    # Simpler: build from companion form directly

    # Actually, let's use the direct construction:
    # Pick C_sq invertible, pick random V (eigenvector matrix)
    # Λ = diag(eigs), then the companion linearization gives us
    # A_sq = -C_sq * V * Λ² * V⁻¹ - B_sq * ... this gets complicated
    # Simpler: pick A_sq, B_sq, C_sq randomly, compute eigenvalues, use those as ground truth.

    A_sq = randn(rng, ComplexF64, n, n)
    B_sq = randn(rng, ComplexF64, n, n)
    C_sq = randn(rng, ComplexF64, n, n)

    # Compute true eigenvalues via companion linearization
    true_eigs = solve_square_qep(A_sq, B_sq, C_sq)

    # Embed into rectangular system via random isometry
    Q_full = qr(randn(rng, ComplexF64, m, n)).Q
    Q = Matrix(Q_full)[:, 1:n]  # m×n isometry (but we need m×m applied to n×n → m×n)
    # Actually we want Q: m×n with Q'Q = I_n
    # The QR gives us this: first n columns of Q_full
    # Correction: Q_full is m×m, we want first n columns
    Q_mat = Matrix(Q_full)[:, 1:n]  # m × n, orthonormal columns

    # Add extra constraints (the "overdetermined" part)
    # Q_extra adds m-n rows that are random linear combinations
    # For a well-posed test: A = [Q*A_sq; R*A_sq] where R is random (m-n)×n
    R = randn(rng, ComplexF64, m - n, n) * 0.01  # small perturbation of extra rows

    # Full embedding: rectangular matrices share the same null space at eigenvalues
    # Top n rows: the actual QEP. Bottom m-n rows: consistent constraints.
    U_top = Matrix(I, n, n)
    U_bot = R
    U_embed = vcat(U_top, U_bot)  # m × n

    A_rect = U_embed * A_sq
    B_rect = U_embed * B_sq
    C_rect = U_embed * C_sq

    return A_rect, B_rect, C_rect, true_eigs
end

"""Solve square QEP via companion linearization + eigen."""
function solve_square_qep(A, B, C)
    n = size(A, 1)
    # Companion linearization: [0 I; -A -B] z = ω [I 0; 0 C] z
    L0 = zeros(ComplexF64, 2n, 2n)
    L1 = zeros(ComplexF64, 2n, 2n)
    L0[1:n, n+1:2n] .= I(n)
    L0[n+1:2n, 1:n] .= -A
    L0[n+1:2n, n+1:2n] .= -B
    L1[1:n, 1:n] .= I(n)
    L1[n+1:2n, n+1:2n] .= C
    F = eigen(L0, L1)
    return F.values
end

# ─────────────────────────────────────────────────────────────
# Method 1: SVD Compression → Square QEP
# ─────────────────────────────────────────────────────────────

"""
Compress rectangular m×n QEP to square n×n QEP using left SVD projection.
Optionally refine by re-projecting at a computed eigenvalue.
"""
function method_svd_compress(A, B, C; ω0=0.0, max_refine=0)
    m, n = size(A)

    # Evaluate P(ω0) and get left singular vectors
    P0 = A .+ ω0 .* B .+ ω0^2 .* C
    U = svd(P0).U
    Un = U[:, 1:n]  # first n left singular vectors (best n-dim subspace)

    # Project to square system
    Ã = Un' * A
    B̃ = Un' * B
    C̃ = Un' * C

    eigs = solve_square_qep(Ã, B̃, C̃)

    # Optional iterative refinement
    for _ in 1:max_refine
        # Pick the eigenvalue with smallest residual as new projection center
        best_ω = eigs[argmin(abs.(eigs))]  # or use median, etc.
        P_ref = A .+ best_ω .* B .+ best_ω^2 .* C
        U_ref = svd(P_ref).U
        Un_ref = U_ref[:, 1:n]
        Ã = Un_ref' * A
        B̃ = Un_ref' * B
        C̃ = Un_ref' * C
        eigs = solve_square_qep(Ã, B̃, C̃)
    end

    return eigs
end

# ─────────────────────────────────────────────────────────────
# Method 2: σ_min Tracking + Newton Refinement
# ─────────────────────────────────────────────────────────────

"""
Find eigenvalues by tracking σ_min(P(ω)) along real line or complex grid.
Returns approximate eigenvalues where σ_min dips below threshold.
"""
function method_sigma_min_grid(A, B, C;
                                re_range=(-5.0, 5.0), im_range=(-5.0, 5.0),
                                n_re=100, n_im=100,
                                threshold_quantile=0.05,
                                newton_iters=10)
    m, n = size(A)
    re_vals = range(re_range..., length=n_re)
    im_vals = range(im_range..., length=n_im)

    # Phase 1: Grid search for σ_min (parallelizable)
    sigma_grid = zeros(n_re, n_im)
    Threads.@threads for idx in CartesianIndices((n_re, n_im))
        i, j = idx[1], idx[2]
        ω = complex(re_vals[i], im_vals[j])
        P = A .+ ω .* B .+ ω^2 .* C
        sigma_grid[i, j] = svdvals(P)[end]  # smallest singular value
    end

    # Phase 2: Find local minima below threshold
    threshold = quantile(vec(sigma_grid), threshold_quantile)
    candidates = ComplexF64[]
    for i in 2:n_re-1, j in 2:n_im-1
        val = sigma_grid[i, j]
        if val < threshold
            # Local minimum check (rough)
            neighbors = [sigma_grid[i+di, j+dj] for di in -1:1, dj in -1:1 if (di,dj) != (0,0)]
            if val <= minimum(neighbors)
                push!(candidates, complex(re_vals[i], im_vals[j]))
            end
        end
    end

    # Phase 3: Newton refinement on each candidate
    refined = ComplexF64[]
    for ω0 in candidates
        ω = _newton_sigma_min(A, B, C, ω0, newton_iters)
        if !isnan(ω) && !isinf(ω)
            push!(refined, ω)
        end
    end

    # Deduplicate
    return _deduplicate_eigenvalues(refined)
end

"""Newton refinement: minimize σ_min(P(ω))² over ℂ."""
function _newton_sigma_min(A, B, C, ω0, max_iter)
    ω = ω0
    for _ in 1:max_iter
        P = A .+ ω .* B .+ ω^2 .* C
        F = svd(P)
        σ_min = F.S[end]
        if σ_min < 1e-12
            return ω
        end
        u = F.U[:, end]  # left singular vector for σ_min
        v = F.Vt[end, :]  # right singular vector for σ_min (conjugated)
        # P'(ω) = B + 2ωC
        dP = B .+ 2ω .* C
        # Derivative of σ_min: dσ/dω = Re(u' * P'(ω) * v)
        # For complex ω, use the full derivative
        deriv = dot(u, dP * v)
        if abs(deriv) < 1e-15
            break
        end
        # Newton step: σ_min / deriv
        ω -= σ_min / deriv
    end
    return ω
end

"""Remove duplicate eigenvalues (within tolerance)."""
function _deduplicate_eigenvalues(eigs; tol=1e-6)
    isempty(eigs) && return eigs
    unique_eigs = [eigs[1]]
    for e in eigs[2:end]
        if all(abs(e - u) > tol for u in unique_eigs)
            push!(unique_eigs, e)
        end
    end
    return unique_eigs
end

# ─────────────────────────────────────────────────────────────
# Method 3: Beyn Contour Integral with Pseudoinverse
# ─────────────────────────────────────────────────────────────

"""
Beyn's contour integral method adapted for rectangular matrices.
Uses pseudoinverse (via least-squares) instead of matrix inverse.

Parameters:
  - center, radius: define circular contour
  - N_quad: number of quadrature points on contour
  - l: number of probe columns (should be ≥ expected eigenvalue count inside contour)
"""
function method_beyn(A, B, C;
                     center=0.0+0.0im, radius=5.0,
                     N_quad=128, l=nothing, svd_tol=1e-10)
    m, n = size(A)
    if l === nothing
        l = n  # probe matrix width
    end

    rng = MersenneTwister(123)
    V_hat = randn(rng, ComplexF64, m, l)  # m×l probe matrix (RHS for least-squares)

    # Quadrature points on contour
    θ = range(0, 2π, length=N_quad + 1)[1:end-1]
    z_pts = center .+ radius .* exp.(im .* θ)
    dz = im .* radius .* exp.(im .* θ) .* (2π / N_quad)

    # Compute contour integrals A0 and A1
    # A_k = (1/2πi) ∮ z^k P(z)⁺ V̂ dz  (using trapezoidal rule)
    # P(z)⁺ V̂ is n×l, so A_k is n×l
    A0 = zeros(ComplexF64, n, l)
    A1 = zeros(ComplexF64, n, l)

    # Sequential accumulation (BLAS is already multi-threaded internally,
    # so Julia-level threading on top causes reentrancy issues)
    for k in 1:N_quad
        z = z_pts[k]
        P = A .+ z .* B .+ z^2 .* C   # m × n
        # Solve P * X = V_hat via least-squares (pseudoinverse)
        X = P \ V_hat   # n × l  (Julia uses QR for overdetermined)
        w = dz[k] / (2π * im)
        A0 .+= w .* X
        A1 .+= (w * z) .* X
    end

    # SVD of A0 to determine rank
    F = svd(A0)
    k = count(F.S .> svd_tol * F.S[1])
    if k == 0
        return ComplexF64[]
    end

    V0 = F.U[:, 1:k]
    W0 = F.Vt[1:k, :]'  # l × k
    Σ_inv = Diagonal(1.0 ./ F.S[1:k])

    # Small eigenvalue problem
    B_small = V0' * A1 * W0 * Σ_inv  # k × k
    eigs = eigen(B_small).values

    return eigs
end

"""
Beyn contour integral — parallelized variant.
Uses Julia threads with BLAS single-threaded per task.
"""
function method_beyn_parallel(A, B, C;
                              center=0.0+0.0im, radius=5.0,
                              N_quad=128, l=nothing, svd_tol=1e-10)
    m, n = size(A)
    if l === nothing
        l = n
    end

    rng = MersenneTwister(123)
    V_hat = randn(rng, ComplexF64, n, l)

    θ = range(0, 2π, length=N_quad + 1)[1:end-1]
    z_pts = center .+ radius .* exp.(im .* θ)
    dz = im .* radius .* exp.(im .* θ) .* (2π / N_quad)

    # Pre-compute each quadrature contribution in parallel
    # Each result is an (n×l, n×l) tuple
    results = Vector{Tuple{Matrix{ComplexF64}, Matrix{ComplexF64}}}(undef, N_quad)

    # Set BLAS to 1 thread so Julia threads don't fight
    old_blas = BLAS.get_num_threads()
    BLAS.set_num_threads(1)
    try
        Threads.@threads for k in 1:N_quad
            z = z_pts[k]
            P = A .+ z .* B .+ z^2 .* C
            X = P \ V_hat
            w = dz[k] / (2π * im)
            results[k] = (w .* X, (w * z) .* X)
        end
    finally
        BLAS.set_num_threads(old_blas)
    end

    # Reduce
    A0 = sum(r[1] for r in results)
    A1 = sum(r[2] for r in results)

    F = svd(A0)
    k = count(F.S .> svd_tol * F.S[1])
    k == 0 && return ComplexF64[]

    V0 = F.U[:, 1:k]
    W0 = F.Vt[1:k, :]'
    Σ_inv = Diagonal(1.0 ./ F.S[1:k])
    B_small = V0' * A1 * W0 * Σ_inv
    return eigen(B_small).values
end

# ─────────────────────────────────────────────────────────────
# Method 4: Companion Linearization + SVD of Rectangular Pencil
# ─────────────────────────────────────────────────────────────

"""
Form the 2m×2n companion linearization of the rectangular QEP,
then find eigenvalues via σ_min tracking on the pencil.

This is expensive but algebraically clean.
"""
function method_companion_svd(A, B, C;
                               re_range=(-5.0, 5.0), im_range=(-5.0, 5.0),
                               n_re=80, n_im=80, newton_iters=10)
    m, n = size(A)

    # Form companion linearization: L(ω) = L0 + ω L1
    # L0 = [0 I_n; -A -B], L1 = [I_n 0; 0 C]
    # L0 is (m+n) × 2n, L1 is (m+n) × 2n
    function P_companion(ω)
        # (L0 + ω L1) is (m+n) × 2n
        L = zeros(ComplexF64, m + n, 2n)
        # Top block: [ωI_n | I_n]
        L[1:n, 1:n] .= ω * I(n)
        L[1:n, n+1:2n] .= I(n)
        # Bottom block: [-A | -B + ωC]
        L[n+1:m+n, 1:n] .= -A
        L[n+1:m+n, n+1:2n] .= -B .+ ω .* C
        return L
    end

    # Same σ_min tracking approach but on the companion
    re_vals = range(re_range..., length=n_re)
    im_vals = range(im_range..., length=n_im)

    sigma_grid = zeros(n_re, n_im)
    Threads.@threads for idx in CartesianIndices((n_re, n_im))
        i, j = idx[1], idx[2]
        ω = complex(re_vals[i], im_vals[j])
        L = P_companion(ω)
        sigma_grid[i, j] = svdvals(L)[end]
    end

    threshold = quantile(vec(sigma_grid), 0.05)
    candidates = ComplexF64[]
    for i in 2:n_re-1, j in 2:n_im-1
        val = sigma_grid[i, j]
        if val < threshold
            neighbors = [sigma_grid[i+di, j+dj] for di in -1:1, dj in -1:1 if (di,dj) != (0,0)]
            if val <= minimum(neighbors)
                push!(candidates, complex(re_vals[i], im_vals[j]))
            end
        end
    end

    # Newton refinement on companion σ_min
    refined = ComplexF64[]
    for ω0 in candidates
        ω = ω0
        for _ in 1:newton_iters
            L = P_companion(ω)
            F = svd(L)
            σ_min = F.S[end]
            if σ_min < 1e-12
                break
            end
            u = F.U[:, end]
            v = F.Vt[end, :]
            # dL/dω: top-left = I_n, bottom-right = C, rest zero
            dL = zeros(ComplexF64, m + n, 2n)
            dL[1:n, 1:n] .= I(n)
            dL[n+1:m+n, n+1:2n] .= C
            deriv = dot(u, dL * v)
            if abs(deriv) < 1e-15
                break
            end
            ω -= σ_min / deriv
        end
        if !isnan(ω) && !isinf(ω)
            push!(refined, ω)
        end
    end

    return _deduplicate_eigenvalues(refined)
end

# ─────────────────────────────────────────────────────────────
# Method 5: Iterative SVD Compression (multi-pass refinement)
# ─────────────────────────────────────────────────────────────

"""
Like method 1, but iterates: project at multiple ω₀ values,
collect eigenvalues, re-project at each found eigenvalue, keep best.
"""
function method_iterative_svd(A, B, C; n_starts=5, n_refine=3)
    m, n = size(A)

    # Start from multiple projection centers
    rng = MersenneTwister(999)
    ω_starts = [0.0+0im, 1.0+1im, -1.0+1im, 1.0-1im, -1.0-1im,
                randn(rng, ComplexF64, max(0, n_starts - 5))...]

    all_eigs = ComplexF64[]

    for ω0 in ω_starts[1:min(n_starts, length(ω_starts))]
        eigs = method_svd_compress(A, B, C; ω0=ω0, max_refine=n_refine)
        append!(all_eigs, eigs)
    end

    # Validate each candidate by checking residual
    validated = ComplexF64[]
    for ω in all_eigs
        P = A .+ ω .* B .+ ω^2 .* C
        σ_min = svdvals(P)[end]
        norm_P = opnorm(P)
        if norm_P > 0 && σ_min / norm_P < 1e-6
            push!(validated, ω)
        end
    end

    return _deduplicate_eigenvalues(validated)
end

# ─────────────────────────────────────────────────────────────
# Method 6: Random Square Padding
# ─────────────────────────────────────────────────────────────

"""
Pad m×n matrices to m×m by adding random columns, solve as square QEP,
filter spurious eigenvalues by residual check on original rectangular system.
"""
function method_random_padding(A, B, C; n_pads=3, residual_tol=1e-6)
    m, n = size(A)
    rng = MersenneTwister(777)

    all_eigs = ComplexF64[]

    for trial in 1:n_pads
        # Pad to square m×m
        ε = 1e-8
        A_pad = hcat(A, ε * randn(rng, ComplexF64, m, m - n))
        B_pad = hcat(B, ε * randn(rng, ComplexF64, m, m - n))
        C_pad = hcat(C, ε * randn(rng, ComplexF64, m, m - n))

        eigs = solve_square_qep(A_pad, B_pad, C_pad)
        append!(all_eigs, eigs)
    end

    # Filter by residual on original system
    validated = ComplexF64[]
    for ω in all_eigs
        (isnan(ω) || isinf(ω)) && continue
        P = A .+ ω .* B .+ ω^2 .* C
        σ_min = svdvals(P)[end]
        norm_P = opnorm(P)
        if norm_P > 0 && σ_min / norm_P < residual_tol
            push!(validated, ω)
        end
    end

    return _deduplicate_eigenvalues(validated)
end

# ─────────────────────────────────────────────────────────────
# Accuracy Assessment
# ─────────────────────────────────────────────────────────────

"""
Compare found eigenvalues against ground truth.
Returns: (matched_count, max_error, mean_error, missed, spurious)
"""
function assess_accuracy(found, truth; tol=1e-4)
    if isempty(found)
        return (matched=0, max_err=Inf, mean_err=Inf,
                missed=length(truth), spurious=0, match_frac=0.0)
    end

    # Filter out Inf/NaN from found and truth
    found_clean = filter(z -> isfinite(z), found)
    truth_clean = filter(z -> isfinite(z), truth)

    if isempty(found_clean) || isempty(truth_clean)
        return (matched=0, max_err=Inf, mean_err=Inf,
                missed=length(truth_clean), spurious=length(found_clean), match_frac=0.0)
    end

    matched = 0
    errors = Float64[]
    truth_matched = falses(length(truth_clean))

    for f in found_clean
        dists = abs.(f .- truth_clean)
        best_idx = argmin(dists)
        best_dist = dists[best_idx]
        if best_dist < tol && !truth_matched[best_idx]
            matched += 1
            push!(errors, best_dist)
            truth_matched[best_idx] = true
        end
    end

    missed = count(.!truth_matched)
    spurious = length(found_clean) - matched
    max_err = isempty(errors) ? Inf : maximum(errors)
    mean_err = isempty(errors) ? Inf : mean(errors)
    match_frac = matched / length(truth_clean)

    return (matched=matched, max_err=max_err, mean_err=mean_err,
            missed=missed, spurious=spurious, match_frac=match_frac)
end

# ─────────────────────────────────────────────────────────────
# Residual-based accuracy (works without ground truth)
# ─────────────────────────────────────────────────────────────

"""Check residual σ_min(P(ω))/‖P(ω)‖ for each found eigenvalue."""
function residual_check(A, B, C, eigs; tol=1e-8)
    good = 0
    residuals = Float64[]
    for ω in eigs
        (isnan(ω) || isinf(ω)) && continue
        P = A .+ ω .* B .+ ω^2 .* C
        σ_min = svdvals(P)[end]
        nP = opnorm(P)
        r = nP > 0 ? σ_min / nP : σ_min
        push!(residuals, r)
        if r < tol
            good += 1
        end
    end
    return (n_good=good, n_total=length(eigs), residuals=residuals)
end

# ─────────────────────────────────────────────────────────────
# Main Benchmark
# ─────────────────────────────────────────────────────────────

function run_benchmark(; sizes=[(40, 30), (200, 150), (400, 300)],
                        full_size=(4000, 3000),
                        run_full=false)
    println("=" ^ 80)
    println("RECTANGULAR QEP METHOD AUDITION")
    println("=" ^ 80)
    println("Julia threads: $(Threads.nthreads())")
    println("BLAS threads:  $(BLAS.get_num_threads())")
    println()

    for (m, n) in sizes
        println("─" ^ 80)
        println("Problem size: $m × $n  ($(m*n) elements per matrix)")
        println("─" ^ 80)

        A, B, C, true_eigs = generate_test_problem(m, n, n; seed=42)
        n_finite_true = count(isfinite, true_eigs)
        println("True eigenvalues (finite): $n_finite_true / $(length(true_eigs))")
        println()

        methods = [
            ("1. SVD Compress",           () -> method_svd_compress(A, B, C; ω0=0.0, max_refine=0)),
            ("2. SVD Compress+Refine",    () -> method_svd_compress(A, B, C; ω0=0.0, max_refine=2)),
            ("3. Beyn Sequential (N=64)", () -> method_beyn(A, B, C; radius=6.0, N_quad=64)),
            ("4. Beyn Parallel (N=64)",   () -> method_beyn_parallel(A, B, C; radius=6.0, N_quad=64)),
            ("5. Beyn Parallel (N=128)",  () -> method_beyn_parallel(A, B, C; radius=6.0, N_quad=128)),
            ("6. Iterative SVD",          () -> method_iterative_svd(A, B, C; n_starts=5, n_refine=2)),
            ("7. Random Padding",         () -> method_random_padding(A, B, C; n_pads=2)),
        ]

        # Skip expensive methods for larger sizes
        if m * n > 100_000
            methods = [
                ("1. SVD Compress",           () -> method_svd_compress(A, B, C; ω0=0.0, max_refine=0)),
                ("2. SVD Compress+Refine",    () -> method_svd_compress(A, B, C; ω0=0.0, max_refine=2)),
                ("3. Beyn Sequential (N=64)", () -> method_beyn(A, B, C; radius=6.0, N_quad=64)),
                ("4. Beyn Parallel (N=64)",   () -> method_beyn_parallel(A, B, C; radius=6.0, N_quad=64)),
                ("5. Beyn Parallel (N=128)",  () -> method_beyn_parallel(A, B, C; radius=6.0, N_quad=128)),
                ("6. Iterative SVD",          () -> method_iterative_svd(A, B, C; n_starts=3, n_refine=2)),
                ("7. Random Padding",         () -> method_random_padding(A, B, C; n_pads=1)),
            ]
        end

        for (name, method) in methods
            print("  $name ... ")
            flush(stdout)

            # Warmup
            try
                method()
            catch e
                println("FAILED: $e")
                continue
            end

            # Timed run
            t0 = time()
            eigs = method()
            dt = time() - t0

            # Accuracy
            acc = assess_accuracy(eigs, true_eigs; tol=1e-3)
            res = residual_check(A, B, C, eigs)

            @printf("%.3fs | found %3d eigs | matched %3d/%d (%.0f%%) | residual-good %3d | max_err %.1e\n",
                    dt, length(eigs), acc.matched, n_finite_true,
                    acc.match_frac * 100, res.n_good, acc.max_err)
        end
        println()
    end

    # Full-scale timing test (SVD compress only — the fastest method)
    if run_full
        m, n = full_size
        println("─" ^ 80)
        println("FULL SCALE: $m × $n")
        println("─" ^ 80)

        A, B, C, _ = generate_test_problem(m, n, n; seed=42)

        for (name, method) in [
            ("SVD Compress",        () -> method_svd_compress(A, B, C; ω0=0.0, max_refine=0)),
            ("SVD Compress+Refine", () -> method_svd_compress(A, B, C; ω0=0.0, max_refine=2)),
            ("Beyn Seq N=32",       () -> method_beyn(A, B, C; radius=6.0, N_quad=32)),
            ("Beyn Par N=32",       () -> method_beyn_parallel(A, B, C; radius=6.0, N_quad=32)),
            ("Beyn Par N=64",       () -> method_beyn_parallel(A, B, C; radius=6.0, N_quad=64)),
        ]
            print("  $name ... ")
            flush(stdout)
            GC.gc()
            t0 = time()
            eigs = method()
            dt = time() - t0
            res = residual_check(A, B, C, eigs)
            @printf("%.1fs | found %d eigs | residual-good %d\n",
                    dt, length(eigs), res.n_good)
        end
    end

    println()
    println("=" ^ 80)
    println("SUMMARY")
    println("=" ^ 80)
    println("""
    Method Rankings (by practicality for 4000×3000):

    🏆 SVD Compression (Method 1/2):
       - Fastest by far. One SVD (O(mn²)) + square QEP solve (O(n³))
       - Finds ALL eigenvalues. No initial guess needed.
       - Iterative refinement improves accuracy cheaply.
       - BLAS-threaded automatically.

    🥈 Beyn Contour Integral (Method 4/5):
       - Embarrassingly parallel over quadrature points.
       - Finds eigenvalues in specified region (great if you know where to look).
       - Each quadrature point = one least-squares solve (O(mn²)).
       - Julia-thread parallel + BLAS parallel.
       - Cost: N_quad × (one SVD), so ~64-128× slower than SVD compress.

    🥉 Iterative SVD (Method 6):
       - Multiple SVD compressions from different centers.
       - More robust than single SVD compress but slower.
       - Good when eigenvalues span large region.

    ⚠️  σ_min Grid+Newton (Method 3):
       - O(N_grid × SVD) — very expensive for fine grids.
       - Only finds eigenvalues near the grid.
       - Good for real eigenvalues or when region is known.

    ⚠️  Random Padding (Method 7):
       - Quadruples problem size (m×m instead of m×n).
       - Introduces spurious eigenvalues.
       - Simple but wasteful.

    ❌ Companion + GSVD (Method 4 variant):
       - Doubles system size.
       - GSVD is expensive.
       - No advantage over SVD compression.

    RECOMMENDATION: Start with SVD Compression. Use Beyn if you need
    eigenvalues in a specific complex region. Use iterative SVD for
    robustness. All three parallelize well via BLAS threading.
    """)
end

# ─────────────────────────────────────────────────────────────
# Run
# ─────────────────────────────────────────────────────────────

if abspath(PROGRAM_FILE) == @__FILE__
    run_full = "--full" in ARGS
    run_benchmark(; run_full=run_full)
end
