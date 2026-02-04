# Comparison driver: ED vs DMRG for BLM model

using Printf

# Compare ground state energies
function compare_ground_states(j_values=[1, 3, 5]; J_coupling=1.0, chi_max=100, nsweeps=10)
    println("\n" * "=" ^ 60)
    println("ED vs DMRG Ground State Comparison")
    println("=" ^ 60)
    println()
    @printf("  j    N    dim       E₀(ED)         E₀(DMRG)       ΔE           Status\n")
    println("-" ^ 75)

    results = []
    for j in j_values
        N = 2j + 1
        dim = 2^N

        # ED
        evals_ed = diag_full(j; J_coupling=J_coupling)
        E0_ed = minimum(evals_ed)

        # DMRG
        E0_dmrg, psi, sites, _ = run_dmrg(j; J_coupling=J_coupling, chi_max=chi_max,
                                          nsweeps=nsweeps, conserve_qns=false)
        delta_E = abs(E0_dmrg - E0_ed)

        # Determine status
        if delta_E < 1e-10
            status = "✓ PASS"
        elseif delta_E < 1e-6
            status = "~ OK"
        else
            status = "✗ FAIL"
        end

        @printf("%3d  %3d  %6d   %14.10f  %14.10f  %12.2e   %s\n",
                j, N, dim, E0_ed, E0_dmrg, delta_E, status)

        push!(results, (j=j, N=N, dim=dim, E0_ed=E0_ed, E0_dmrg=E0_dmrg, delta_E=delta_E))
    end

    println("-" ^ 75)
    return results
end

# Compare low-lying spectrum (using sector-resolved ED)
function compare_spectrum_structure(j; J_coupling=1.0)
    println("\n" * "=" ^ 60)
    println("Spectrum Structure (j=$j)")
    println("=" ^ 60)

    # ED spectrum by sector
    sector_evals = diag_by_sector(j; J_coupling=J_coupling)

    # Count states at each energy level
    all_evals = Float64[]
    for evals in values(sector_evals)
        append!(all_evals, evals)
    end
    sort!(all_evals)

    # Print unique energy levels with degeneracies
    println("\nUnique energy levels (degeneracy):")
    i = 1
    tol = 1e-10
    count = 0
    while i <= length(all_evals) && count < 15
        E = all_evals[i]
        deg = 1
        while i + deg <= length(all_evals) && abs(all_evals[i + deg] - E) < tol
            deg += 1
        end
        @printf("  E = %10.6f  (deg = %d)\n", E, deg)
        i += deg
        count += 1
    end
    if i <= length(all_evals)
        println("  ... $(length(all_evals) - i + 1) more levels")
    end

    # BPS summary
    bps_sectors = find_bps_sectors(sector_evals; tol=1e-10)
    total_bps = sum(x[3] for x in bps_sectors)
    println("\nBPS states (E=0): $total_bps total")
    println("BPS at R = -1/6 (n=$(Int(j))): $(sum(x[3] for x in bps_sectors if x[1]==j))")
    println("BPS at R = +1/6 (n=$(Int(j+1))): $(sum(x[3] for x in bps_sectors if x[1]==j+1))")
    println("Predicted: 2 × 3^$j = $(2 * 3^j)")
end

# Full validation for a single j value
function validate_j(j; J_coupling=1.0, chi_max=100, nsweeps=10, verbose=true)
    N = 2j + 1
    dim = 2^N

    if verbose
        println("\n" * "=" ^ 60)
        println("Full Validation: j=$j (N=$N, dim=$dim)")
        println("=" ^ 60)
    end

    results = Dict{String, Any}()

    # Build Hamiltonian
    H = build_hamiltonian(j; J_coupling=J_coupling)

    # Check 1: Hermitian
    results["Hermitian"] = norm(H - H') < 1e-12
    verbose && println("1. Hermitian: $(results["Hermitian"])")

    # Check 2: Positive semi-definite
    evals = eigvals(Hermitian(Matrix(H)))
    results["PSD"] = minimum(evals) > -1e-10
    verbose && println("2. H ≥ 0: $(results["PSD"]) (λ_min = $(minimum(evals)))")

    # Check 3: Vacuum energy
    E_vac_pred = J_coupling * N / 3
    E_vac_actual = H[1, 1]
    results["Vacuum"] = abs(E_vac_actual - E_vac_pred) < 1e-10
    verbose && println("3. Vacuum energy: $(results["Vacuum"]) (E_vac = $E_vac_actual, pred = $E_vac_pred)")

    # Check 4: ED ground state = 0 (BPS)
    E0_ed = minimum(evals)
    results["E0_BPS"] = abs(E0_ed) < 1e-10
    verbose && println("4. ED ground state BPS: $(results["E0_BPS"]) (E₀ = $E0_ed)")

    # Check 5: DMRG matches ED
    E0_dmrg, _, _, _ = run_dmrg(j; J_coupling=J_coupling, chi_max=chi_max,
                                 nsweeps=nsweeps, conserve_qns=false)
    delta_E = abs(E0_dmrg - E0_ed)
    results["DMRG_match"] = delta_E < 1e-6
    verbose && println("5. DMRG matches ED: $(results["DMRG_match"]) (ΔE = $delta_E)")

    # Check 6: MPO matches ED matrix (only for small j)
    if dim <= 256
        H_mpo, sites = build_blm_mpo(j; J_coupling=J_coupling, conserve_qns=false)
        H_itensor = mpo_to_matrix(H_mpo, sites)
        H_ed = Matrix(H)
        mpo_diff = norm(H_itensor - H_ed)
        results["MPO_match"] = mpo_diff < 1e-10
        verbose && println("6. MPO matches ED: $(results["MPO_match"]) (diff = $mpo_diff)")
    end

    # Summary
    all_pass = all(values(results))
    verbose && println("\nOverall: $(all_pass ? "✓ ALL PASS" : "✗ SOME FAILED")")

    return results, all_pass
end
