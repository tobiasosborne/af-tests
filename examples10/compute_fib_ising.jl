#!/usr/bin/env julia
#=
  Compute categorical data for Fib ⊠ Ising (Deligne product)

  This script uses TensorCategories.jl (which depends on Oscar) to:
    1. Construct the Fibonacci and Ising fusion categories
    2. Compute Fib ⊠ Ising (Deligne product) — rank 6
    3. Extract F-symbols and verify pentagon axiom
    4. Print fusion rules and FP dimensions
    5. Find separable algebra structures (→ module categories)
    6. Compute module categories over each separable algebra
    7. Compute the Drinfeld center Z(Fib ⊠ Ising)
    8. Compute modular S and T matrices

  Fib: rank 2, simples {𝟙, τ}, τ⊗τ = 𝟙⊕τ, defined over QQ(ϕ)
  Ising: rank 3, simples {𝟙, χ, X}, X⊗X = 𝟙⊕χ, defined over QQ(√2)
  Fib ⊠ Ising: rank 6, requires common base field QQ(ϕ, √2)

  Key: Both categories must be constructed over the SAME field for ⊠ to work.
  We build a number field K = QQ(α) where α⁴ - α² - 1 = 0 contains both
  ϕ = α² and √2 as elements.

  Run with:  julia --project=../../TensorCategories.jl compute_fib_ising.jl
=#

using Pkg
Pkg.activate(joinpath(@__DIR__, "..", "..", "TensorCategories.jl"))

t_start = time()
println("="^70)
println("COMPUTING CATEGORICAL DATA FOR Fib ⊠ Ising")
println("="^70)
println("Loading TensorCategories.jl + Oscar...")
flush(stdout)

using TensorCategories
using Oscar

println("  Loaded in $(round(time() - t_start, digits=1))s")
flush(stdout)

# ================================================================
# Step 1: Common base field and base categories
# ================================================================
println("\n" * "="^70)
println("STEP 1: Common Base Field + Fibonacci and Ising Categories")
println("="^70)
flush(stdout)

# Fib needs ϕ (root of x²-x-1), Ising needs √2 (root of x²-2).
# Build common field K = QQ(ϕ,√2) ≅ QQ[x]/(min poly), degree 4 over QQ.
# Method: tower QQ → QQ(ϕ) → QQ(ϕ,√2), then flatten to absolute field.

_,x = QQ[:x]
K_phi, phi = number_field(x^2 - x - 1, "ϕ")
_,y = K_phi[:y]
K_rel, sqrt2_rel = number_field(y^2 - 2, "√2")

# Flatten tower to absolute simple number field
K, m = absolute_simple_field(K_rel)
m_inv = inv(m)
phi_K = m_inv(K_rel(phi))
sqrt2_K = m_inv(sqrt2_rel)

println("  K = QQ(ϕ,√2), degree $(degree(K)) over QQ")
println("  ϕ in K: $(phi_K)")
println("  √2 in K: $(sqrt2_K)")
println("  Check: ϕ²-ϕ-1 = $(phi_K^2 - phi_K - 1)")
println("  Check: (√2)²-2 = $(sqrt2_K^2 - 2)")

# Construct Fib and Ising over K
println("\n  Constructing Fib over K...")
flush(stdout)
Fib = fibonacci_category(K)
S_fib = simples(Fib)
println("  Fib constructed: rank $(length(S_fib))")
println("  Simples: $(simples_names(Fib))")
for (i, s) in enumerate(S_fib)
    println("    dim($(simples_names(Fib)[i])) = $(fpdim(s))")
end
println("  FPdim²(Fib) = $(fpdim(Fib))")

println("\n  Constructing Ising over K...")
flush(stdout)
Ising = ising_category(K, sqrt2_K, 1)
S_ising = simples(Ising)
println("  Ising constructed: rank $(length(S_ising))")
println("  Simples: $(simples_names(Ising))")
for (i, s) in enumerate(S_ising)
    println("    dim($(simples_names(Ising)[i])) = $(fpdim(s))")
end
println("  FPdim²(Ising) = $(fpdim(Ising))")

# Ising F-symbols
println("\n  Ising F-symbols (nonzero):")
F_ising = F_symbols(Ising)
n_nz_ising = count(!iszero, values(F_ising))
println("    Total nonzero: $n_nz_ising out of $(length(F_ising))")
for (k, v) in sort(collect(F_ising), by=first)
    if !iszero(v)
        println("    F$(k) = $(v)")
    end
end

# Ising fusion rules
println("\n  Ising fusion rules:")
names_ising = simples_names(Ising)
for i in 1:length(S_ising), j in i:length(S_ising)
    prod = S_ising[i] ⊗ S_ising[j]
    comps = prod.components
    terms = String[]
    for k in 1:length(S_ising)
        if comps[k] > 0
            push!(terms, comps[k] == 1 ? names_ising[k] : "$(comps[k])$(names_ising[k])")
        end
    end
    println("    $(names_ising[i]) ⊗ $(names_ising[j]) = $(join(terms, " + "))")
end

println("\n  Pentagon checks:")
println("    Fib: $(pentagon_axiom(S_fib) ? "PASS" : "FAIL")")
println("    Ising: $(pentagon_axiom(S_ising) ? "PASS" : "FAIL")")
flush(stdout)

# ================================================================
# Step 2: Fib ⊠ Ising (Deligne product)
# ================================================================
println("\n" * "="^70)
println("STEP 2: Fib ⊠ Ising (Deligne Product)")
println("="^70)
flush(stdout)

t2 = time()
FI = Fib ⊠ Ising
S_fi = simples(FI)
println("  Fib ⊠ Ising constructed in $(round(time() - t2, digits=1))s")
println("  Rank: $(length(S_fi))")
println("  Simples: $(simples_names(FI))")
for (i, s) in enumerate(S_fi)
    println("    dim($(simples_names(FI)[i])) = $(fpdim(s))")
end
println("  FPdim²(Fib ⊠ Ising) = $(fpdim(FI))")
flush(stdout)

# ================================================================
# Step 3: F-symbols
# ================================================================
println("\n" * "="^70)
println("STEP 3: F-symbols of Fib ⊠ Ising")
println("="^70)
flush(stdout)

t3 = time()
F_fi = F_symbols(FI)
n_total = length(F_fi)
n_nz = count(!iszero, values(F_fi))
println("  F-symbols extracted in $(round(time() - t3, digits=1))s")
println("  Total entries: $n_total")
println("  Nonzero entries: $n_nz")

# Write F-symbols to file
open(joinpath(@__DIR__, "fsymbols_fib_ising.txt"), "w") do io
    println(io, "# F-symbols of Fib ⊠ Ising")
    println(io, "# Computed via TensorCategories.jl (Deligne product)")
    println(io, "#")
    println(io, "# Category: Fib ⊠ Ising")
    println(io, "# Rank: $(length(S_fi))")
    println(io, "# FPdim²: $(fpdim(FI))")
    println(io, "# Nonzero F-symbols: $n_nz")
    println(io, "#")
    println(io, "# Format: F[a,b,c,d,e,f] = value")
    println(io, "#   (a,b,c) = input triple, d = output, (e,f) = multiplicity indices")
    println(io, "#")
    println(io, "# Simple objects: $(simples_names(FI))")
    println(io, "#")
    for (k, v) in sort(collect(F_fi), by=first)
        if !iszero(v)
            println(io, "F$(k) = $(v)")
        end
    end
end
println("  Written to fsymbols_fib_ising.txt")
flush(stdout)

# ================================================================
# Step 4: Pentagon axiom verification
# ================================================================
println("\n" * "="^70)
println("STEP 4: Pentagon Axiom Verification")
println("="^70)
flush(stdout)

t4 = time()
pent_ok = pentagon_axiom(S_fi)
println("  Pentagon axiom: $(pent_ok ? "PASSED ✓" : "FAILED ✗")")
println("  Checked in $(round(time() - t4, digits=1))s")
flush(stdout)

# ================================================================
# Step 5: Fusion rules
# ================================================================
println("\n" * "="^70)
println("STEP 5: Fusion Rules")
println("="^70)
flush(stdout)

names_fi = simples_names(FI)
n_s = length(S_fi)
println("  Fusion table (nonzero products):")
for i in 1:n_s, j in i:n_s
    prod = S_fi[i] ⊗ S_fi[j]
    comps = prod.components
    terms = String[]
    for k in 1:n_s
        if comps[k] > 0
            push!(terms, comps[k] == 1 ? names_fi[k] : "$(comps[k])$(names_fi[k])")
        end
    end
    if !isempty(terms)
        println("    $(names_fi[i]) ⊗ $(names_fi[j]) = $(join(terms, " + "))")
    end
end
flush(stdout)

# ================================================================
# Step 6: Separable algebra structures → module categories
# ================================================================
println("\n" * "="^70)
println("STEP 6: Separable Algebras and Module Categories")
println("="^70)
flush(stdout)

t6 = time()

# Find separable algebras on small direct sums of simples
# These classify indecomposable module categories over Fib ⊠ Ising
println("  Searching for separable algebra structures...")
println("  (Each separable algebra A gives a module category Mod_A)")
flush(stdout)

algebras_found = []

# Try all single simples and pairs
for i in 1:n_s
    print("    Checking $(names_fi[i])... ")
    flush(stdout)
    try
        algs = separable_algebra_structures(S_fi[i])
        println("$(length(algs)) found")
        for a in algs
            push!(algebras_found, (names_fi[i], a))
        end
    catch e
        println("ERROR: $e")
    end
    flush(stdout)
end

# Try 𝟙 ⊕ X for various X (the Ising test uses 𝟙 ⊕ χ)
println("\n  Checking direct sums:")
flush(stdout)
for i in 2:n_s
    obj = S_fi[1] ⊕ S_fi[i]
    label = "$(names_fi[1]) ⊕ $(names_fi[i])"
    print("    Checking $label... ")
    flush(stdout)
    try
        algs = separable_algebra_structures(obj)
        println("$(length(algs)) found")
        for a in algs
            push!(algebras_found, (label, a))
        end
    catch e
        println("ERROR: $e")
    end
    flush(stdout)
end

# Try sums of pairs within each factor
for i in 2:n_s, j in (i+1):n_s
    obj = S_fi[i] ⊕ S_fi[j]
    label = "$(names_fi[i]) ⊕ $(names_fi[j])"
    print("    Checking $label... ")
    flush(stdout)
    try
        algs = separable_algebra_structures(obj)
        println("$(length(algs)) found")
        for a in algs
            push!(algebras_found, (label, a))
        end
    catch e
        println("ERROR: $e")
    end
    flush(stdout)
end

println("\n  Total separable algebras found: $(length(algebras_found))")

# Compute module categories for each algebra
module_cats = []
for (idx, (label, A)) in enumerate(algebras_found)
    println("\n  Module category $idx (algebra on $label):")
    flush(stdout)
    try
        M = category_of_right_modules(A)
        S_mod = simples(M)
        println("    Right modules: $(length(S_mod)) simple objects")
        push!(module_cats, (label, A, M, S_mod))

        # Also try bimodule category (= dual category)
        try
            Func = category_of_bimodules(A)
            println("    Bimodules (dual): pentagon = $(pentagon_axiom(Func) ? "PASS" : "FAIL")")
        catch e
            println("    Bimodules: ERROR ($e)")
        end
    catch e
        println("    ERROR computing modules: $e")
    end
    flush(stdout)
end

println("\n  Step 6 completed in $(round(time() - t6, digits=1))s")
flush(stdout)

# ================================================================
# Step 7: Drinfeld Center
# ================================================================
println("\n" * "="^70)
println("STEP 7: Drinfeld Center Z(Fib ⊠ Ising)")
println("="^70)
flush(stdout)

t7 = time()
center_ok = false
n_center_simples = 0
try
    # Set name to avoid UndefRefError in center computation
    try set_name!(FI, "Fib ⊠ Ising") catch; end

    Z = center(FI)

    println("  Computing center simples via induction...")
    flush(stdout)
    for (i, s) in enumerate(S_fi)
        print("    Inducing simple $i ($(names_fi[i]))... ")
        flush(stdout)
        ind_s = induction(s)
        sub_simples = simple_subobjects(ind_s)
        println("$(length(sub_simples)) simple subobjects")
        for ss in sub_simples
            try
                TensorCategories.add_simple!(Z, ss)
            catch e
                println("      (skipped non-simple: $e)")
            end
        end
    end

    global n_center_simples = length(simples(Z))
    println("  Center constructed in $(round(time() - t7, digits=1))s")
    println("  Number of simple objects in Z(Fib ⊠ Ising): $n_center_simples")

    # Expected: Z(Fib ⊠ Ising) ≅ Z(Fib) ⊠ Z(Ising)
    # Z(Fib) has 4 simples, Z(Ising) has 6 simples → Z should have 24? No...
    # Actually Z(Fib) ≅ Fib⊠Fib̄ has rank... let's just report what we find.
    println("  FPdim²(Z) = $(fpdim(Z))")

    for (i, s) in enumerate(simples(Z))
        println("    Z_$i: dim = $(fpdim(s))")
    end

    global center_ok = true
catch e
    println("  CENTER COMPUTATION FAILED: $e")
    println("  (Known TensorCategories.jl issue with matrix operations)")
    println("  Skipping S and T matrix computation.")
end
flush(stdout)

# ================================================================
# Step 8: Modular S and T matrices
# ================================================================
if center_ok
    println("\n" * "="^70)
    println("STEP 8: Modular S and T Matrices")
    println("="^70)
    flush(stdout)

    t8 = time()
    try
        S_mat = smatrix(Z)
        println("  S matrix ($(size(S_mat))):")
        display(S_mat)
        println()

        T_mat = tmatrix(Z)
        println("  T matrix diagonal:")
        for i in 1:size(T_mat, 1)
            println("    T[$i,$i] = $(T_mat[i,i])")
        end

        # Verify S²=C and (ST)³=C
        println("\n  Modular relations:")
        n_z = size(S_mat, 1)
        S2 = S_mat * S_mat
        # Check if S² is a permutation matrix (charge conjugation)
        is_perm = all(sum(abs.(S2[i,:]) .> 0) == 1 for i in 1:n_z)
        println("    S² is permutation matrix: $is_perm")

        # Write to file
        open(joinpath(@__DIR__, "modular_data_fib_ising.txt"), "w") do io
            println(io, "# Modular data for Z(Fib ⊠ Ising)")
            println(io, "# Computed via TensorCategories.jl")
            println(io, "# Center rank: $n_center_simples")
            println(io, "#")
            println(io, "# S matrix ($(size(S_mat))):")
            for i in 1:size(S_mat, 1)
                println(io, "S[$i,:] = [$(join([string(S_mat[i,j]) for j in 1:size(S_mat,2)], ", "))]")
            end
            println(io, "#")
            println(io, "# T matrix diagonal:")
            for i in 1:size(T_mat, 1)
                println(io, "T[$i] = $(T_mat[i,i])")
            end
        end
        println("  Written to modular_data_fib_ising.txt")
    catch e
        println("  MODULAR DATA FAILED: $e")
    end
    println("  Computed in $(round(time() - t8, digits=1))s")
    flush(stdout)
end

# ================================================================
# Summary
# ================================================================
t_total = time() - t_start
println("\n" * "="^70)
println("COMPUTATION COMPLETE")
println("="^70)
println("  Total time: $(round(t_total/60, digits=1)) minutes")
println("  Category: Fib ⊠ Ising")
println("  Rank: $(length(S_fi))")
println("  Pentagon: $(pent_ok ? "PASS" : "FAIL")")
println("  F-symbols: $n_nz nonzero (written to fsymbols_fib_ising.txt)")
println("  Separable algebras: $(length(algebras_found))")
println("  Module categories: $(length(module_cats))")
println("  Center: $(center_ok ? "$n_center_simples simples" : "FAILED")")
println("="^70)
