#!/usr/bin/env julia
#=
  Compute module categories over Fib ⊠ Ising.

  Module categories over a fusion category C are classified by separable
  (= connected étale = condensable) algebra objects A in C. Each such A
  gives:
    - Right module category Mod_A(C)
    - Bimodule category Bimod_A(C) (= the "dual" fusion category)

  For Fib ⊠ Ising, previous run found 3 algebras on ≤2-simple sums.
  This script also searches 3-fold sums.

  Expected module categories:
    - Trivial: A = 𝟙⊠𝟙 (always exists)
    - Ising condensation: A = 𝟙⊠𝟙 ⊕ 𝟙⊠χ (Z₂ algebra from Ising)
    - Fib condensation: A = 𝟙⊠𝟙 ⊕ τ⊠𝟙 (the Fibonacci algebra)
    - Mixed: A = 𝟙⊠𝟙 ⊕ 𝟙⊠χ ⊕ τ⊠𝟙 ⊕ τ⊠χ (?) — needs unit check

  Run with:  julia --threads=1 --project=../../TensorCategories.jl compute_fib_ising_modules.jl
=#

using Pkg
Pkg.activate(joinpath(@__DIR__, "..", "..", "TensorCategories.jl"))

t_start = time()
println("="^70)
println("MODULE CATEGORIES OVER Fib ⊠ Ising")
println("="^70)
println("Loading TensorCategories.jl + Oscar...")
flush(stdout)

using TensorCategories
using Oscar

println("  Loaded in $(round(time() - t_start, digits=1))s")
flush(stdout)

# ================================================================
# Step 1: Build Fib ⊠ Ising
# ================================================================
println("\n" * "="^70)
println("STEP 1: Build Fib ⊠ Ising")
println("="^70)
flush(stdout)

_,x = QQ[:x]
K_phi, phi = number_field(x^2 - x - 1, "ϕ")
_,y = K_phi[:y]
K_rel, sqrt2_rel = number_field(y^2 - 2, "√2")
K, m = absolute_simple_field(K_rel)
m_inv = inv(m)
phi_K = m_inv(K_rel(phi))
sqrt2_K = m_inv(sqrt2_rel)

Fib = fibonacci_category(K)
Ising = ising_category(K, sqrt2_K, 1)
FI = Fib ⊠ Ising
try set_name!(FI, "Fib ⊠ Ising") catch; end

S = simples(FI)
names = simples_names(FI)
n = length(S)
println("  Rank: $n")
println("  Simples: $names")
println("  FPdim²: $(fpdim(FI))")
flush(stdout)

# ================================================================
# Step 2: Find all separable algebra structures
# ================================================================
println("\n" * "="^70)
println("STEP 2: Find Separable Algebra Structures")
println("="^70)
flush(stdout)

algebras_found = Tuple{String, Any}[]

# --- Single simples ---
println("  Single simples:")
flush(stdout)
for i in 1:n
    print("    $(names[i])... ")
    flush(stdout)
    try
        algs = separable_algebra_structures(S[i])
        println("$(length(algs)) algebra(s)")
        for a in algs
            push!(algebras_found, (names[i], a))
        end
    catch e
        println("ERROR: $(sprint(showerror, e))")
    end
    flush(stdout)
end

# --- Pairs containing 𝟙⊠𝟙 (needed for unit morphism) ---
println("\n  Pairs with 𝟙⊠𝟙:")
flush(stdout)
for i in 2:n
    obj = S[1] ⊕ S[i]
    label = "$(names[1]) ⊕ $(names[i])"
    print("    $label... ")
    flush(stdout)
    try
        algs = separable_algebra_structures(obj)
        println("$(length(algs)) algebra(s)")
        for a in algs
            push!(algebras_found, (label, a))
        end
    catch e
        println("ERROR: $(sprint(showerror, e))")
    end
    flush(stdout)
end

# --- Other pairs (without 𝟙⊠𝟙 — need explicit unit) ---
println("\n  Other pairs:")
flush(stdout)
for i in 2:n, j in (i+1):n
    obj = S[i] ⊕ S[j]
    label = "$(names[i]) ⊕ $(names[j])"
    print("    $label... ")
    flush(stdout)
    try
        # These may crash (BoundsError) if 𝟙 is not a summand
        algs = separable_algebra_structures(obj)
        println("$(length(algs)) algebra(s)")
        for a in algs
            push!(algebras_found, (label, a))
        end
    catch e
        println("ERROR (expected if no unit): $(sprint(showerror, e))")
    end
    flush(stdout)
end

# --- Triple sums containing 𝟙⊠𝟙 ---
println("\n  Triples with 𝟙⊠𝟙:")
flush(stdout)
for i in 2:n, j in (i+1):n
    obj = S[1] ⊕ S[i] ⊕ S[j]
    label = "$(names[1]) ⊕ $(names[i]) ⊕ $(names[j])"
    print("    $label... ")
    flush(stdout)
    try
        algs = separable_algebra_structures(obj)
        println("$(length(algs)) algebra(s)")
        for a in algs
            push!(algebras_found, (label, a))
        end
    catch e
        println("ERROR: $(sprint(showerror, e))")
    end
    flush(stdout)
end

# --- Quadruple sums containing 𝟙⊠𝟙 (selective) ---
println("\n  Selected quadruples with 𝟙⊠𝟙:")
flush(stdout)
# The most promising: 𝟙⊠𝟙 ⊕ 𝟙⊠χ ⊕ τ⊠𝟙 ⊕ τ⊠χ
for i in 2:n, j in (i+1):n, k in (j+1):n
    obj = S[1] ⊕ S[i] ⊕ S[j] ⊕ S[k]
    label = "$(names[1]) ⊕ $(names[i]) ⊕ $(names[j]) ⊕ $(names[k])"
    print("    $label... ")
    flush(stdout)
    try
        algs = separable_algebra_structures(obj)
        println("$(length(algs)) algebra(s)")
        for a in algs
            push!(algebras_found, (label, a))
        end
    catch e
        println("ERROR: $(sprint(showerror, e))")
    end
    flush(stdout)
end

println("\n  ════════════════════════════════════════════")
println("  Total separable algebras found: $(length(algebras_found))")
println("  ════════════════════════════════════════════")
flush(stdout)

# ================================================================
# Step 3: Compute module categories for each algebra
# ================================================================
println("\n" * "="^70)
println("STEP 3: Module Categories")
println("="^70)
flush(stdout)

results = []

for (idx, (label, A)) in enumerate(algebras_found)
    println("\n  ─── Module category $idx: algebra on $label ───")
    flush(stdout)

    # Right modules
    println("    Computing right modules...")
    flush(stdout)
    t_mod = time()
    try
        M = category_of_right_modules(A)
        S_mod = simples(M)
        n_mod = length(S_mod)
        println("    Right module category: $n_mod simple objects")
        for (j, sm) in enumerate(S_mod)
            println("      M_$j: $(sm)")
        end

        # Bimodule category (= dual fusion category)
        println("    Computing bimodule category (dual)...")
        flush(stdout)
        try
            Func = category_of_bimodules(A)
            S_bim = simples(Func)
            n_bim = length(S_bim)
            println("    Bimodule category: $n_bim simple objects")
            for (j, sb) in enumerate(S_bim)
                println("      B_$j: $(sb)")
            end

            # Pentagon check for bimodule category
            println("    Pentagon check for bimodules...")
            flush(stdout)
            pent = pentagon_axiom(Func)
            println("    Pentagon: $(pent ? "PASS ✓" : "FAIL ✗")")

            # FP dimensions
            println("    FPdim²(Bimod): $(fpdim(Func))")

            push!(results, (label=label, n_right=n_mod, n_bimod=n_bim, pentagon=pent,
                            fpdim2=fpdim(Func), time=round(time()-t_mod, digits=1)))
        catch e
            println("    Bimodule ERROR: $(sprint(showerror, e))")
            push!(results, (label=label, n_right=n_mod, n_bimod=-1, pentagon=false,
                            fpdim2=nothing, time=round(time()-t_mod, digits=1)))
        end
    catch e
        println("    Right module ERROR: $(sprint(showerror, e))")
        push!(results, (label=label, n_right=-1, n_bimod=-1, pentagon=false,
                        fpdim2=nothing, time=round(time()-t_mod, digits=1)))
    end
    flush(stdout)
end

# ================================================================
# Summary
# ================================================================
t_total = time() - t_start
println("\n" * "="^70)
println("SUMMARY — Module Categories over Fib ⊠ Ising")
println("="^70)
println()

println("  $(length(algebras_found)) separable algebras found")
println()
println("  | # | Algebra on | Right mods | Bimodules | Pentagon | FPdim² | Time |")
println("  |---|-----------|-----------|----------|---------|--------|------|")
for (idx, r) in enumerate(results)
    pstr = r.pentagon ? "PASS" : (r.n_bimod < 0 ? "ERR" : "FAIL")
    bstr = r.n_bimod < 0 ? "ERR" : string(r.n_bimod)
    rstr = r.n_right < 0 ? "ERR" : string(r.n_right)
    fstr = r.fpdim2 === nothing ? "—" : string(r.fpdim2)
    println("  | $idx | $(r.label) | $rstr | $bstr | $pstr | $fstr | $(r.time)s |")
end

println("\n  Total time: $(round(t_total/60, digits=1)) minutes")
println("="^70)

# Write results
outfile = joinpath(@__DIR__, "module_cats_fib_ising.txt")
open(outfile, "w") do io
    println(io, "# Module categories over Fib ⊠ Ising")
    println(io, "# Computed via TensorCategories.jl (corrected)")
    println(io, "#")
    println(io, "# Separable algebras found: $(length(algebras_found))")
    println(io, "#")
    for (idx, r) in enumerate(results)
        pstr = r.pentagon ? "PASS" : "FAIL"
        println(io, "Algebra $idx: $(r.label)")
        println(io, "  Right modules: $(r.n_right)")
        println(io, "  Bimodules: $(r.n_bimod)")
        println(io, "  Pentagon: $pstr")
        println(io, "  FPdim²: $(r.fpdim2)")
        println(io, "  Time: $(r.time)s")
        println(io, "")
    end
end
println("  Written to module_cats_fib_ising.txt")
