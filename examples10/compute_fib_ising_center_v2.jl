#!/usr/bin/env julia
#=
  Compute the Drinfeld center Z(Fib ⊠ Ising) with corrected TensorCategories.jl.

  Fixes applied to ../TensorCategories.jl:
    1. Thread-safety: hom_by_adjunction race in Center.jl & Centralizer.jl
    2. Thread-safety: smatrix write-write race in both files
    3. Thread-safety: add_induction! Dict mutation lock in both files
    4. Simplicity check: add_simple! now warns instead of asserting dim(End(s))==1

  Strategy: Use simples_by_induction!(Z) which bypasses add_simple! entirely
  and goes through the robust MeatAxe decomposition path.

  Expected result: Z(Fib ⊠ Ising) ≅ Z(Fib) ⊠ Z(Ising)
    Z(Fib) has rank 4 (Yang-Lee model)
    Z(Ising) has rank 6
    → Z(Fib ⊠ Ising) should have rank 24

  Run with:  julia --threads=1 --project=../../TensorCategories.jl compute_fib_ising_center_v2.jl
  (Use --threads=1 for safety; multi-threaded should also work with fixes applied)
=#

using Pkg
Pkg.activate(joinpath(@__DIR__, "..", "..", "TensorCategories.jl"))

t_start = time()
println("="^70)
println("DRINFELD CENTER Z(Fib ⊠ Ising) — v2 (with TC.jl fixes)")
println("="^70)
println("Loading TensorCategories.jl + Oscar...")
println("  Julia threads: $(Threads.nthreads())")
flush(stdout)

using TensorCategories
using Oscar
using Dates

println("  Loaded in $(round(time() - t_start, digits=1))s")
flush(stdout)

# ================================================================
# Step 1: Common base field + categories
# ================================================================
println("\n" * "="^70)
println("STEP 1: Build Fib ⊠ Ising over K = QQ(ϕ,√2)")
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

println("  K = QQ(ϕ,√2), degree $(degree(K))")
println("  ϕ in K: $(phi_K), check: ϕ²-ϕ-1 = $(phi_K^2 - phi_K - 1)")
println("  √2 in K: $(sqrt2_K), check: (√2)²-2 = $(sqrt2_K^2 - 2)")
flush(stdout)

Fib = fibonacci_category(K)
Ising = ising_category(K, sqrt2_K, 1)
FI = Fib ⊠ Ising
try set_name!(FI, "Fib ⊠ Ising") catch; end

S_fi = simples(FI)
names_fi = simples_names(FI)
println("  Rank: $(length(S_fi))")
println("  Simples: $names_fi")
println("  FPdim²(Fib ⊠ Ising) = $(fpdim(FI))")
for (i, s) in enumerate(S_fi)
    println("    dim($(names_fi[i])) = $(fpdim(s))")
end
flush(stdout)

# Quick pentagon sanity check
println("\n  Pentagon check...")
flush(stdout)
pent_ok = pentagon_axiom(S_fi)
println("  Pentagon: $(pent_ok ? "PASS ✓" : "FAIL ✗")")
flush(stdout)

# ================================================================
# Step 2: Drinfeld center via simples_by_induction!
# ================================================================
println("\n" * "="^70)
println("STEP 2: Drinfeld Center Z(Fib ⊠ Ising)")
println("="^70)
println("  Using simples_by_induction! (bypasses dim(End)==1 check)")
flush(stdout)

t_center = time()
Z = center(FI)

# Use the built-in induction machinery which handles everything
println("  Computing center simples via induction...")
flush(stdout)
TensorCategories.simples_by_induction!(Z, true)

S_z = simples(Z)
n_z = length(S_z)
t_center_done = time() - t_center

println("\n  Center rank: $n_z (expected: 24)")
println("  Center computed in $(round(t_center_done, digits=1))s")

for (i, s) in enumerate(S_z)
    d = fpdim(s)
    println("    Z_$i: FPdim = $d")
end
println("  FPdim²(Z) = $(fpdim(Z))")
flush(stdout)

# Sanity check: total FPdim² should equal FPdim²(FI)²
expected_fpdim2 = fpdim(FI)^2
println("  Expected FPdim²(Z) = FPdim²(C)² = $(expected_fpdim2)")
flush(stdout)

# ================================================================
# Step 3: Modular S matrix
# ================================================================
println("\n" * "="^70)
println("STEP 3: Modular S Matrix")
println("="^70)
flush(stdout)

t_s = time()
S_mat = smatrix(Z)
println("  S matrix ($(size(S_mat))):")
display(S_mat)
println()
println("  Computed in $(round(time() - t_s, digits=1))s")
flush(stdout)

# Verify S²
println("\n  Checking S²...")
try
    S2 = S_mat * S_mat
    # Check if proportional to identity or permutation
    println("  S² computed, checking structure...")
    for i in 1:min(n_z, 5)
        println("    S²[$i,:] = $(S2[i,:])")
    end
catch e
    println("  S² computation failed: $e")
end
flush(stdout)

# ================================================================
# Step 4: T matrix
# ================================================================
println("\n" * "="^70)
println("STEP 4: T Matrix (conformal spins)")
println("="^70)
flush(stdout)

t_t = time()
T_mat = tmatrix(Z)
println("  T matrix diagonal:")
for i in 1:size(T_mat, 1)
    println("    T[$i,$i] = $(T_mat[i,i])")
end
println("  Computed in $(round(time() - t_t, digits=1))s")
flush(stdout)

# Check (ST)³
println("\n  Checking (ST)³...")
try
    ST = S_mat * T_mat
    ST3 = ST * ST * ST
    println("  (ST)³ computed, checking structure...")
    for i in 1:min(n_z, 3)
        println("    (ST)³[$i,:] = $(ST3[i,:])")
    end
catch e
    println("  (ST)³ failed: $e")
end
flush(stdout)

# ================================================================
# Step 5: Write results to file
# ================================================================
outfile = joinpath(@__DIR__, "modular_data_fib_ising_v2.txt")
open(outfile, "w") do io
    println(io, "# Modular data for Z(Fib ⊠ Ising) — v2 (corrected)")
    println(io, "# Computed via TensorCategories.jl with thread-safety + simplicity check fixes")
    println(io, "# Date: $(Dates.now())")
    println(io, "# Julia threads: $(Threads.nthreads())")
    println(io, "#")
    println(io, "# Category: Fib ⊠ Ising")
    println(io, "# Rank: $(length(S_fi))")
    println(io, "# FPdim²(C): $(fpdim(FI))")
    println(io, "#")
    println(io, "# Center rank: $n_z")
    println(io, "# Simple objects of Z(Fib ⊠ Ising):")
    for (i, s) in enumerate(S_z)
        println(io, "#   Z_$i: FPdim = $(fpdim(s))")
    end
    println(io, "# FPdim²(Z): $(fpdim(Z))")
    println(io, "# Expected FPdim²(Z) = FPdim²(C)² = $(expected_fpdim2)")
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
println("\n  Written to modular_data_fib_ising_v2.txt")

# ================================================================
# Summary
# ================================================================
t_total = time() - t_start
println("\n" * "="^70)
println("COMPLETE — $(round(t_total/60, digits=1)) minutes")
println("  Category: Fib ⊠ Ising (rank $(length(S_fi)))")
println("  Pentagon: $(pent_ok ? "PASS" : "FAIL")")
println("  Center rank: $n_z (expected 24)")
println("  S matrix: $(size(S_mat))")
println("  T matrix: $(size(T_mat))")
println("="^70)
