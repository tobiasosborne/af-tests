#!/usr/bin/env julia
#=
  Compute the Drinfeld center Z(Fib ⊠ Ising) and modular data.
  Requires ~2 minutes for Fib ⊠ Ising construction + center time.

  Run with:  julia --project=../../TensorCategories.jl compute_fib_ising_center.jl
=#

using Pkg
Pkg.activate(joinpath(@__DIR__, "..", "..", "TensorCategories.jl"))

t_start = time()
println("="^70)
println("DRINFELD CENTER Z(Fib ⊠ Ising)")
println("="^70)
println("Loading TensorCategories.jl + Oscar...")
flush(stdout)

using TensorCategories
using Oscar

println("  Loaded in $(round(time() - t_start, digits=1))s")
flush(stdout)

# Build common field K = QQ(ϕ,√2)
_,x = QQ[:x]
K_phi, phi = number_field(x^2 - x - 1, "ϕ")
_,y = K_phi[:y]
K_rel, sqrt2_rel = number_field(y^2 - 2, "√2")
K, m = absolute_simple_field(K_rel)
m_inv = inv(m)
phi_K = m_inv(K_rel(phi))
sqrt2_K = m_inv(sqrt2_rel)
println("  K = QQ(ϕ,√2), degree $(degree(K))")

# Construct categories
println("  Constructing Fib ⊠ Ising...")
flush(stdout)
Fib = fibonacci_category(K)
Ising = ising_category(K, sqrt2_K, 1)
FI = Fib ⊠ Ising
try set_name!(FI, "Fib ⊠ Ising") catch; end
S_fi = simples(FI)
names_fi = simples_names(FI)
println("  Rank: $(length(S_fi)), FPdim²: $(fpdim(FI))")
flush(stdout)

# Drinfeld center
println("\n" * "="^70)
println("DRINFELD CENTER")
println("="^70)
flush(stdout)

t_center = time()
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

S_z = simples(Z)
n_z = length(S_z)
println("  Center rank: $n_z")
println("  Center computed in $(round(time() - t_center, digits=1))s")

for (i, s) in enumerate(S_z)
    println("    Z_$i: dim = $(fpdim(s))")
end
println("  FPdim²(Z) = $(fpdim(Z))")
flush(stdout)

# Modular S matrix
println("\n" * "="^70)
println("MODULAR S MATRIX")
println("="^70)
flush(stdout)

t_s = time()
S_mat = smatrix(Z)
println("  S matrix ($(size(S_mat))):")
display(S_mat)
println()
println("  Computed in $(round(time() - t_s, digits=1))s")
flush(stdout)

# T matrix
println("\n" * "="^70)
println("MODULAR T MATRIX")
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

# Write to file
open(joinpath(@__DIR__, "modular_data_fib_ising.txt"), "w") do io
    println(io, "# Modular data for Z(Fib ⊠ Ising)")
    println(io, "# Computed via TensorCategories.jl")
    println(io, "# Center rank: $n_z")
    println(io, "#")
    println(io, "# Simple objects of Z(Fib ⊠ Ising):")
    for (i, s) in enumerate(S_z)
        println(io, "#   Z_$i: dim = $(fpdim(s))")
    end
    println(io, "# FPdim²(Z) = $(fpdim(Z))")
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
println("\n  Written to modular_data_fib_ising.txt")

# Summary
t_total = time() - t_start
println("\n" * "="^70)
println("COMPLETE — $(round(t_total/60, digits=1)) minutes")
println("  Center rank: $n_z")
println("  S matrix: $(size(S_mat))")
println("="^70)
