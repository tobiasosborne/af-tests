#!/usr/bin/env julia
#=
  Focused pentagon debug: trace exactly what goes wrong for pentagon(2,7,7,7)
=#

using Pkg
Pkg.activate(joinpath(@__DIR__, "..", "..", "TensorCategories.jl"))
println("Loading..."); flush(stdout)
using TensorCategories, Oscar

# Build CxG (same setup)
Fib = fibonacci_category()
FibFib = Fib ⊠ Fib
S_ff = simples(FibFib)
n_indecs = length(S_ff)
swap_images = [S_ff[1], S_ff[3], S_ff[2], S_ff[4]]
σ_sixj = TensorCategories.SixJFunctor(FibFib, FibFib, swap_images)
id_images = [S_ff[1], S_ff[2], S_ff[3], S_ff[4]]
id_sixj = TensorCategories.SixJFunctor(FibFib, FibFib, id_images)
indecs = simples(FibFib)
id_mon = Dict((i,j) => id(indecs[i] ⊗ indecs[j]) for i in 1:n_indecs, j in 1:n_indecs)
σ_mon = Dict((i,j) => id(σ_sixj(indecs[i]) ⊗ σ_sixj(indecs[j])) for i in 1:n_indecs, j in 1:n_indecs)
id_functor = TensorCategories.MonoidalFunctor(id_sixj, indecs, id_mon)
σ_functor = TensorCategories.MonoidalFunctor(σ_sixj, indecs, σ_mon)
G = symmetric_group(2)
elems_G = collect(elements(G))
id_idx = findfirst(g -> isone(g), elems_G)
if id_idx != 1; elems_G[1], elems_G[id_idx] = elems_G[id_idx], elems_G[1]; end
images_functors = [id_functor, σ_functor]
sixj_functors = [id_sixj, σ_sixj]
monoidal_dict = Dict{Tuple{Int,Int}, Any}()
for a in 1:2, b in 1:2
    comp_sixj = TensorCategories.compose(sixj_functors[b], sixj_functors[a])
    g_ab = elems_G[a] * elems_G[b]
    ab_idx = findfirst(==(g_ab), elems_G)
    components = [id(sixj_functors[ab_idx](indecs[i])) for i in 1:n_indecs]
    monoidal_dict[(a, b)] = TensorCategories.AdditiveNaturalTransformation(
        comp_sixj, sixj_functors[ab_idx], indecs, components)
end
action = TensorCategories.GTensorAction(FibFib, G, elems_G, images_functors, monoidal_dict)
try set_name!(FibFib, "Fib ⊠ Fib") catch; end
CxG = gcrossed_product(FibFib, action)
S = simples(CxG)
names = simples_names(CxG)
println("Built CxG: rank $(length(S))")
println("Simples: $names")
flush(stdout)

# ================================================================
# Debug pentagon(2,7,7,7)
# ================================================================
println("\n" * "="^70)
println("Pentagon(2,7,7,7) = S₂ × S₇ × S₇ × S₇")
println("  S₂ = $(names[2])")
println("  S₇ = $(names[7])")
println("="^70)
flush(stdout)

X, Y, Z, W = S[2], S[7], S[7], S[7]

println("\nComponents:")
println("  X = $(X.components)")
println("  Y = $(Y.components)")
println("  Z = $(Z.components)")
println("  W = $(W.components)")
println("  Y⊗Z = $((Y⊗Z).components)")
println("  Z⊗W = $((Z⊗W).components)")
println("  X⊗Y = $((X⊗Y).components)")
println("  (X⊗Y)⊗Z = $((X⊗Y⊗Z).components)")
println("  X⊗(Y⊗Z) = $((X⊗(Y⊗Z)).components)")
flush(stdout)

# Compute LHS and RHS of pentagon
println("\nComputing pentagon sides...")
flush(stdout)

println("  α(Y,Z,W)...")
a_YZW = associator(Y,Z,W)
println("    OK: $(domain(a_YZW)) → $(codomain(a_YZW))")

println("  id(X)⊗α(Y,Z,W)...")
lhs1 = id(X) ⊗ a_YZW
println("    OK: $(domain(lhs1)) → $(codomain(lhs1))")

println("  α(X,Y⊗Z,W)...")
a_XYZW = associator(X, Y⊗Z, W)
println("    OK: $(domain(a_XYZW)) → $(codomain(a_XYZW))")

println("  α(X,Y,Z)⊗id(W)...")
a_XYZ = associator(X,Y,Z)
lhs3 = a_XYZ ⊗ id(W)
println("    OK: $(domain(lhs3)) → $(codomain(lhs3))")

println("  α(X,Y,Z⊗W)...")
a_XYZW2 = associator(X,Y,Z⊗W)
println("    OK: $(domain(a_XYZW2)) → $(codomain(a_XYZW2))")

println("  α(X⊗Y,Z,W)...")
a_XYZW3 = associator(X⊗Y,Z,W)
println("    OK: $(domain(a_XYZW3)) → $(codomain(a_XYZW3))")

LHS = compose(lhs3, a_XYZW, lhs1)
RHS = compose(a_XYZW3, a_XYZW2)
println("\nLHS and RHS computed.")
println("LHS == RHS: $(LHS == RHS)")
flush(stdout)

# Compare block-by-block
println("\nBlock-by-block comparison:")
for k in 1:length(LHS.m)
    if size(LHS.m[k]) != (0,0)
        diff = LHS.m[k] - RHS.m[k]
        if !iszero(diff)
            println("  Block $k ($(names[k])): DIFFERS!")
            println("    Size: $(size(LHS.m[k]))")
            println("    LHS[$k] = $(LHS.m[k])")
            println("    RHS[$k] = $(RHS.m[k])")
            println("    Diff = $(diff)")
        else
            println("  Block $k ($(names[k])): OK (size $(size(LHS.m[k])))")
        end
    end
end
flush(stdout)

# ================================================================
# Now debug the associator on non-simple objects
# Focus on α(X, Y⊗Z, W) where Y⊗Z is non-simple
# ================================================================
println("\n" * "="^70)
println("DEBUG: associator(X, Y⊗Z, W) internals")
println("="^70)
flush(stdout)

YZ = Y ⊗ Z
println("Y⊗Z components: $(YZ.components)")
println("Is Y⊗Z simple? $(is_simple(YZ))")
println("one(CxG) components: $(one(CxG).components)")
println("one(CxG) ∈ [X, YZ, W]: $(one(CxG) ∈ [X, YZ, W])")
flush(stdout)

# Check if the shortcut is triggered
if one(CxG) ∈ [X, YZ, W]
    println("  SHORTCUT: one(C) ∈ arguments, returns id")
else
    println("  Takes non-simple code path")

    simple_objects = simples(CxG)
    n = CxG.simples

    X_summands = vcat([[s for l ∈ 1:X.components[k]] for (k,s) ∈ zip(1:n, simple_objects)]...)
    Y_summands = vcat([[s for l ∈ 1:YZ.components[k]] for (k,s) ∈ zip(1:n, simple_objects)]...)
    Z_summands = vcat([[s for l ∈ 1:W.components[k]] for (k,s) ∈ zip(1:n, simple_objects)]...)

    println("  X_summands: $(length(X_summands)) = $([findfirst(e -> e == 1, s.components) for s in X_summands])")
    println("  Y_summands (Y⊗Z): $(length(Y_summands)) = $([findfirst(e -> e == 1, s.components) for s in Y_summands])")
    println("  Z_summands (W): $(length(Z_summands)) = $([findfirst(e -> e == 1, s.components) for s in Z_summands])")
end
flush(stdout)

# ================================================================
# Check F-symbols directly for the failing 4-tuple
# ================================================================
println("\n" * "="^70)
println("DEBUG: F-symbols for (2,7,7,7)")
println("="^70)
flush(stdout)

i,j,k = 2,7,7
println("6j-symbols for (i=$i, j=$j, k=$k):")
for l in 1:length(S)
    F = TensorCategories.six_j_symbol(CxG, i, j, k, l)
    if size(F) != (0,0)
        println("  F[$i,$j,$k,$l] = $F  (size $(size(F)))")
    end
end

# Also check the associator on simples directly
println("\nDirect associator on simples (2,7,7):")
a_simple = associator(S[2], S[7], S[7])
for (kk, m) in enumerate(a_simple.m)
    if size(m) != (0,0)
        println("  Block $kk: $(m) (size $(size(m)))")
    end
end

# Compare with stored ass
println("\nStored C.ass entries for (2,7,7):")
for l in 1:length(S)
    F = CxG.ass[2,7,7,l]
    if size(F) != (0,0)
        println("  ass[2,7,7,$l] = $F  (size $(size(F)))")
    end
end

println("\n" * "="^70)
println("DEBUG COMPLETE")
println("="^70)
