#!/usr/bin/env julia
#= Quick pentagon test focused on the known failing tuple (2,7,7,7) =#
using Pkg
Pkg.activate(joinpath(@__DIR__, "..", "..", "TensorCategories.jl"))
println("Loading..."); flush(stdout)
using TensorCategories, Oscar

# Build CxG
Fib = fibonacci_category()
FibFib = Fib ⊠ Fib
S_ff = simples(FibFib)
n_i = length(S_ff)
swap_images = [S_ff[1], S_ff[3], S_ff[2], S_ff[4]]
σ_sixj = TensorCategories.SixJFunctor(FibFib, FibFib, swap_images)
id_sixj = TensorCategories.SixJFunctor(FibFib, FibFib, S_ff)
indecs = simples(FibFib)
id_mon = Dict((i,j) => id(indecs[i]⊗indecs[j]) for i in 1:n_i, j in 1:n_i)
σ_mon = Dict((i,j) => id(σ_sixj(indecs[i])⊗σ_sixj(indecs[j])) for i in 1:n_i, j in 1:n_i)
id_f = TensorCategories.MonoidalFunctor(id_sixj, indecs, id_mon)
σ_f = TensorCategories.MonoidalFunctor(σ_sixj, indecs, σ_mon)
G = symmetric_group(2)
eG = collect(elements(G))
id_idx = findfirst(isone, eG)
if id_idx != 1; eG[1], eG[id_idx] = eG[id_idx], eG[1]; end
sj = [id_sixj, σ_sixj]
md = Dict{Tuple{Int,Int},Any}()
for a in 1:2, b in 1:2
    cs = TensorCategories.compose(sj[b], sj[a])
    ab = findfirst(==(eG[a]*eG[b]), eG)
    md[(a,b)] = TensorCategories.AdditiveNaturalTransformation(cs,sj[ab],indecs,[id(sj[ab](indecs[i])) for i in 1:n_i])
end
act = TensorCategories.GTensorAction(FibFib,G,eG,[id_f,σ_f],md)
try set_name!(FibFib,"Fib⊠Fib") catch; end
CxG = gcrossed_product(FibFib, act)
S = simples(CxG)
println("Built CxG: rank $(length(S))")
flush(stdout)

# Quick test: the known failing tuple
println("\n=== Quick test: pentagon(2,7,7,7) ===")
ok = pentagon_axiom(S[2],S[7],S[7],S[7])
println("pentagon(2,7,7,7) = $ok")

if !ok
    # Show the difference
    X,Y,Z,W = S[2],S[7],S[7],S[7]
    f = (id(X)⊗associator(Y,Z,W)) ∘ associator(X,Y⊗Z,W) ∘ (associator(X,Y,Z)⊗id(W))
    g = associator(X,Y,Z⊗W) ∘ associator(X⊗Y,Z,W)
    println("Block-by-block diff:")
    for k in 1:length(S)
        diff = f.m[k] - g.m[k]
        if !iszero(diff)
            println("  Block $k: nonzero diff, size $(size(diff))")
            println("  $diff")
        end
    end
end

# Full sweep
println("\n=== Full pentagon sweep ===")
flush(stdout)
fails = 0
fail_tuples = Tuple{Int,Int,Int,Int}[]
n = length(S)
for i in 1:n, j in 1:n, k in 1:n, l in 1:n
    ok = pentagon_axiom(S[i],S[j],S[k],S[l])
    if !ok
        fails += 1
        if length(fail_tuples) < 10
            push!(fail_tuples, (i,j,k,l))
        end
    end
end
println("Pentagon failures: $fails / $(n^4)")
if fails == 0
    println("PENTAGON PASS ✓")
else
    println("PENTAGON FAIL ✗")
    println("First failing tuples: $fail_tuples")
end
flush(stdout)
