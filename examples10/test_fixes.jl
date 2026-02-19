#!/usr/bin/env julia
#= Test both fixes: pentagon + center =#
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

# Test 1: Pentagon
println("\n=== PENTAGON TEST ===")
flush(stdout)
global pf = 0
n = length(S)
for i in 1:n, j in 1:n, k in 1:n, l in 1:n
    ok = pentagon_axiom(S[i],S[j],S[k],S[l])
    if !ok; global pf += 1; end
end
println("Pentagon failures: $pf / $(n^4)")
println(pf == 0 ? "PENTAGON PASS ✓" : "PENTAGON FAIL ✗")
flush(stdout)

# Test 2: Center (first simple only)
println("\n=== CENTER TEST ===")
flush(stdout)
Z = center(CxG)
s1 = S[1]
println("Inducing simple 1...")
Is = induction(s1, parent_category=Z)
println("Computing end_of_induction...")
H = TensorCategories.end_of_induction(s1, Is)
println("End dim: $(length(basis(H)))")
println("Computing simple_subobjects...")
flush(stdout)
try
    subs = simple_subobjects(Is, H)
    println("Found $(length(subs)) simples ✓")
catch e
    println("CRASH: $e")
end
flush(stdout)

println("\n=== DONE ===")
