#!/usr/bin/env julia
#= Targeted diagnostic: trace where P_{23} permutation enters in pentagon(2,7,7,7) =#
using Pkg
Pkg.activate(joinpath(@__DIR__, "..", "..", "TensorCategories.jl"))
using TensorCategories, Oscar

# Build CxG (compact)
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
n = length(S)
println("Built CxG: rank $n")

X,Y,Z,W = S[2],S[7],S[7],S[7]
YZ = Y ⊗ Z
println("\nYZ = S[7]⊗S[7], components = $(YZ.components)")

println("\n=== STEP 1: Check simple associators ===")
for i in 1:n, j in 1:n, k in 1:n
    a = associator(S[i],S[j],S[k])
    ia = inv_associator(S[i],S[j],S[k])
    prod = TensorCategories.compose(a, ia)
    ident = id(S[i]⊗S[j]⊗S[k])
    if prod != ident
        println("  assoc($i,$j,$k) ∘ inv_assoc ≠ id!")
    end
end
println("  Simple associator inverses: OK")

println("\n=== STEP 2: Decompose associator(X, YZ, W) ===")
println("  X=S[2], YZ=S[7]⊗S[7], W=S[7]")

simple_objects = simples(CxG)
Y_summands = vcat([[s for l in 1:YZ.components[k]] for (k,s) in zip(1:n, simple_objects)]...)
println("  Y_summands types: ", [findfirst(e -> e != 0, s.components) for s in Y_summands])

# Build the pieces
_,ix,px = direct_sum([X])
_,iy,py = direct_sum(Y_summands...)
_,iz,pz = direct_sum([W])

println("  #projections from direct_sum(Y_summands): $(length(py))")

# Check distr_before
println("\n=== STEP 3: Check distr_before ===")
projs = [(f⊗g)⊗h for f in px, g in py, h in pz][:]
println("  #projection morphisms: $(length(projs))")
for (idx, p) in enumerate(projs)
    println("  proj[$idx] block 8: size=$(size(p.m[8])), nonzero=$(count(!iszero, p.m[8]))")
end

distr_before = TensorCategories.vertical_direct_sum(projs)
println("  distr_before block 8: size=$(size(distr_before.m[8]))")

# Check m
println("\n=== STEP 4: Check block-diagonal m ===")
assocs = [associator(x,y,z) for x in [X], y in Y_summands, z in [W]][:]
println("  #assoc blocks: $(length(assocs))")
for (idx, a) in enumerate(assocs)
    y_type = findfirst(e -> e != 0, Y_summands[idx].components)
    println("  assoc(2,$y_type,7) block 8: size=$(size(a.m[8]))")
    if size(a.m[8],1) > 0
        println("    matrix = $(a.m[8])")
    end
end

m = direct_sum(assocs...)
println("  m block 8: size=$(size(m.m[8]))")

# Check distr_after
println("\n=== STEP 5: Check distr_after ===")
incls = [f⊗(g⊗h) for f in ix, g in iy, h in iz][:]
distr_after = TensorCategories.horizontal_direct_sum(incls)
println("  distr_after block 8: size=$(size(distr_after.m[8]))")

# Result
println("\n=== STEP 6: Check composition ===")
result = TensorCategories.compose(distr_before, m, distr_after)
println("  result block 8: size=$(size(result.m[8]))")
println("  result block 8 matrix:")
println("  $(result.m[8])")

# Compare with what the pentagon expects
println("\n=== STEP 7: Compare with pentagon ===")
# LHS piece 2: assoc(X, YZ, W)
a_direct = associator(X, YZ, W)
println("  assoc(X,YZ,W) block 8:")
println("  $(a_direct.m[8])")

# Check: is result == a_direct?
diff = result.m[8] - a_direct.m[8]
println("  diff (result - a_direct) block 8:")
println("  $(diff)")

println("\n=== STEP 8: Stored 6j symbols for (2,7,7) ===")
for l in 1:n
    sym = TensorCategories.six_j_symbol(CxG, 2, 7, 7, l)
    if size(sym,1) > 0 && size(sym,2) > 0
        println("  6j(2,7,7,$l): size=$(size(sym))")
        println("    $sym")
    end
end

println("\n=== STEP 9: tensor_product block ordering ===")
table = CxG.tensor_product
println("  Contributions to block 8 of (X⊗YZ)⊗W:")
println("  (X⊗YZ) components: $((X⊗YZ).components)")
for p in 1:n, q in 1:n
    c = table[p,q,8]
    xyz_p = (X⊗YZ).components[p]
    w_q = W.components[q]
    if c > 0 && xyz_p > 0 && w_q > 0
        println("    (p=$p, q=$q): c=$c, XYZ[$p]=$xyz_p, W[$q]=$w_q → $(xyz_p*w_q*c) rows")
    end
end

println("\n  Sub-structure of (X⊗YZ) at each p:")
for p in 1:n
    xyz_p = (X⊗YZ).components[p]
    if xyz_p == 0; continue; end
    println("    p=$p: total=$xyz_p")
    for i in 1:n, j in 1:n
        c = table[i,j,p]
        xi = X.components[i]
        yzj = YZ.components[j]
        if c > 0 && xi > 0 && yzj > 0
            println("      from (i=$i,j=$j): X[$i]=$xi, YZ[$j]=$yzj, table[$i,$j,$p]=$c → $(xi*yzj*c)")
        end
    end
end

println("\n=== DONE ===")
