#!/usr/bin/env julia
#= Trace each morphism in the pentagon equation for (2,7,7,7) =#
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

X,Y,Z,W = S[2],S[7],S[7],S[7]
BLK = 8  # the failing block

println("Pentagon equation for (2,7,7,7), block $BLK")
println("=" ^ 60)

# LHS: (id(X)⊗α(Y,Z,W)) ∘ α(X,Y⊗Z,W) ∘ (α(X,Y,Z)⊗id(W))
# RHS: α(X,Y,Z⊗W) ∘ α(X⊗Y,Z,W)

println("\n--- Individual morphisms ---")

a_XYZ = associator(X,Y,Z)
println("α(X,Y,Z) block $BLK: $(a_XYZ.m[BLK])")

a_YZW = associator(Y,Z,W)
println("α(Y,Z,W) block $BLK: $(a_YZW.m[BLK])")

a_XYZ_idW = a_XYZ ⊗ id(W)
println("α(X,Y,Z)⊗id(W) block $BLK: $(a_XYZ_idW.m[BLK])")

idX_aYZW = id(X) ⊗ a_YZW
println("id(X)⊗α(Y,Z,W) block $BLK: $(idX_aYZW.m[BLK])")

YZ = Y ⊗ Z
a_XYZW = associator(X, YZ, W)
println("α(X,Y⊗Z,W) block $BLK: $(a_XYZW.m[BLK])")

ZW = Z ⊗ W
a_XYZW2 = associator(X, Y, ZW)
println("α(X,Y,Z⊗W) block $BLK: $(a_XYZW2.m[BLK])")

XY = X ⊗ Y
a_XYZW3 = associator(XY, Z, W)
println("α(X⊗Y,Z,W) block $BLK: $(a_XYZW3.m[BLK])")

println("\n--- LHS composition ---")
lhs1 = a_XYZ_idW
println("Step 1 (α(X,Y,Z)⊗id(W)): $(lhs1.m[BLK])")

lhs2 = a_XYZW ∘ lhs1
println("Step 2 (α(X,Y⊗Z,W) ∘ step1): $(lhs2.m[BLK])")

lhs3 = idX_aYZW ∘ lhs2
println("Step 3 (id(X)⊗α(Y,Z,W) ∘ step2): $(lhs3.m[BLK])")
println("LHS final: $(lhs3.m[BLK])")

println("\n--- RHS composition ---")
rhs1 = a_XYZW3
println("Step 1 (α(X⊗Y,Z,W)): $(rhs1.m[BLK])")

rhs2 = a_XYZW2 ∘ rhs1
println("Step 2 (α(X,Y,Z⊗W) ∘ step1): $(rhs2.m[BLK])")
println("RHS final: $(rhs2.m[BLK])")

println("\n--- Comparison ---")
println("LHS == RHS: $(lhs3 == rhs2)")
println("Diff: $(lhs3.m[BLK] - rhs2.m[BLK])")

# Now check which step introduces the discrepancy
println("\n--- Isolate the problem ---")
# Does α(X,Y⊗Z,W) contain the P_{23}?
println("α(X,Y⊗Z,W) is the non-simple assoc. Its block $BLK:")
println("  $(a_XYZW.m[BLK])")
println("Is this the identity? $(a_XYZW.m[BLK] == identity_matrix(base_ring(CxG), 4))")

# Does α(X⊗Y,Z,W) contain P_{23}?
println("α(X⊗Y,Z,W) block $BLK:")
println("  $(a_XYZW3.m[BLK])")
println("Is this the identity? $(a_XYZW3.m[BLK] == identity_matrix(base_ring(CxG), 4))")

# Check: is the problem that α(X,Y⊗Z,W) has P_{23} but the pentagon expects identity?
# Or is P_{23} correct and something else is wrong?
println("\n--- Check: does replacing α(X,Y⊗Z,W) with identity fix it? ---")
# If α(X,Y⊗Z,W) were identity, LHS step 2 would be just lhs1
lhs2_test = lhs1  # pretend α(X,Y⊗Z,W) = id
lhs3_test = idX_aYZW ∘ lhs2_test
println("LHS with id instead of α(X,Y⊗Z,W): $(lhs3_test.m[BLK])")
println("Would match RHS? $(lhs3_test.m[BLK] == rhs2.m[BLK])")

println("\n--- Check: does replacing α(X⊗Y,Z,W) with identity fix it? ---")
rhs1_test = id(XY⊗Z⊗W)
rhs2_test = a_XYZW2 ∘ rhs1_test
println("RHS with id instead of α(X⊗Y,Z,W): $(rhs2_test.m[BLK])")

println("\nDONE")
