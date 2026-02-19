#!/usr/bin/env julia
#=
  Trace the exact ordering mismatch in pentagon(2,7,7,7)
  Block 8 has a 4×4 matrix with rows 2,3 swapped.
  Need to find which tensor product ordering convention differs.
=#

using Pkg
Pkg.activate(joinpath(@__DIR__, "..", "..", "TensorCategories.jl"))
println("Loading..."); flush(stdout)
using TensorCategories, Oscar

# Build CxG
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
n = CxG.simples
println("Built CxG: rank $n")
flush(stdout)

X, Y, Z, W = S[2], S[7], S[7], S[7]
YZ = Y ⊗ Z  # [1,0,1,0,1,0,1,0]

# ================================================================
# Trace the ordering within the tensor product X ⊗ YZ block 8
# ================================================================
println("\n" * "="^70)
println("TRACE: Block structure of X ⊗ YZ in block 8")
println("="^70)
flush(stdout)

# X = S₂ = [0,1,0,0,0,0,0,0]
# YZ = [1,0,1,0,1,0,1,0]
# (X ⊗ YZ)[8] = sum_{i,j} table[i,j,8] * X[i] * YZ[j]
# Only i=2 contributes (since X[i] = 0 for i≠2)
# So (X ⊗ YZ)[8] = sum_j table[2,j,8] * 1 * YZ[j]

table = CxG.tensor_product
println("Fusion rules table[2,j,8] for j=1..8:")
for j in 1:n
    if table[2,j,8] > 0 && YZ.components[j] > 0
        println("  table[2,$j,8] = $(table[2,j,8]), YZ[$j] = $(YZ.components[j]) → contributes $(table[2,j,8] * YZ.components[j])")
    end
end
total_8 = sum(table[2,j,8] * YZ.components[j] for j in 1:n)
println("Total (X⊗YZ)[8] = $total_8")
flush(stdout)

# Now trace how tensor_product(f,g) orders these
# In the for loop: for i=1..n, j=1..n
# Only i=2 matters. For i=2:
#   j=1: table[2,1,8], YZ[1]=1  → contributes table[2,1,8]*1*1
#   j=3: table[2,3,8], YZ[3]=1  → contributes table[2,3,8]*1*1
#   j=5: table[2,5,8], YZ[5]=1  → contributes table[2,5,8]*1*1
#   j=7: table[2,7,8], YZ[7]=1  → contributes table[2,7,8]*1*1

println("\nTensor product ordering for block 8:")
println("Iteration order (i outer, j inner):")
row_idx = 0
for i in 1:n
    for j in 1:n
        c = table[i,j,8]
        dx = X.components[i]
        dy = YZ.components[j]
        if c > 0 && dx > 0 && dy > 0
            contrib = c * dx * dy
            println("  (i=$i,j=$j): table=c=$c, X[$i]=$dx, YZ[$j]=$dy → $contrib rows starting at $(row_idx+1)")
            row_idx += contrib
        end
    end
end
flush(stdout)

# ================================================================
# Now trace the associator's internal decomposition
# ================================================================
println("\n" * "="^70)
println("TRACE: Non-simple associator decomposition")
println("="^70)
flush(stdout)

simple_objects = S
X_summands = vcat([[s for l ∈ 1:X.components[k]] for (k,s) ∈ zip(1:n, simple_objects)]...)
Y_summands = vcat([[s for l ∈ 1:YZ.components[k]] for (k,s) ∈ zip(1:n, simple_objects)]...)
Z_summands = vcat([[s for l ∈ 1:W.components[k]] for (k,s) ∈ zip(1:n, simple_objects)]...)

println("X_summands types: $([findfirst(==(1), s.components) for s in X_summands])")
println("Y_summands types: $([findfirst(==(1), s.components) for s in Y_summands])")
println("Z_summands types: $([findfirst(==(1), s.components) for s in Z_summands])")

# The associator m = direct_sum([associator(x,y,z) for x ∈ X_summands, y ∈ Y_summands, z ∈ Z_summands][:])
# Ordering: column-major on the 3D array → x varies fastest, then y, then z
# Since |X_summands|=1, |Z_summands|=1, this is just iterating over Y_summands
println("\nBlock-diagonal associators (x varies fastest):")
for (y_idx, y) in enumerate(Y_summands)
    y_type = findfirst(==(1), y.components)
    a = associator(X_summands[1], y, Z_summands[1])
    println("  y_idx=$y_idx (type $y_type): α[2,$y_type,7] → block 8 entry = $(a.m[8])")
end
flush(stdout)

# ================================================================
# Now trace the distribution morphisms
# ================================================================
println("\n" * "="^70)
println("TRACE: Distribution morphisms")
println("="^70)
flush(stdout)

_,ix,px = direct_sum(X_summands...)
_,iy,py = direct_sum(Y_summands...)
_,iz,pz = direct_sum(Z_summands...)

println("Projections from YZ onto Y_summands (py[j].m[k]):")
for (j, p) in enumerate(py)
    y_type = findfirst(==(1), Y_summands[j].components)
    for k in 1:n
        if size(p.m[k]) != (0,0) && !iszero(p.m[k])
            println("  py[$j] (type $y_type): block $k = $(p.m[k])")
        end
    end
end

println("\nInclusions from Y_summands into YZ (iy[j].m[k]):")
for (j, inc) in enumerate(iy)
    y_type = findfirst(==(1), Y_summands[j].components)
    for k in 1:n
        if size(inc.m[k]) != (0,0) && !iszero(inc.m[k])
            println("  iy[$j] (type $y_type): block $k = $(inc.m[k])")
        end
    end
end
flush(stdout)

# ================================================================
# Trace how distr_before works for block 8
# ================================================================
println("\n" * "="^70)
println("TRACE: distr_before block 8")
println("="^70)
flush(stdout)

# distr_before = vertical_direct_sum([(f⊗g)⊗h for f ∈ px, g ∈ py, h ∈ pz][:])
# Since |px|=1, |pz|=1, this is vertical_direct_sum([(px[1]⊗py[j])⊗pz[1] for j in 1:4])

for (j, p_y) in enumerate(py)
    y_type = findfirst(==(1), Y_summands[j].components)
    fg = px[1] ⊗ p_y   # X⊗YZ → x₁⊗y_j
    fgh = fg ⊗ pz[1]   # (X⊗YZ)⊗W → (x₁⊗y_j)⊗z₁
    println("  j=$j (type $y_type): (px⊗py[$j])⊗pz block 8:")
    println("    domain block 8 size: $(size(fgh.m[8]))")
    if size(fgh.m[8]) != (0,0)
        println("    matrix: $(fgh.m[8])")
    end
end
flush(stdout)

# ================================================================
# Compare with the tensor product's internal ordering
# ================================================================
println("\n" * "="^70)
println("TRACE: Tensor product X⊗(Y⊗Z) block 8 internal ordering")
println("="^70)
flush(stdout)

# For X ⊗ YZ, block 8 has contributions from (i=2, j=?) pairs.
# For each j: table[2,j,8] * X[2] * YZ[j]
# j=1 (type 1): table[2,1,8] * 1 * 1 = ?
# j=3 (type 3): table[2,3,8] * 1 * 1 = ?
# j=5 (type 5): table[2,5,8] * 1 * 1 = ?
# j=7 (type 7): table[2,7,8] * 1 * 1 = ?

println("table[2,j,8] values:")
for j in [1,3,5,7]
    println("  table[2,$j,8] = $(table[2,j,8])")
end

# Now check: what order does the projection from direct_sum(Y_summands)
# give vs what order the tensor product uses?
println("\nY = Y⊗Z = S₇⊗S₇, components = $(YZ.components)")
println("YZ is built by tensor_product(S₇, S₇)")
println("In tensor_product, block k of S₇⊗S₇:")
println("  Only (i=7,j=7) contributes since S₇=[0,0,0,0,0,0,1,0]")
for k in 1:n
    c = table[7,7,k]
    if c > 0
        println("  block $k: table[7,7,$k] = $c")
    end
end

# Now for X ⊗ YZ where YZ has components [1,0,1,0,1,0,1,0]:
# block 8: sum_j table[2,j,8] * YZ[j] for j with YZ[j]>0
# = table[2,1,8]*1 + table[2,3,8]*1 + table[2,5,8]*1 + table[2,7,8]*1
println("\nFor X ⊗ YZ, block 8:")
println("  table[2,1,8] = $(table[2,1,8]) (j=1, type (𝟙⊠𝟙,e))")
println("  table[2,3,8] = $(table[2,3,8]) (j=3, type (𝟙⊠τ,e))")
println("  table[2,5,8] = $(table[2,5,8]) (j=5, type (τ⊠𝟙,e))")
println("  table[2,7,8] = $(table[2,7,8]) (j=7, type (τ⊠τ,e))")
println("  Total = $(sum(table[2,j,8] for j in [1,3,5,7]))")
println("  Ordering in tensor_product: j=1, j=3, j=5, j=7 (i=2 is outer, j is inner)")

# The projections py[1..4] correspond to types [1,3,5,7] in that order
# The direct_sum(Y_summands) also orders by type: 1,3,5,7
# These match!

# But what about (x⊗y)⊗z → x⊗(y⊗z) when going through the tensor product?
# Let's check: for (X⊗YZ)⊗W, block 8's internal structure
println("\n\n(X⊗YZ)⊗W block 8:")
XYZ = X ⊗ YZ
println("  X⊗YZ components: $(XYZ.components)")
for i in 1:n
    for j in 1:n
        c = table[i,j,8]
        if c > 0 && XYZ.components[i] > 0 && W.components[j] > 0
            println("  (i=$i,j=$j): table[$i,$j,8]=$c, XYZ[$i]=$(XYZ.components[i]), W[$j]=$(W.components[j]) → $(c * XYZ.components[i] * W.components[j]) rows")
        end
    end
end

println("\nX⊗(YZ⊗W) block 8:")
YZW = YZ ⊗ W
println("  YZ⊗W components: $(YZW.components)")
for i in 1:n
    for j in 1:n
        c = table[i,j,8]
        if c > 0 && X.components[i] > 0 && YZW.components[j] > 0
            println("  (i=$i,j=$j): table[$i,$j,8]=$c, X[$i]=$(X.components[i]), YZW[$j]=$(YZW.components[j]) → $(c * X.components[i] * YZW.components[j]) rows")
        end
    end
end

println("\n" * "="^70)
println("DEBUG COMPLETE")
println("="^70)
