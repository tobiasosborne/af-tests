#!/usr/bin/env julia
#=
  Minimal reproduction of Drinfeld center crash on (Fib⊠Fib)⋊S₂
  Goal: capture the actual error message and stacktrace
=#

using Pkg
Pkg.activate(joinpath(@__DIR__, "..", "..", "TensorCategories.jl"))

println("Loading TensorCategories.jl + Oscar...")
flush(stdout)
t0 = time()

using TensorCategories
using Oscar

println("  Loaded in $(round(time() - t0, digits=1))s")
flush(stdout)

# ================================================================
# Build (Fib⊠Fib)⋊S₂ — same as compute_fsymbols.jl
# ================================================================
println("\nBuilding (Fib⊠Fib)⋊S₂...")
flush(stdout)

Fib = fibonacci_category()
FibFib = Fib ⊠ Fib
S_ff = simples(FibFib)
n_indecs = length(S_ff)

# Build swap action
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
if id_idx != 1
    elems_G[1], elems_G[id_idx] = elems_G[id_idx], elems_G[1]
end

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
S_cxg = simples(CxG)
println("  Built: rank $(length(S_cxg)), FPdim² = $(fpdim(CxG))")
flush(stdout)

# ================================================================
# Debug 1: Pentagon axiom — identify exactly which 4-tuple fails
# ================================================================
println("\n" * "="^70)
println("DEBUG 1: Pentagon axiom — checking individual 4-tuples")
println("="^70)
flush(stdout)

n = length(S_cxg)
global pent_fail_count = 0
for i in 1:n, j in 1:n, k in 1:n, l in 1:n
    try
        ok = pentagon_axiom(S_cxg[i], S_cxg[j], S_cxg[k], S_cxg[l])
        if !ok
            global pent_fail_count += 1
            if pent_fail_count <= 5
                println("  FAIL: pentagon($i,$j,$k,$l) [$(simples_names(CxG)[[i,j,k,l]])]")
            end
        end
    catch e
        global pent_fail_count += 1
        if pent_fail_count <= 5
            println("  ERROR: pentagon($i,$j,$k,$l): $e")
        end
    end
end
println("  Total failures: $pent_fail_count / $(n^4)")
flush(stdout)

# ================================================================
# Debug 2: Drinfeld center — step through induction
# ================================================================
println("\n" * "="^70)
println("DEBUG 2: Drinfeld center — step-by-step induction")
println("="^70)
flush(stdout)

Z = center(CxG)
names = simples_names(CxG)

for (idx, s) in enumerate(S_cxg)
    println("\n  --- Inducing simple $idx ($(names[idx])) ---")
    flush(stdout)

    try
        # Step 1: Build induction object manually to find where it breaks
        simpls = simples(CxG)
        println("    Step 1: Computing s_i ⊗ X ⊗ dual(s_i) for each simple s_i...")
        flush(stdout)

        summands = []
        for (i, si) in enumerate(simpls)
            try
                d = dual(si)
                prod = si ⊗ s ⊗ d
                push!(summands, prod)
            catch e
                println("    ERROR at summand $i: dual or tensor: $e")
                println("    Stacktrace: $(catch_backtrace()[1:min(5,end)])")
            end
        end
        println("    All $(length(summands)) summands computed OK")

        # Step 2: direct_sum
        println("    Step 2: direct_sum...")
        flush(stdout)
        try
            ds = direct_sum(summands)[1]
            println("    direct_sum OK: $(ds)")
        catch e
            println("    ERROR in direct_sum: $e")
        end

        # Step 3: Full induction
        println("    Step 3: Full induction(s)...")
        flush(stdout)
        ind_s = induction(s, parent_category=Z)
        println("    Induction OK: $(ind_s)")

        # Step 4: End(I(s))
        println("    Step 4: end_of_induction...")
        flush(stdout)
        H = TensorCategories.end_of_induction(s, ind_s)
        println("    End space dim: $(length(basis(H)))")

        # Step 5: simple_subobjects
        println("    Step 5: simple_subobjects...")
        flush(stdout)
        subs = simple_subobjects(ind_s, H)
        println("    Found $(length(subs)) simples")

    catch e
        println("    CRASH: $e")
        bt = catch_backtrace()
        for line in stacktrace(bt)[1:min(15,length(stacktrace(bt)))]
            println("      $line")
        end
    end
    flush(stdout)

    # Only try first 2 simples for debugging
    if idx >= 2
        println("\n  (Stopping after 2 simples for debugging)")
        break
    end
end

println("\n" * "="^70)
println("DEBUG COMPLETE")
println("="^70)
