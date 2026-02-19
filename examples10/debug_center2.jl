#!/usr/bin/env julia
#=
  Targeted debug: unwrap the threading error in hom_by_adjunction
=#

using Pkg
Pkg.activate(joinpath(@__DIR__, "..", "..", "TensorCategories.jl"))

println("Loading...")
flush(stdout)
using TensorCategories
using Oscar

# Build (Fib⊠Fib)⋊S₂ — same setup
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
S_cxg = simples(CxG)
println("Built CxG: rank $(length(S_cxg))")
flush(stdout)

# ================================================================
# Debug the center crash on simple 1
# ================================================================
println("\n" * "="^70)
println("DEBUG: Hom computation crash")
println("="^70)
flush(stdout)

Z = center(CxG)
s = S_cxg[1]  # (𝟙⊠𝟙, ())

println("Computing induction of simple 1...")
flush(stdout)
Is = induction(s, parent_category=Z)
println("  Induction OK")

println("Computing End(induction(s)) via end_of_induction...")
flush(stdout)
H = TensorCategories.end_of_induction(s, Is)
println("  End dim: $(length(basis(H)))")

# Now step through simple_subobjects_semisimple
println("\nStep through simple_subobjects_semisimple:")
flush(stdout)

E = H
X = Is

# Step 1: central_primitive_idempotents
println("  Computing central primitive idempotents...")
flush(stdout)
try
    idems = TensorCategories.central_primitive_idempotents(E)
    println("  Found $(length(idems)) idempotents")

    # Step 2: image of each idempotent
    println("  Computing images of idempotents...")
    flush(stdout)
    img = [image(i)[1] for i in idems]
    println("  Got $(length(img)) images")

    # Step 3: For each image, compute End
    for (idx, Y) in enumerate(img)
        println("\n  Image $idx: $(Y)")
        println("    Computing End(image_$idx)...")
        flush(stdout)
        try
            EY = End(Y)
            println("    End dim: $(length(basis(EY)))")
        catch e
            println("    CRASH in End: ")
            if e isa CompositeException
                for (k, task_e) in enumerate(e.exceptions)
                    println("      Thread $k error:")
                    if task_e isa TaskFailedException
                        inner = task_e.task.result
                        println("        Inner error: $inner")
                        bt = task_e.task.backtrace
                        if bt !== nothing
                            for line in stacktrace(bt)[1:min(20,length(stacktrace(bt)))]
                                println("          $line")
                            end
                        end
                    else
                        println("        $task_e")
                    end
                end
            else
                println("      $e")
                bt = catch_backtrace()
                for line in stacktrace(bt)[1:min(15,length(stacktrace(bt)))]
                    println("        $line")
                end
            end
        end
        flush(stdout)
    end

catch e
    println("  CRASH in idempotents: $e")
    bt = catch_backtrace()
    for line in stacktrace(bt)[1:min(15,length(stacktrace(bt)))]
        println("    $line")
    end
end

# ================================================================
# Debug: hom_by_adjunction single-threaded
# ================================================================
println("\n" * "="^70)
println("DEBUG: hom_by_adjunction single-threaded")
println("="^70)
flush(stdout)

# Try computing Hom(Is, Is) manually (unthreaded)
try
    C_cat = TensorCategories.category(Z)
    S_gen = TensorCategories.induction_generators(Z)
    println("  Induction generators: $(length(S_gen))")

    X_Homs = [Hom(object(Is), sg) for sg in S_gen]
    Y_Homs = [Hom(sg, object(Is)) for sg in S_gen]
    candidates = [int_dim(h1)*int_dim(h2) > 0 for (h1,h2) in zip(X_Homs, Y_Homs)]
    println("  Candidates: $(findall(==(true), candidates))")

    for i in findall(==(true), candidates)
        println("\n  --- Candidate $i (gen = $(S_gen[i])) ---")
        flush(stdout)
        sg = S_gen[i]
        X_s = X_Homs[i]
        s_Y = Y_Homs[i]
        println("    dim Hom(obj(X), s) = $(int_dim(X_s))")
        println("    dim Hom(s, obj(Y)) = $(int_dim(s_Y))")

        println("    Computing induction of generator $i...")
        flush(stdout)
        Is_gen = induction(sg, parent_category=Z)
        println("    Induction OK")

        println("    Computing induction_right_adjunction...")
        flush(stdout)
        try
            B = TensorCategories.induction_right_adjunction(X_s, Is, Is_gen)
            println("    Right adjunction dim: $(length(basis(B)))")
        catch e
            println("    CRASH in right adjunction: $e")
            if e isa CompositeException
                for task_e in e.exceptions
                    if task_e isa TaskFailedException
                        println("      Inner: $(task_e.task.result)")
                        bt = task_e.task.backtrace
                        if bt !== nothing
                            for line in stacktrace(bt)[1:min(10,length(stacktrace(bt)))]
                                println("        $line")
                            end
                        end
                    end
                end
            else
                bt = catch_backtrace()
                for line in stacktrace(bt)[1:min(10,length(stacktrace(bt)))]
                    println("      $line")
                end
            end
            continue
        end

        println("    Computing induction_adjunction...")
        flush(stdout)
        try
            B2 = TensorCategories.induction_adjunction(s_Y, Is, Is_gen)
            println("    Left adjunction dim: $(length(basis(B2)))")
        catch e
            println("    CRASH in left adjunction: $e")
            if e isa CompositeException
                for task_e in e.exceptions
                    if task_e isa TaskFailedException
                        println("      Inner: $(task_e.task.result)")
                        bt = task_e.task.backtrace
                        if bt !== nothing
                            for line in stacktrace(bt)[1:min(10,length(stacktrace(bt)))]
                                println("        $line")
                            end
                        end
                    end
                end
            else
                bt = catch_backtrace()
                for line in stacktrace(bt)[1:min(10,length(stacktrace(bt)))]
                    println("      $line")
                end
            end
            continue
        end
        flush(stdout)
    end
catch e
    println("  CRASH: $e")
    bt = catch_backtrace()
    for line in stacktrace(bt)[1:min(15,length(stacktrace(bt)))]
        println("    $line")
    end
end

println("\n" * "="^70)
println("DEBUG COMPLETE")
println("="^70)
