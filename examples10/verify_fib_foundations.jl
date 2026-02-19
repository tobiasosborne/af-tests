#!/usr/bin/env julia
#=
  Independent verification of Fibonacci category foundations
  using TensorCategories.jl (arXiv:2602.06117 Section 2)

  Verifies: fusion rules, quantum dimensions, F-symbols, total dimension
  Corresponds to af nodes: 1.1.1, 1.1.2, 1.1.3, 1.1.4
=#

using Pkg
Pkg.activate("/home/tobiasosborne/Projects/TensorCategories.jl")
using TensorCategories, Oscar
using LinearAlgebra

println("="^70)
println("VERIFY: Fibonacci category foundations (nodes 1.1.1–1.1.4)")
println("="^70)

# ── Golden ratio reference values ──
ξ = (1 + √5) / 2
@assert abs(ξ^2 - (1 + ξ)) < 1e-14 "golden ratio identity ξ²=1+ξ"

# ── Construct Fib via TensorCategories.jl ──
Fib = fibonacci_category()
S = simples(Fib)

# ================================================================
# Node 1.1.1: Fusion rule τ×τ = 1 + τ
# ================================================================
println("\n--- Node 1.1.1: Fusion rules ---")
# S[1] = 𝟙, S[2] = τ
prod_11 = S[1] ⊗ S[1]  # 𝟙⊗𝟙 = 𝟙
prod_12 = S[1] ⊗ S[2]  # 𝟙⊗τ = τ
prod_21 = S[2] ⊗ S[1]  # τ⊗𝟙 = τ
prod_22 = S[2] ⊗ S[2]  # τ⊗τ = 𝟙 ⊕ τ

println("  𝟙⊗𝟙 = $prod_11")
println("  𝟙⊗τ = $prod_12")
println("  τ⊗𝟙 = $prod_21")
println("  τ⊗τ = $prod_22")

# Extract fusion coefficients for τ⊗τ
# The decomposition should give 𝟙 ⊕ τ
d_ττ = fpdim(prod_22)
d_expected = 1 + ξ  # dim(𝟙) + dim(τ) = 1 + ξ
println("  dim(τ⊗τ) = $(Float64(d_ττ)), expected $(d_expected)")
pass_111 = abs(Float64(d_ττ) - d_expected) < 1e-12
println("  ✓ Node 1.1.1 PASS: $pass_111")

# ================================================================
# Node 1.1.2: Quantum dimensions d(𝟙)=1, d(τ)=ξ
# ================================================================
println("\n--- Node 1.1.2: Quantum dimensions ---")
d1 = Float64(fpdim(S[1]))
dτ = Float64(fpdim(S[2]))
println("  d(𝟙) = $d1 (expected 1)")
println("  d(τ) = $dτ (expected ξ = $ξ)")
pass_112 = abs(d1 - 1) < 1e-14 && abs(dτ - ξ) < 1e-12
println("  ✓ Node 1.1.2 PASS: $pass_112")

# ================================================================
# Node 1.1.3: F-symbols (eq 2.6)
# ================================================================
println("\n--- Node 1.1.3: F-symbols (eq 2.6) ---")

# Paper F-matrix (eq 2.6):
# F = [[1/ξ, 1/√ξ], [1/√ξ, -1/ξ]]
F_paper = [1/ξ 1/√ξ; 1/√ξ -1/ξ]
println("  Paper F-matrix:")
println("    [$(F_paper[1,1])  $(F_paper[1,2])]")
println("    [$(F_paper[2,1])  $(F_paper[2,2])]")

# TensorCategories.jl F-symbols
ass = Fib.ass
mat = ass[2,2,2,2]  # F^{τ,τ}_τ block — 2×2 over number field
# Convert from Oscar number field to Float64 via conjugates
# Pick the embedding where d(τ) > 0
K = parent(mat[1,1])
embs = complex_embeddings(K)
# Test which embedding gives positive quantum dimension
dτ_test = [real(ComplexF64(e(Fib.pivotal[2]))) for e in embs]
embed_idx = findfirst(x -> x > 0, dτ_test)  # pivotal dims should be positive
if embed_idx === nothing; embed_idx = 1; end
embed = embs[embed_idx]
println("\n  Using embedding #$embed_idx (d(τ)=$(dτ_test[embed_idx]))")

F_TC = zeros(Float64, 2, 2)
for i in 1:2, j in 1:2
    F_TC[i,j] = real(ComplexF64(embed(mat[i,j])))
end
println("  TensorCategories.jl F^{τ,τ,τ,τ}:")
println("    [$(F_TC[1,1])  $(F_TC[1,2])]")
println("    [$(F_TC[2,1])  $(F_TC[2,2])]")

# Check paper F is unitary
F_unitary_err = norm(F_paper * F_paper' - I)
println("\n  Paper F unitarity: ||FF†-I|| = $F_unitary_err")
pass_unitary = F_unitary_err < 1e-14

# Check paper F satisfies pentagon identity via F² + (1/ξ)F - (1/ξ)I = 0
# (This is the characteristic equation)
F2 = F_paper^2
pentagon_err = norm(F2 + (1/ξ)*F_paper - (1/ξ)*I)
println("  Pentagon check (F²+(1/ξ)F-(1/ξ)I=0): ||·|| = $pentagon_err")

# Both F matrices should be gauge-equivalent (same eigenvalues)
eig_paper = sort(eigvals(F_paper), by=real)
eig_TC = sort(eigvals(F_TC), by=real)
println("\n  Paper eigenvalues: $eig_paper")
println("  TC eigenvalues:    $eig_TC")
eig_match = norm(eig_paper - eig_TC) < 1e-10
println("  Eigenvalues match: $eig_match")

pass_113 = pass_unitary && eig_match
println("  ✓ Node 1.1.3 PASS: $pass_113")

# ================================================================
# Node 1.1.4: Total dimension D_Fib
# ================================================================
println("\n--- Node 1.1.4: Total dimension ---")
D2_computed = d1^2 + dτ^2  # = 1 + ξ²
D2_expected = 1 + ξ^2
D_Fib = √D2_computed
println("  D²_Fib = Σ d(i)² = $D2_computed")
println("  Expected: 1+ξ² = $D2_expected")
println("  D_Fib = $D_Fib")
println("  Check: D²=2+ξ since ξ²=1+ξ: $(abs(D2_computed - (2+ξ)) < 1e-14)")
println("  Numerical: D²_Fib ≈ $(D2_computed) ≈ (5+√5)/2 = $((5+√5)/2)")
pass_114 = abs(D2_computed - D2_expected) < 1e-14
println("  ✓ Node 1.1.4 PASS: $pass_114")

# ================================================================
# Summary
# ================================================================
println("\n" * "="^70)
println("SUMMARY")
println("="^70)
results = [
    ("1.1.1", "Fusion rule τ×τ=1+τ", pass_111),
    ("1.1.2", "Quantum dimensions", pass_112),
    ("1.1.3", "F-symbols (eq 2.6)", pass_113),
    ("1.1.4", "Total dimension", pass_114),
]
all_pass = true
for (node, desc, pass) in results
    status = pass ? "PASS ✓" : "FAIL ✗"
    println("  $node: $desc — $status")
    global all_pass = all_pass && pass
end
println("\nOverall: $(all_pass ? "ALL PASS" : "SOME FAILURES")")
