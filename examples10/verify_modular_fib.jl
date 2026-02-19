#!/usr/bin/env julia
#=
  Independent verification of Fib modular S and T matrices
  (arXiv:2602.06117 eq 2.37 and surrounding)

  Verifies: 4×4 S matrix, T matrix, S²=C, (ST)³=C
  Corresponds to af nodes: 1.4.1–1.4.4
=#

using LinearAlgebra

println("="^70)
println("VERIFY: Fib modular matrices (nodes 1.4.1–1.4.4)")
println("="^70)

ξ = (1 + √5) / 2
D = 1 + ξ^2  # D_Fib² = 1+ξ²

# ================================================================
# Node 1.4.1: 4×4 S matrix (eq 2.37)
# ================================================================
println("\n--- Node 1.4.1: S matrix (eq 2.37) ---")

# Partition function ordering: Z₁⁽¹⁾, Z₁⁽²⁾, Z_τ⁽²⁾, Z_τ⁽³⁾
S_fib = (1/D) * [
    1.0   ξ^2   ξ     ξ;
    ξ^2   1.0  -ξ    -ξ;
    ξ    -ξ    -1.0   ξ^2;
    ξ    -ξ     ξ^2  -1.0
]

println("  S = (1/D) × M where D = 1+ξ² = $D")
println("  S matrix:")
for i in 1:4
    println("    [$(join(round.(S_fib[i,:], digits=6), "  "))]")
end

# Check symmetry
err_sym = norm(S_fib - S_fib')
println("\n  Symmetry: ||S-Sᵀ|| = $err_sym")

# Check unitarity
err_unit = norm(S_fib * S_fib' - I)
println("  Unitarity: ||SS†-I|| = $err_unit")

# Check S is real
println("  Real: $(all(isreal, S_fib))")

pass_141 = err_sym < 1e-14 && err_unit < 1e-12
println("  ✓ Node 1.4.1 PASS: $pass_141")

# ================================================================
# Node 1.4.2: T matrix
# ================================================================
println("\n--- Node 1.4.2: T matrix ---")

# T = diag(1, 1, e^{4πi/5}, e^{-4πi/5})
# Spins: 0, 0, 2/5, -2/5
ω = exp(4π*im/5)
T_fib = Diagonal(ComplexF64[1, 1, ω, conj(ω)])

println("  T = diag(1, 1, e^{4πi/5}, e^{-4πi/5})")
println("  Spins: [0, 0, 2/5, -2/5]")
println("  T eigenvalues:")
for i in 1:4
    println("    T[$i,$i] = $(round(T_fib[i,i], digits=8))")
end

# Check T is unitary
err_T_unit = norm(T_fib * T_fib' - I)
println("  Unitarity: ||TT†-I|| = $err_T_unit")

pass_142 = err_T_unit < 1e-14
println("  ✓ Node 1.4.2 PASS: $pass_142")

# ================================================================
# Node 1.4.3: S² = C
# ================================================================
println("\n--- Node 1.4.3: S² = C ---")

# For Fib, all objects are self-dual, so charge conjugation C = I
S2 = S_fib^2
println("  S²:")
for i in 1:4
    println("    [$(join(round.(S2[i,:], digits=10), "  "))]")
end

err_S2 = norm(S2 - I)
println("  ||S²-I|| = $err_S2")

# Also verify key identity used in the proof:
# ξ⁴ + 1 + 2ξ² = (1+ξ²)² = D²
println("\n  Algebraic identity: ξ⁴+1+2ξ² = $(ξ^4+1+2*ξ^2), D² = $(D^2)")
println("  Match: $(abs(ξ^4+1+2*ξ^2 - D^2) < 1e-14)")

pass_143 = err_S2 < 1e-12
println("  ✓ Node 1.4.3 PASS: $pass_143")

# ================================================================
# Node 1.4.4: (ST)³ = C
# ================================================================
println("\n--- Node 1.4.4: (ST)³ = C ---")

ST = S_fib * T_fib
ST3 = ST^3

println("  (ST)³:")
for i in 1:4
    val = round(real(ST3[i,i]), digits=10)
    ival = round(imag(ST3[i,i]), digits=10)
    println("    ($i,$i): $val + $(ival)i")
end

# C = I for Fib (self-dual)
err_ST3 = norm(ST3 - I)
println("  ||(ST)³-I|| = $err_ST3")

# Also check the SL(2,Z) relation: S²=(ST)³ (both = C)
err_relation = norm(S2 - ST3)
println("  ||S²-(ST)³|| = $err_relation")

pass_144 = err_ST3 < 1e-10
println("  ✓ Node 1.4.4 PASS: $pass_144")

# ================================================================
# Extra: Verlinde formula check
# ================================================================
println("\n--- Extra: Verlinde formula ---")
# N^k_{ij} = Σ_m S_{im}S_{jm}S*_{km}/S_{0m}
# For Fib: check N^τ_{ττ} = 1 (fusion coefficient δ_{τ,τ,τ}=1)
# and N^1_{ττ} = 1 (δ_{τ,τ,1}=1)

# But careful: our S matrix is 4×4 (tube algebra), not 2×2 (fusion).
# The Fib fusion S matrix is 2×2:
S_fusion = (1/√D) * [1 ξ; ξ -1]
println("  Fib fusion S matrix (2×2):")
println("    [$(round.(S_fusion[1,:], digits=6))]")
println("    [$(round.(S_fusion[2,:], digits=6))]")

# Verlinde: N^k_{ij} = Σ_m S_{im}S_{jm}S*_{km}/S_{0m}
for i in 1:2, j in 1:2, k in 1:2
    N = sum(S_fusion[i,m]*S_fusion[j,m]*conj(S_fusion[k,m])/S_fusion[1,m] for m in 1:2)
    if abs(round(real(N)) - real(N)) < 1e-10 && abs(real(N)) > 0.5
        name_i = i==1 ? "1" : "τ"
        name_j = j==1 ? "1" : "τ"
        name_k = k==1 ? "1" : "τ"
        println("    N^{$name_k}_{$name_i,$name_j} = $(round(real(N), digits=1))")
    end
end

# ================================================================
# Summary
# ================================================================
println("\n" * "="^70)
println("SUMMARY")
println("="^70)
results = [
    ("1.4.1", "S matrix (eq 2.37)", pass_141),
    ("1.4.2", "T matrix", pass_142),
    ("1.4.3", "S²=C", pass_143),
    ("1.4.4", "(ST)³=C", pass_144),
]
all_pass = true
for (node, desc, pass) in results
    status = pass ? "PASS ✓" : "FAIL ✗"
    println("  $node: $desc — $status")
    global all_pass = all_pass && pass
end
println("\nOverall: $(all_pass ? "ALL PASS" : "SOME FAILURES")")
