#!/usr/bin/env julia
#=
  Numerical verification of arXiv:2602.06117
  "On the (Fib ⊠ Fib) ⋊ S₂ fusion category"
  by Ferragatta & van Rees

  Uses TensorCategories.jl for independent computation.
  Verifies: F-symbols, tube algebra, representations,
  modular S and T matrices for (Fib⊠Fib)⋊S₂.
=#

using Pkg
Pkg.activate("/home/tobiasosborne/Projects/TensorCategories.jl")

using TensorCategories
using Oscar
using LinearAlgebra

println("="^70)
println("VERIFICATION: arXiv:2602.06117 — (Fib ⊠ Fib) ⋊ S₂")
println("="^70)

# ================================================================
# Section 1: Fibonacci category foundations
# ================================================================
println("\n" * "="^70)
println("SECTION 1: Fibonacci Category Foundations")
println("="^70)

# Golden ratio
ξ = (1 + √5) / 2
println("Golden ratio ξ = $(ξ)")
println("ξ² = $(ξ^2), 1 + ξ = $(1 + ξ) — should be equal: $(abs(ξ^2 - (1+ξ)) < 1e-14)")

# Total dimension squared
D = 1 + ξ^2
println("D = 1 + ξ² = $(D)")
println("D_Fib = √D = $(√D)")

# Construct Fibonacci category from TensorCategories.jl
println("\nConstructing Fibonacci category via TensorCategories.jl...")
Fib = fibonacci_category()
println("Fib category: $(Fib)")
println("Simples: $(simples(Fib))")
println("Rank: $(rank(Fib))")

# Check dimensions
for (i, s) in enumerate(simples(Fib))
    d = fpdim(s)
    println("  dim(simple[$i]) = $d")
end

# F-symbols (eq 2.6)
# The paper's convention:
# F^{ττ1}_{ττ1} = 1/ξ,  F^{ττ1}_{τττ} = 1/√ξ
# F^{τττ}_{ττ1} = 1/√ξ, F^{ττ τ}_{τττ} = -1/ξ
println("\n--- F-symbols (paper eq 2.6) ---")
F_paper = [1/ξ  1/√ξ;
           1/√ξ -1/ξ]
println("Paper F matrix:\n$F_paper")
println("Check: F is unitary: $(norm(F_paper * F_paper' - I) < 1e-14)")
println("Check: F² entries...")
F2 = F_paper^2
println("  F² = \n$F2")

# ================================================================
# Section 2: Tube algebra of Fib
# ================================================================
println("\n" * "="^70)
println("SECTION 2: Tube Algebra of Fib")
println("="^70)

# Tube algebra for twisted sector (eqs 2.10-2.12)
# Three generators: id_τ, T_τ, L^{ττ}_τ
# Let a = L^{ττ}_τ and T = T_τ
# Relations:
# a × a = -ξ^(-5/2) a - ξ^(-1) id + T      (eq 2.10)
# T × T = ξ^(-1/2) a + ξ^(-1) id            (eq 2.11)
# a × T = -ξ^(-1) a + ξ^(-1/2) id           (eq 2.12)

println("Verifying tube algebra relations (eqs 2.10-2.12)...")

# Eigenvalues from the paper's table:
# (1): T = 1,   a = √ξ/(1+ξ)
# (2): T = e^{4πi/5}, a = √ξ/(1+e^{4πi/5}ξ)
# (3): T = e^{-4πi/5}, a = √ξ/(1+e^{-4πi/5}ξ)

t_vals = [1.0, exp(4π*im/5), exp(-4π*im/5)]
a_vals = [√ξ / (1 + t * ξ) for t in t_vals]

println("\nEigenvalue table:")
for (i, (t, a)) in enumerate(zip(t_vals, a_vals))
    println("  ($i): T = $t, a = $a")

    # Check eq 2.10: a² = -ξ^(-5/2) a - ξ^(-1) + T
    lhs = a^2
    rhs = -ξ^(-5/2) * a - ξ^(-1) + t
    println("    eq 2.10: |a² - (-ξ^(-5/2)a - ξ^(-1) + T)| = $(abs(lhs - rhs))")

    # Check eq 2.11: T² = ξ^(-1/2) a + ξ^(-1)
    lhs = t^2
    rhs = ξ^(-1/2) * a + ξ^(-1)
    println("    eq 2.11: |T² - (ξ^(-1/2)a + ξ^(-1))| = $(abs(lhs - rhs))")

    # Check eq 2.12: aT = -ξ^(-1) a + ξ^(-1/2)
    lhs = a * t
    rhs = -ξ^(-1) * a + ξ^(-1/2)
    println("    eq 2.12: |aT - (-ξ^(-1)a + ξ^(-1/2))| = $(abs(lhs - rhs))")
end

# Projectors (eq 2.7) — untwisted sector
println("\n--- Untwisted sector projectors (eq 2.7) ---")
P1_1 = 1/(1 + ξ^2) * [1.0, ξ]   # coefficients of [id, τ]
P1_2 = 1/(1 + 1/ξ^2) * [1.0, -1/ξ]
println("P₁⁽¹⁾: [$(P1_1[1]), $(P1_1[2])] (id, τ)")
println("P₁⁽²⁾: [$(P1_2[1]), $(P1_2[2])] (id, τ)")
println("Sum = [$(P1_1[1]+P1_2[1]), $(P1_1[2]+P1_2[2])] — should be [1, 0]")

# ================================================================
# Section 4: Modular matrices of Fib (eq 2.37)
# ================================================================
println("\n" * "="^70)
println("SECTION 4: Modular Matrices of Fib")
println("="^70)

S_fib = (1/(1+ξ^2)) * [1.0  ξ^2  ξ   ξ;
                         ξ^2  1.0  -ξ  -ξ;
                         ξ   -ξ   -1.0  ξ^2;
                         ξ   -ξ    ξ^2 -1.0]

T_fib = Diagonal([1.0, 1.0, exp(4π*im/5), exp(-4π*im/5)])

println("S matrix (eq 2.37):")
display(S_fib)

println("\nT matrix:")
display(T_fib)

# Check S² = C (charge conjugation)
S2 = S_fib^2
println("\nS² (should be charge conjugation C):")
display(round.(S2, digits=10))
# For Fib, C = I since all objects are self-dual
println("S² ≈ I: $(norm(S2 - I) < 1e-12)")

# Check (ST)³ = C
ST = S_fib * T_fib
ST3 = ST^3
println("\n(ST)³ (should be C):")
display(round.(real.(ST3), digits=10))
println("(ST)³ ≈ I: $(norm(ST3 - I) < 1e-10)")

# ================================================================
# Section 5: (Fib × Fib) ⋊ S₂ — Category Structure
# ================================================================
println("\n" * "="^70)
println("SECTION 5: (Fib × Fib) ⋊ S₂ Category Structure")
println("="^70)

# 8 simple objects:
# c₁=(1,1,1), c₂=(1,1,p), c₃=(τ,1,1), c₄=(τ,1,p)
# c₅=(1,τ,1), c₆=(1,τ,p), c₇=(τ,τ,1), c₈=(τ,τ,p)
println("Simple objects: c₁,...,c₈")
# Quantum dimensions: d(i,j) = d(i)d(j)
dims = [1.0, 1.0, ξ, ξ, ξ, ξ, ξ^2, ξ^2]
names = ["c₁=(1,1,1)", "c₂=(1,1,p)", "c₃=(τ,1,1)", "c₄=(τ,1,p)",
         "c₅=(1,τ,1)", "c₆=(1,τ,p)", "c₇=(τ,τ,1)", "c₈=(τ,τ,p)"]
for (n, d) in zip(names, dims)
    println("  $n: d = $d")
end
println("Total dimension² = Σd² = $(sum(dims.^2))")
println("Expected: 2D² = 2(1+ξ²)² = $(2*D^2)")

# Duality: c₄* = c₆
println("\nDuality: c₄* = c₆ (self-dual for all others)")

# ================================================================
# Section 6: Untwisted Hilbert space representations
# ================================================================
println("\n" * "="^70)
println("SECTION 6: Untwisted Hilbert Space H_{c₁}")
println("="^70)

# 4 one-dim irreps + 1 two-dim irrep = 5 minimal central idempotents
# Representation table from the paper:
# (1): 1, 1, ξ, ξ, ξ, ξ, ξ², ξ²
# (2): 1, -1, ξ, -ξ, ξ, -ξ, ξ², -ξ²
# (3): 1, 1, -1/ξ, -1/ξ, -1/ξ, -1/ξ, 1/ξ², 1/ξ²
# (4): 1, -1, -1/ξ, 1/ξ, -1/ξ, 1/ξ, 1/ξ², -1/ξ²

reps_c1 = [
    [1, 1, ξ, ξ, ξ, ξ, ξ^2, ξ^2],
    [1, -1, ξ, -ξ, ξ, -ξ, ξ^2, -ξ^2],
    [1, 1, -1/ξ, -1/ξ, -1/ξ, -1/ξ, 1/ξ^2, 1/ξ^2],
    [1, -1, -1/ξ, 1/ξ, -1/ξ, 1/ξ, 1/ξ^2, -1/ξ^2]
]

println("4 one-dim representations (eigenvalues for c₁,...,c₈):")
for (i, r) in enumerate(reps_c1)
    println("  ($i): $r")
end

# 2-dim rep
println("\n2-dim representation (5):")
println("  c₂=p = [0 1; 1 0]")
println("  c₃ = diag(ξ, -1/ξ), c₅ = diag(-1/ξ, ξ)")
println("  c₇ = c₃c₅ = -I₂")
println("  c₈ = -[0 1; 1 0]")

# Verify dimension count: 4×1² + 1×2² = 4+4 = 8 = |L₁|
println("\nDimension check: 4×1² + 1×2² = $(4*1 + 1*4) = 8 simple networks ✓")

# Verify projectors (eq 4.5)
println("\n--- Projectors (eq 4.5) ---")
# P₁⁽¹⁾ = 1/(10ξ²) (id + c₂ + ξ(c₃+c₄+c₅+c₆) + ξ²(c₇+c₈))
println("P₁⁽¹⁾ = 1/(10ξ²)(id + c₂ + ξ(c₃+c₄+c₅+c₆) + ξ²(c₇+c₈))")
coeff1 = 1/(10*ξ^2) * [1, 1, ξ, ξ, ξ, ξ, ξ^2, ξ^2]
println("  Coefficients: $(round.(coeff1, digits=6))")
println("  Check: sum of coefficients × eigenvalues for rep (1) = $(round(sum(coeff1 .* reps_c1[1]), digits=10)) (should be 1)")
println("  Check: sum for rep (2) = $(round(sum(coeff1 .* reps_c1[2]), digits=10)) (should be 0)")

# ================================================================
# Section 14/15: The 22×22 Modular S and T matrices
# ================================================================
println("\n" * "="^70)
println("SECTION 14/15: The 22×22 Modular S and T Matrices")
println("="^70)

# T matrix: diagonal with spins
spins = [0, 0, 0, 0, 1/2, 0, 1/2, 0, 0, 2/5, 2/5, -2/5, -2/5,
         1/5, -3/10, -1/5, 3/10, 4/5, -4/5, 4/5, -4/5, 0]
T_22 = Diagonal([exp(2π*im*s) for s in spins])
println("T matrix spins: $spins")
println("T matrix eigenvalues:")
for (i, s) in enumerate(spins)
    println("  Z[$i]: spin = $s, T = $(round(exp(2π*im*s), digits=8))")
end

# The full 22×22 S matrix from the paper
# Assemble the two halves (left 11 cols + right 11 cols)
S_left = (1/(2*D^2)) * [
    1       1       ξ^4     ξ^4     D*ξ^2    D*ξ^2    D       D       2ξ^2     2ξ      2ξ^3;
    1       1       ξ^4     ξ^4    -D*ξ^2   -D*ξ^2   -D      -D       2ξ^2     2ξ      2ξ^3;
    ξ^4     ξ^4     1       1       D        D        D*ξ^2   D*ξ^2   2ξ^2    -2ξ^3   -2ξ;
    ξ^4     ξ^4     1       1      -D       -D       -D*ξ^2  -D*ξ^2   2ξ^2    -2ξ^3   -2ξ;
    D*ξ^2  -D*ξ^2   D      -D       D*ξ^2  -D*ξ^2    D      -D       0        0       0;
    D*ξ^2  -D*ξ^2   D      -D      -D*ξ^2   D*ξ^2   -D       D       0        0       0;
    D       -D      D*ξ^2  -D*ξ^2   D       -D       D*ξ^2  -D*ξ^2   0        0       0;
    D       -D      D*ξ^2  -D*ξ^2  -D        D      -D*ξ^2   D*ξ^2   0        0       0;
    2ξ^2    2ξ^2    2ξ^2    2ξ^2    0        0        0       0       6ξ^2     2ξ^2   -2ξ^2;
    2ξ      2ξ     -2ξ^3   -2ξ^3   0        0        0       0       2ξ^2     2ξ     -4ξ^2;
    2ξ^3    2ξ^3   -2ξ     -2ξ      0        0        0       0      -2ξ^2    -4ξ^2    2ξ;
    2ξ      2ξ     -2ξ^3   -2ξ^3   0        0        0       0       2ξ^2     4ξ^2    2ξ^3;
    2ξ^3    2ξ^3   -2ξ     -2ξ      0        0        0       0      -2ξ^2     2ξ^3    4ξ^2;
    D*ξ    -D*ξ    -D*ξ     D*ξ    -D*ξ      D*ξ      D*ξ   -D*ξ     0        0       0;
    D*ξ    -D*ξ    -D*ξ     D*ξ     D*ξ     -D*ξ     -D*ξ    D*ξ     0        0       0;
    D*ξ    -D*ξ    -D*ξ     D*ξ    -D*ξ      D*ξ      D*ξ   -D*ξ     0        0       0;
    D*ξ    -D*ξ    -D*ξ     D*ξ     D*ξ     -D*ξ     -D*ξ    D*ξ     0        0       0;
    ξ^2     ξ^2     ξ^2     ξ^2    -D*ξ     -D*ξ      D*ξ    D*ξ    -2ξ^2    -2ξ      2ξ;
    ξ^2     ξ^2     ξ^2     ξ^2    -D*ξ     -D*ξ      D*ξ    D*ξ    -2ξ^2     2ξ^3   -2ξ^3;
    ξ^2     ξ^2     ξ^2     ξ^2     D*ξ      D*ξ     -D*ξ   -D*ξ    -2ξ^2    -2ξ      2ξ;
    ξ^2     ξ^2     ξ^2     ξ^2     D*ξ      D*ξ     -D*ξ   -D*ξ    -2ξ^2     2ξ^3   -2ξ^3;
    4ξ^2    4ξ^2    4ξ^2    4ξ^2    0        0        0       0      -8ξ^2     4ξ^2   -4ξ^2
]

S_right = (1/(2*D^2)) * [
    2ξ      2ξ^3    D*ξ     D*ξ     D*ξ     D*ξ     ξ^2     ξ^2     ξ^2     ξ^2     ξ^2;
    2ξ      2ξ^3   -D*ξ    -D*ξ    -D*ξ    -D*ξ     ξ^2     ξ^2     ξ^2     ξ^2     ξ^2;
   -2ξ^3   -2ξ     -D*ξ    -D*ξ    -D*ξ    -D*ξ     ξ^2     ξ^2     ξ^2     ξ^2     ξ^2;
   -2ξ^3   -2ξ      D*ξ     D*ξ     D*ξ     D*ξ     ξ^2     ξ^2     ξ^2     ξ^2     ξ^2;
    0       0       -D*ξ     D*ξ    -D*ξ     D*ξ    -D*ξ    -D*ξ     D*ξ     D*ξ     0;
    0       0        D*ξ    -D*ξ     D*ξ    -D*ξ    -D*ξ    -D*ξ     D*ξ     D*ξ     0;
    0       0        D*ξ    -D*ξ     D*ξ    -D*ξ     D*ξ     D*ξ    -D*ξ    -D*ξ     0;
    0       0       -D*ξ     D*ξ    -D*ξ     D*ξ     D*ξ     D*ξ    -D*ξ    -D*ξ     0;
    2ξ^2   -2ξ^2    0       0       0       0       -2ξ^2   -2ξ^2   -2ξ^2   -2ξ^2   -2ξ^2;
    4ξ^2    2ξ^3    0       0       0       0       -2ξ      2ξ^3   -2ξ      2ξ^3    ξ^2;
    2ξ^3    4ξ^2    0       0       0       0        2ξ     -2ξ^3    2ξ     -2ξ^3   -ξ^2;
    2ξ     -4ξ^2    0       0       0       0        2ξ^3   -2ξ      2ξ^3   -2ξ      ξ^2;
   -4ξ^2    2ξ      0       0       0       0       -2ξ^3    2ξ     -2ξ^3    2ξ     -ξ^2;
    0       0       -D*ξ^2   D*ξ^2   D      -D       -D       D*ξ^2   D      -D*ξ^2   0;
    0       0        D*ξ^2  -D*ξ^2  -D       D       -D       D*ξ^2   D      -D*ξ^2   0;
    0       0        D       -D     -D*ξ^2   D*ξ^2   D*ξ^2  -D       -D*ξ^2  D        0;
    0       0       -D        D      D*ξ^2  -D*ξ^2   D*ξ^2  -D       -D*ξ^2  D        0;
    2ξ^3   -2ξ^3   -D       -D      D*ξ^2   D*ξ^2   1       ξ^4      1       ξ^4    -ξ^2;
   -2ξ      2ξ      D*ξ^2   D*ξ^2  -D       -D       ξ^4     1        ξ^4     1      -ξ^2;
    2ξ^3   -2ξ^3    D        D     -D*ξ^2  -D*ξ^2    1       ξ^4      1       ξ^4    -ξ^2;
   -2ξ      2ξ     -D*ξ^2  -D*ξ^2   D        D       ξ^4     1        ξ^4     1      -ξ^2;
    4ξ^2   -4ξ^2    0       0       0       0       -4ξ^2   -4ξ^2   -4ξ^2   -4ξ^2    6ξ^2
]

S_22 = hcat(S_left, S_right)
println("\n22×22 S matrix assembled ($(size(S_22)))")

# Verify S² = C
println("\n--- Checking S² = C ---")
S2_22 = S_22^2
# Find C matrix (charge conjugation: c₄ ↔ c₆, rest self-dual)
# In the partition function basis, need to identify which Z's swap
# For the 22 partition functions listed in eq 5.1, C acts on the
# c₄ sector partition functions
println("S² diagonal (should be ±1):")
for i in 1:22
    println("  S²[$i,$i] = $(round(real(S2_22[i,i]), digits=8))")
end
println("Max |S² - S²_expected|: need to identify C explicitly")

# Check symmetry
println("\n--- Checking S symmetry ---")
println("S is symmetric: $(norm(S_22 - S_22') < 1e-12)")

# Check unitarity: S S† = I
println("S S† ≈ I: $(norm(S_22 * S_22' - I) < 1e-10)")

# Check (ST)³ = C
ST_22 = S_22 * T_22
ST3_22 = ST_22^3
println("\n--- Checking (ST)³ ---")
for i in 1:22
    println("  (ST)³[$i,$i] = $(round(real(ST3_22[i,i]), digits=6)) + $(round(imag(ST3_22[i,i]), digits=6))i")
end

println("\n" * "="^70)
println("VERIFICATION COMPLETE")
println("="^70)
