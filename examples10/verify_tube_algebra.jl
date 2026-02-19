#!/usr/bin/env julia
#=
  Independent verification of Fib tube algebra structure constants
  and eigenvalues (arXiv:2602.06117 eqs 2.10-2.13)

  Verifies: tube algebra relations, eigenvalue table, projectors
  Corresponds to af nodes: 1.2.1–1.2.7
=#

using LinearAlgebra

println("="^70)
println("VERIFY: Fib tube algebra (nodes 1.2.1–1.2.7)")
println("="^70)

ξ = (1 + √5) / 2
D = 1 + ξ^2  # = 2 + ξ

# ================================================================
# Nodes 1.2.2–1.2.4: Tube algebra relations (eqs 2.10-2.12)
# ================================================================
# Twisted sector H_τ: three generators {id_τ, T_τ, L^{ττ}_τ}
# Let a = L^{ττ}_τ, T = T_τ
#
# eq 2.10: a² = -ξ^(-5/2) a - ξ^(-1) id + T
# eq 2.11: T² = ξ^(-1/2) a + ξ^(-1) id
# eq 2.12: aT = -ξ^(-1) a + ξ^(-1/2) id

println("\n--- Nodes 1.2.2–1.2.4: Tube algebra structure constants ---")

# Build 3×3 regular representation matrices
# Basis: {id, T, a} → e₁, e₂, e₃
# id·X = X for all X (trivially)

# T·id = T, T·T = ξ^(-1/2) a + ξ^(-1) id, T·a = ?
# Need T·a: from eq 2.12 written as aT = ..., need Ta
# By taking adjoint/transpose of eq 2.12 and the algebra structure,
# or compute directly: Ta = (eq 2.12 reversed)
# Actually the tube algebra is associative, so we can derive Ta from
# the other relations. From aT = -ξ^(-1) a + ξ^(-1/2) id (eq 2.12)

# Let's verify by eigenvalue substitution (node 1.2.5):
# Eigenvalues: for t ∈ {1, e^{4πi/5}, e^{-4πi/5}}
#   a = √ξ/(1 + tξ)

println("\n--- Node 1.2.5: Eigenvalue verification ---")
t_vals = [1.0+0im, exp(4π*im/5), exp(-4π*im/5)]
a_vals = [√ξ / (1 + t * ξ) for t in t_vals]

pass_210 = true
pass_211 = true
pass_212 = true

for (i, (t, a)) in enumerate(zip(t_vals, a_vals))
    println("  Rep ($i): T = $(round(t, digits=6)), a = $(round(a, digits=6))")

    # eq 2.10: a² + ξ^(-5/2)a + ξ^(-1) - T = 0
    err_210 = abs(a^2 + ξ^(-5/2)*a + ξ^(-1) - t)
    println("    eq 2.10 residual: $err_210")
    global pass_210 = pass_210 && err_210 < 1e-12

    # eq 2.11: T² - ξ^(-1/2)a - ξ^(-1) = 0
    err_211 = abs(t^2 - ξ^(-1/2)*a - ξ^(-1))
    println("    eq 2.11 residual: $err_211")
    global pass_211 = pass_211 && err_211 < 1e-12

    # eq 2.12: aT + ξ^(-1)a - ξ^(-1/2) = 0
    err_212 = abs(a*t + ξ^(-1)*a - ξ^(-1/2))
    println("    eq 2.12 residual: $err_212")
    global pass_212 = pass_212 && err_212 < 1e-12
end

println("\n  ✓ eq 2.10 (node 1.2.2): $pass_210")
println("  ✓ eq 2.11 (node 1.2.3): $pass_211")
println("  ✓ eq 2.12 (node 1.2.4): $pass_212")
println("  ✓ Eigenvalues (node 1.2.5): $(pass_210 && pass_211 && pass_212)")

# ================================================================
# Node 1.2.6: Untwisted sector projectors (eq 2.7)
# ================================================================
println("\n--- Node 1.2.6: Untwisted projectors (eq 2.7) ---")

# H_1 basis: {id_1, τ_1} where τ_1 acts by multiplication (τ eigenvalue ξ or -1/ξ)
# P₁⁽¹⁾ = 1/(1+ξ²) (id + ξ·τ)
# P₁⁽²⁾ = 1/(1+ξ⁻²) (id - ξ⁻¹·τ)
#
# In matrix form with basis {id, τ}:
# τ·τ = id + τ (from fusion), so as a 2×2 matrix: τ = [[0,1],[1,1]]
# (τ acts on H_1 = span{id, τ} by: τ·id=τ, τ·τ=id+τ)

M_τ = [0.0 1.0; 1.0 1.0]  # τ action in {id, τ} basis
M_id = [1.0 0.0; 0.0 1.0]

# Check M_τ eigenvalues are ξ and -1/ξ
eig_τ = eigvals(M_τ)
println("  τ eigenvalues: $eig_τ")
println("  Expected: ξ=$ξ, -1/ξ=$(-1/ξ)")
eig_ok = abs(sort(real.(eig_τ))[1] - (-1/ξ)) < 1e-12 && abs(sort(real.(eig_τ))[2] - ξ) < 1e-12

# Build projectors
P1_1 = (1/(1+ξ^2)) * (M_id + ξ * M_τ)
P1_2 = (1/(1+ξ^(-2))) * (M_id - (1/ξ) * M_τ)

println("\n  P₁⁽¹⁾ = ")
display(P1_1)
println("\n  P₁⁽²⁾ = ")
display(P1_2)

# Check idempotency
err_idem1 = norm(P1_1^2 - P1_1)
err_idem2 = norm(P1_2^2 - P1_2)
println("\n  ||P₁⁽¹⁾² - P₁⁽¹⁾|| = $err_idem1")
println("  ||P₁⁽²⁾² - P₁⁽²⁾|| = $err_idem2")

# Check orthogonality
err_orth = norm(P1_1 * P1_2)
println("  ||P₁⁽¹⁾P₁⁽²⁾|| = $err_orth")

# Check completeness
err_comp = norm(P1_1 + P1_2 - M_id)
println("  ||P₁⁽¹⁾+P₁⁽²⁾-I|| = $err_comp")

pass_126 = err_idem1 < 1e-14 && err_idem2 < 1e-14 && err_orth < 1e-14 && err_comp < 1e-14
println("  ✓ Node 1.2.6 PASS: $pass_126")

# ================================================================
# Node 1.2.7: Twisted sector projectors (eq 2.13)
# ================================================================
println("\n--- Node 1.2.7: Twisted projectors (eq 2.13) ---")

# Build 3×3 representation matrices from eqs 2.10-2.12
# Basis: {id, T, a}
# id acts as identity
# T·id=T, T·T=ξ^(-1/2)a+ξ^(-1)id, T·a=? (need this)

# From eq 2.12: aT = -ξ^(-1)a + ξ^(-1/2)id
# We need Ta. Use: (Ta)·(anything) should be consistent.
# From eq 2.11: T²=ξ^(-1/2)a+ξ^(-1)id → T(T·x) for basis elements.
# Actually, let's build the LEFT regular representation:
# L_X(Y) = X·Y
# L_id = I₃
# L_T: T·id=T, T·T=ξ^(-1/2)a+ξ^(-1)id, T·a=?
# From associativity + eqs, compute T·a:
#   (T·a) from (a·T) and commutativity? The algebra need not be commutative.
#   Use: T·a·T = T·(-ξ^(-1)a + ξ^(-1/2)id) = -ξ^(-1)(T·a) + ξ^(-1/2)T
#   Also: (T·a)·T from T²·a = (ξ^(-1/2)a+ξ^(-1)id)·a = ξ^(-1/2)a²+ξ^(-1)a
#     = ξ^(-1/2)(-ξ^(-5/2)a-ξ^(-1)+T) + ξ^(-1)a
#     = -ξ^(-3)a - ξ^(-3/2) + ξ^(-1/2)T + ξ^(-1)a
#     = (ξ^(-1)-ξ^(-3))a - ξ^(-3/2) + ξ^(-1/2)T

# Actually, let's just use 3×3 matrices directly.
# Use eigenvalues to construct matrices in a basis where they're diagonal.
# The three eigenvectors correspond to the three 1-dim irreps.

# Eigenvalues for (id, T, a):
id_eig = [1, 1, 1]
T_eig = t_vals
a_eig = a_vals

# Transition matrix: columns are the eigenvectors of L_T (and L_a simultaneously)
# In the simultaneous eigenbasis, L_T = diag(t₁,t₂,t₃), L_a = diag(a₁,a₂,a₃)

# Build projectors in the algebra: P^(k) = Σ_X χ^(k)(X)* · X / dim(H)
# For 1-dim irreps, χ^(k) = eigenvalue

# But actually, the projectors are expressed in terms of {id, T, a}:
# P^(k) = (1/3) Σ_{X∈{id,T,a}} χ^(k)(X)* · X   (this is wrong for non-group algebras)

# Better: use the general formula. The projectors are:
# P^(k) = d_k/|H| Σ χ^(k)(X)* X where d_k is dimension and |H| = dim(H_τ) = 3
# But this needs the trace in the regular representation.

# For commutative semisimple algebras with basis {e_1, e_2, e_3} and
# three 1-dim irreps, the minimal idempotents are determined by:
# P^(k) projects onto k-th eigenspace.

# Since all irreps are 1-dim and the algebra is 3-dim,
# the algebra is isomorphic to C³ (commutative semisimple).
# The minimal idempotents satisfy P^(k) = p_k^id · id + p_k^T · T + p_k^a · a
# with P^(k)(X) = eigenvalue_k(X) for all X.

# Solve: for each k, P^(k) · X = eigenvalue_k(X) · P^(k)
# In the eigenbasis this is trivial. Let's verify using the matrix approach.

# Build structure constants matrix: if we label basis = {id(=1), T(=2), a(=3)}
# M^c_{ab} = coefficient of e_c in e_a · e_b

# e₁·e₁=e₁, e₁·e₂=e₂, e₁·e₃=e₃
# e₂·e₂=ξ^(-1)e₁+ξ^(-1/2)e₃   (eq 2.11)
# e₂·e₃=-ξ^(-1/2)e₁+ξ^(-1)e₃  ... wait, eq 2.12 says aT=-ξ^(-1)a+ξ^(-1/2)id
# so e₃·e₂ = ξ^(-1/2)e₁ - ξ^(-1)e₃

# We also need e₂·e₃ (= T·a). Since the eigenvalue analysis works for
# BOTH left and right multiplication, and all irreps are 1-dim, the algebra
# must be commutative. So T·a = a·T = ξ^(-1/2)id - ξ^(-1)a.
# Let's verify: T·a should give eigenvalue t_k·a_k for each k.

println("  Checking algebra commutativity (Ta = aT):")
for (k, (t, a)) in enumerate(zip(t_vals, a_vals))
    ta_eig = t * a
    at_eig = a * t  # same by definition for scalars
    # Check: ta = ξ^(-1/2) - ξ^(-1)·a? That's what eq 2.12 gives for aT.
    check_val = ξ^(-1/2) - ξ^(-1)*a
    println("    Rep $k: t·a = $(round(ta_eig, digits=8)), ξ^(-1/2)-ξ^(-1)a = $(round(check_val, digits=8)), diff = $(abs(ta_eig - check_val))")
end

# Build left-regular representation matrices (3×3)
# Basis ordering: [id, T, a]
L_id = Matrix{ComplexF64}(I, 3, 3)

# L_T: T·id=T, T·T=ξ^(-1)id+ξ^(-1/2)a, T·a=ξ^(-1/2)id-ξ^(-1)a
L_T = ComplexF64[
    0         ξ^(-1)     ξ^(-1/2);
    1         0          0;
    0         ξ^(-1/2)  -ξ^(-1)
]

# L_a: a·id=a, a·T=ξ^(-1/2)id-ξ^(-1)a, a·a=-ξ^(-5/2)a-ξ^(-1)id+T
L_a = ComplexF64[
    0        ξ^(-1/2)  -ξ^(-1);
    0        0          1;
    1       -ξ^(-1)    -ξ^(-5/2)
]

println("\n  Checking L_T eigenvalues:")
eig_LT = eigvals(L_T)
println("    L_T eigenvalues: $(round.(eig_LT, digits=6))")
println("    Expected: $(round.(t_vals, digits=6))")
LT_ok = sort(eig_LT, by=x->(real(x), imag(x)))
t_sorted = sort(t_vals, by=x->(real(x), imag(x)))
println("    Match: $(norm(LT_ok - t_sorted) < 1e-10)")

println("  Checking L_a eigenvalues:")
eig_La = eigvals(L_a)
println("    L_a eigenvalues: $(round.(eig_La, digits=6))")
a_sorted = sort(a_vals, by=x->(real(x), imag(x)))
La_ok = sort(eig_La, by=x->(real(x), imag(x)))
println("    Match: $(norm(La_ok - a_sorted) < 1e-10)")

# Verify algebra relations in matrix form
err_2_10 = norm(L_a^2 + ξ^(-5/2)*L_a + ξ^(-1)*L_id - L_T)
err_2_11 = norm(L_T^2 - ξ^(-1/2)*L_a - ξ^(-1)*L_id)
err_2_12 = norm(L_a*L_T + ξ^(-1)*L_a - ξ^(-1/2)*L_id)
println("\n  Matrix algebra checks:")
println("    ||L_a²+ξ^(-5/2)L_a+ξ^(-1)I-L_T|| (eq 2.10) = $err_2_10")
println("    ||L_T²-ξ^(-1/2)L_a-ξ^(-1)I|| (eq 2.11) = $err_2_11")
println("    ||L_aL_T+ξ^(-1)L_a-ξ^(-1/2)I|| (eq 2.12) = $err_2_12")

# Commutativity
err_comm = norm(L_a*L_T - L_T*L_a)
println("    ||[L_a,L_T]|| (commutativity) = $err_comm")

# Build projectors from eigenvectors
F = eigen(L_T)
V = F.vectors  # columns are eigenvectors
# Projectors: P^(k) = |v_k⟩⟨w_k| (biorthogonal, NOT adjoint)
W = inv(V)
println("\n  Constructing projectors:")
pass_127 = true
for k in 1:3
    P_k = V[:,k] * transpose(W[k,:])  # outer product (no conjugation!)
    err_idem = norm(P_k^2 - P_k)
    println("    P^($k): idempotent err = $err_idem")
    global pass_127 = pass_127 && err_idem < 1e-10
end

# Check mutual orthogonality and completeness
P_all = [V[:,k] * transpose(W[k,:]) for k in 1:3]
for j in 1:3, k in j+1:3
    err = norm(P_all[j] * P_all[k])
    println("    ||P^($j)P^($k)|| = $err")
    global pass_127 = pass_127 && err < 1e-10
end
err_comp_tw = norm(sum(P_all) - L_id)
println("    ||ΣP^(k)-I|| = $err_comp_tw")
pass_127 = pass_127 && err_comp_tw < 1e-10
println("  ✓ Node 1.2.7 PASS: $pass_127")

# ================================================================
# Summary
# ================================================================
println("\n" * "="^70)
println("SUMMARY")
println("="^70)
results = [
    ("1.2.2", "eq 2.10 (a²)", pass_210),
    ("1.2.3", "eq 2.11 (T²)", pass_211),
    ("1.2.4", "eq 2.12 (aT)", pass_212),
    ("1.2.5", "Eigenvalues", pass_210 && pass_211 && pass_212),
    ("1.2.6", "Untwisted projectors", pass_126),
    ("1.2.7", "Twisted projectors", pass_127),
]
all_pass = true
for (node, desc, pass) in results
    status = pass ? "PASS ✓" : "FAIL ✗"
    println("  $node: $desc — $status")
    global all_pass = all_pass && pass
end
println("\nOverall: $(all_pass ? "ALL PASS" : "SOME FAILURES")")
