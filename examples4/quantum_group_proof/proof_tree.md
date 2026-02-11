# Proof Export

## Node 1

**Statement:** The Biggs-Lin-Maldacena melonic quantum mechanical model (arXiv:2601.08908) admits a consistent quantum group generalization: replacing the SU(2) Wigner 3j coupling coefficients with U_q(su(2)) quantum Clebsch-Gordan coefficients yields a well-defined Hamiltonian H_q = {Q_q, Q_q†} that (1) preserves N=2 supersymmetry and positive semi-definiteness for q > 0 real, (2) exhibits melonic dominance in the large-j limit via quantum 3j orthogonality, (3) admits q-deformed BPS states with degeneracy computable from the q-Witten index, and (4) connects in the large-j semiclassical limit to Turaev-Viro 3D topological invariants (generalizing the Ponzano-Regge connection of the original model).

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

### Node 1.1

**Statement:** PART 1 (Well-definedness and SUSY): The q-deformed supercharge Q_q, constructed by replacing Wigner 3j symbols with quantum 3j symbols of U_q(su(2)) in the BLM supercharge, satisfies (Q_q)^2 = 0 and (Q_q^dagger)^2 = 0 for all q > 0 real. Consequently H_q = {Q_q, Q_q^dagger} is a well-defined, positive semi-definite Hamiltonian with N=2 supersymmetry.

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

#### Node 1.1.1

**Statement:** Step 1.1.1 (Quantum 3j antisymmetry): The quantum 3j symbol C^j_{m1,m2,m3}(q) with all spins equal to j (j odd) is totally antisymmetric under permutations of (m1,m2,m3), i.e., C^j_{sigma(m1,m2,m3)}(q) = sgn(sigma) C^j_{m1,m2,m3}(q). This follows from the quantum Regge symmetries of q-3j symbols and the fact that 3j is odd.

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

#### Node 1.1.2

**Statement:** Step 1.1.2 (Nilpotency Q_q^2 = 0): Since Q_q is a sum of cubic monomials psi_{m1} psi_{m2} psi_{m3} weighted by the totally antisymmetric coefficients C^j_{m1,m2,m3}(q), the computation Q_q^2 reduces to a sum over products of two 3j symbols contracted with six fermion operators. The complete antisymmetry ensures that every term in Q_q^2 vanishes by the Grassmann property {psi_m, psi_n} = 0, giving Q_q^2 = 0. Identical argument for (Q_q^dagger)^2 = 0.

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

#### Node 1.1.3

**Statement:** Step 1.1.3 (U_q(su(2)) covariance): The q-supercharge Q_q transforms as a scalar under U_q(su(2)), i.e., [J_q^+, Q_q] = [J_q^-, Q_q] = [J_q^3, Q_q] = 0, where J_q^{+,-,3} are the generators of U_q(su(2)) acting on the fermion Fock space. This follows from the Wigner-Eckart theorem for quantum groups: the quantum 3j symbol with j1=j2=j3=j couples three spin-j representations to the trivial (spin-0) representation.

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

#### Node 1.1.4

**Statement:** Step 1.1.4 (Positive semi-definiteness): For q > 0 real, the quantum 3j symbols are real-valued (since q-numbers [n]_q are real for q > 0). Therefore Q_q^dagger is the Hermitian adjoint of Q_q in the standard Fock space inner product. It follows that H_q = Q_q Q_q^dagger + Q_q^dagger Q_q >= 0 as an operator, with ker(H_q) = ker(Q_q) intersect ker(Q_q^dagger).

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

### Node 1.2

**Statement:** PART 2 (Melonic dominance): The q-deformed BLM model exhibits melonic dominance in the large-j limit: the quantum 3j bubble identity implies that the self-energy is dominated by melonic (iterated bubble) diagrams, with non-melonic corrections suppressed by powers of 1/j. The leading correction (quantum 12j symbol) scales as (log j)/j, matching the undeformed case up to q-dependent prefactors.

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

#### Node 1.2.1

**Statement:** Step 1.2.1 (Quantum 3j bubble identity): The q-deformed bubble identity holds: sum_{m1,m2} C^j_{m1,m2,m}(q) C^j_{m1,m2,m-prime}(q) = delta_{m,m-prime} / [2j+1]_q. This is the quantum analog of 3j orthogonality and follows from the completeness of quantum Clebsch-Gordan coefficients in the tensor product decomposition of U_q(su(2)) representations.

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

#### Node 1.2.2

**Statement:** Step 1.2.2 (q-melonic self-energy): The q-bubble identity implies that the leading (melonic) self-energy diagram evaluates to Sigma_melonic(q) = J delta_{m,m-prime} / [N]_q, where [N]_q = [2j+1]_q. This has the same structure as the undeformed case but with [N]_q replacing N, ensuring the melonic Schwinger-Dyson equations close.

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

#### Node 1.2.3

**Statement:** Step 1.2.3 (Non-melonic suppression — q-tetrahedron): The first non-melonic correction involves the quantum 6j symbol {j j j; j j j}_q. Its large-j asymptotics are controlled by the quantum Racah formula. For generic q > 0 (not a root of unity), the quantum 6j symbol has the same 1/sqrt(j) suppression as the classical case, giving a 1/sqrt(j) suppression of the tetrahedron diagram.

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

#### Node 1.2.4

**Statement:** Step 1.2.4 (q-9j vanishing): The quantum 9j symbol with all spins j (j odd) vanishes identically, just as in the classical case. This follows from the quantum analog of the symmetry property: the q-9j symbol changes sign under a column permutation that leaves it invariant when 3j is odd, forcing it to zero.

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

#### Node 1.2.5

**Statement:** Step 1.2.5 (q-12j leading correction): The leading non-vanishing non-melonic correction comes from the quantum 12j symbol of the second kind. Its large-j asymptotics scale as (log j)/j^{3/2}, giving an overall (log j)/j suppression of the non-melonic diagrams relative to the melonic ones, matching the classical scaling up to q-dependent prefactors.

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

### Node 1.3

**Statement:** PART 3 (q-BPS states and q-Witten index): The q-deformed Hamiltonian H_q admits BPS states (ker H_q) whose count is given by a q-deformed Witten index W_q(r) = Tr[(-1)^F exp(2pi i r R_q)]. For j odd and q > 0 real, D^BPS_q(j, ±1/6) is a q-deformation of 3^j computable from the representation ring of U_q(su(2)).

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

#### Node 1.3.1

**Statement:** Step 1.3.1 (q-Witten index computation): The q-Witten index is W_q(r) = Tr_{Fock}[(-1)^F exp(2pi i r N_psi/3)] where the trace is over the full Fock space of N=[2j+1]_q-dimensional fermions. Since the fermion operators are undeformed (only the couplings carry q-dependence), this trace factorizes identically to the undeformed case: W_q(r) = omega^{-N/2} (1 - omega^r)^N where omega = exp(2pi i/3) and N = 2j+1. The Witten index is q-INDEPENDENT.

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

#### Node 1.3.2

**Statement:** Step 1.3.2 (q-BPS at maximal spin): The states of maximal angular momentum l_max = j(j+1)/2 with n=j fermions (R=1/6) and n=j+1 fermions (R=-1/6) are BPS for all q > 0. These states |0_tilde>_pm satisfy Q_q|0_tilde> = Q_q^dagger|0_tilde> = 0 because the pair operator O_{j,m}(q) annihilates them (no room for additional/fewer pairs at maximal spin). The argument is topological in nature, depending only on angular momentum quantum numbers not on q.

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

#### Node 1.3.3

**Statement:** Step 1.3.3 (q-deformed BPS partition function): In the large SU(2) charge regime (J3 ~ j^2/2), the q-BPS partition function is Z^BPS_q(j) = sum_s d_s(j,q) q_BPS^s = 2 prod_{m=1}^{j} (1 + q_BPS^m + q_BPS^{2m}), where the product structure reflects the factorization of the Hilbert space into z-modes and +-modes. For q=1 this reproduces Z^BPS from BLM. The total count D^BPS_q = Z^BPS_q(1) = 2 times 3^j is q-independent (it counts states topologically).

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

#### Node 1.3.4

**Statement:** Step 1.3.4 (Spectral deformation): While the BPS count is q-independent, the non-BPS spectrum of H_q depends on q. The energy eigenvalues satisfy E_q(R, l) = (J/3){[2j+1]_q - 3([N_psi]_q + [j+1/2]_q) + 3 sum_m <O^dagger_{j,m}(q) O_{j,m}(q)>}, providing a smooth q-deformation of the BLM spectrum that reduces to the standard spectrum at q=1.

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

### Node 1.4

**Statement:** PART 4 (Turaev-Viro connection): In the large-j semiclassical limit, the non-melonic corrections to the q-deformed model are controlled by quantum 6j symbols. When q = exp(2pi i/r) is a root of unity, these give the Turaev-Viro state sum invariants of 3-manifolds, generalizing the Ponzano-Regge/3D-gravity connection of the undeformed (q=1) BLM model. This provides a direct link between the q-BLM model and 3D Chern-Simons/topological gravity.

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

#### Node 1.4.1

**Statement:** Step 1.4.1 (Ponzano-Regge review): In the undeformed BLM model (q=1), the non-melonic corrections involve classical 6j symbols whose large-j asymptotics give the Ponzano-Regge amplitude: {j j j; j j j} ~ (1/sqrt(12 pi j)) cos(S_Regge + pi/4), where S_Regge is the Regge action of a regular tetrahedron with edge lengths j+1/2. This connects the BLM diagram expansion to a sum over 3D Euclidean gravity simplicial geometries (BLM-paper, Section on 6j asymptotics).

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

#### Node 1.4.2

**Statement:** Step 1.4.2 (Quantum 6j asymptotics — generic q): For q > 0 real and not a root of unity, the quantum 6j symbol {j j j; j j j}_q has large-j asymptotics of the form (1/sqrt(j)) times oscillatory terms involving the q-deformed Regge action. The q-deformation modifies the edge lengths and dihedral angles of the dual tetrahedron, corresponding to a deformed simplicial geometry. The 1/sqrt(j) suppression factor is preserved.

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

#### Node 1.4.3

**Statement:** Step 1.4.3 (Root-of-unity truncation — Turaev-Viro): When q = exp(2 pi i / r) is a primitive root of unity, the representation theory of U_q(su(2)) truncates: spins are bounded by j <= (r-2)/2. The quantum 6j symbols become the building blocks of the Turaev-Viro state sum TV_r(M) = sum_{colorings} prod_{edges} dim_q(j_e) prod_{tetrahedra} {6j}_q, which is a topological invariant of the 3-manifold M. This is the q-deformation of the (formal) Ponzano-Regge sum.

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

#### Node 1.4.4

**Statement:** Step 1.4.4 (Chern-Simons correspondence): The Turaev-Viro invariant TV_r(M) equals |Z_CS(M; SU(2), k)|^2 where Z_CS is the Chern-Simons partition function at level k = r-2 (Turaev-Walker theorem). Thus the non-melonic corrections to the q-BLM model at q = root of unity are controlled by 3D Chern-Simons theory, providing a direct link between the q-deformed melonic model and 3D topological quantum gravity.

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

#### Node 1.4.5

**Statement:** Step 1.4.5 (Physical interpretation): The q-deformation parameter interpolates between two gravitational regimes: (a) q=1 (k -> infinity): corrections controlled by 3D Euclidean gravity (Ponzano-Regge, infinite Chern-Simons level), and (b) q = root of unity (finite k): corrections controlled by 3D topological gravity (Turaev-Viro/Chern-Simons at finite level). The melonic dominance at large j persists in both regimes, providing a disorder-free quantum mechanical model with a tunable gravitational dual.

**Type:** claim

**Inference:** assumption

**Status:** pending

**Taint:** unresolved

