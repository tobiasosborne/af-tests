# Rigorous Mathematical Statements

Extracted from: **"A melonic quantum mechanical model without disorder"**
by Anna Biggs, Loki L. Lin, and Juan Maldacena (arXiv: 2601.08908).

All statements are formulated exclusively in the Hamiltonian (operator-algebraic) setting.
Equation references of the form (n) refer to the original paper.

---

## 1. Model Definition (Precise)

### Definition 1 (Hilbert Space)

Fix an odd integer j >= 1 and set N = 2j + 1. The single-particle space is
V = C^N with canonical basis {|m>}_{m = -j, -j+1, ..., j}. The Hilbert space is
the fermionic Fock space

    H = /\*(V) = /\^0(V) + /\^1(V) + ... + /\^N(V)  (isomorphic to C^{2^N})

equipped with creation and annihilation operators psi^dag_m, psi_m for
m in {-j, -j+1, ..., j} satisfying the canonical anticommutation relations

    {psi_m, psi^dag_{m'}} = delta_{m,m'},    {psi_m, psi_{m'}} = 0,    {psi^dag_m, psi^dag_{m'}} = 0.

The Fock vacuum |0> is defined by psi_m |0> = 0 for all m.

### Definition 2 (Wigner 3j Symbol)

For three copies of the spin-j representation of SU(2), the 3j symbol is

    C^j_{m_1 m_2 m_3} := ( j   j   j  )
                          ( m_1 m_2 m_3 )

which equals (-1)^{j-j-m_3} / sqrt(2j+1) times the Clebsch-Gordan coefficient
<j m_1; j m_2 | j (-m_3)>. For odd j, C^j is antisymmetric under transposition
of any two columns. It vanishes unless m_1 + m_2 + m_3 = 0 and the triangle
inequality is satisfied (which is automatic here since all spins equal j, so the
condition is 3j even -- satisfied since j is odd gives 3j odd, but note the 3j
symbol requires j+j+j = 3j even for non-vanishing; in fact for three equal
odd-integer spins the antisymmetry precisely accounts for the fermionic statistics).

**Key property.** C^j_{m_1 m_2 m_3} is real, and satisfies
C^j_{-m_1, -m_2, -m_3} = -C^j_{m_1, m_2, m_3}.

### Definition 3 (Supercharge)

Let J > 0 be a coupling constant with dimensions of energy. The supercharge
Q : H -> H is defined by

    Q = (1/3!) sqrt(2JN) sum_{m_1, m_2, m_3 = -j}^{j} C^j_{m_1 m_2 m_3} psi_{m_1} psi_{m_2} psi_{m_3}

and its adjoint is

    Q^dag = -(1/3!) sqrt(2JN) sum_{m_1, m_2, m_3 = -j}^{j} C^j_{m_1 m_2 m_3} psi^dag_{m_1} psi^dag_{m_2} psi^dag_{m_3}.

*Remark.* The factor sqrt(2JN) is a normalization convention chosen so that
the melonic Dyson-Schwinger equations match those of N=2 supersymmetric SYK
with coupling J (see Sec. 2 below).

### Definition 4 (Hamiltonian)

    H := {Q, Q^dag} = Q Q^dag + Q^dag Q.

### Definition 5 (Symmetry Operators)

**(a) Fermion number operator:**

    N_psi = sum_{m=-j}^{j} psi^dag_m psi_m - (2j+1)/2.

The shift -(2j+1)/2 makes N_psi antisymmetric under charge conjugation.

**(b) R-charge:**

    R = N_psi / 3.

**(c) SU(2) generators:**

    J_3 = sum_{m=-j}^{j} m psi^dag_m psi_m,

    J_+ = sum_{m=-j}^{j-1} sqrt((j-m)(j+m+1)) psi^dag_{m+1} psi_m,

    J_- = sum_{m=-j+1}^{j} sqrt((j+m)(j-m+1)) psi^dag_{m-1} psi_m.

These satisfy the standard su(2) commutation relations [J_3, J_+/-] = +/- J_+/-,
[J_+, J_-] = 2 J_3, and the Casimir is J^2 = J_3^2 + (J_+ J_- + J_- J_+)/2.

**(d) Charge conjugation:** C is the antilinear map defined by

    C : psi_m -> (-1)^m psi^dag_{-m}.

### Definition 6 (Composite Bilinear Operators)

For 0 <= l <= 2j with l odd (since j is odd, the antisymmetry of the fermions
restricts to odd l), define the spin-l fermion bilinear multiplet:

    O_{l,m} = sqrt(2(2l+1)) sum_{-j <= m_1 < m_2 <= j} ( j   j   l  ) psi_{m_1} psi_{m_2}.
                                                          ( m_1 m_2 -m )

---

## 2. Basic Properties (Provable)

### Proposition 1 (N=2 Supersymmetry Algebra)

(i) Q^2 = 0.

(ii) (Q^dag)^2 = 0.

(iii) H = {Q, Q^dag} >= 0 as an operator (i.e., <v|H|v> >= 0 for all |v> in H).

*Proof sketch.* (i) follows from the antisymmetry of C^j_{m_1 m_2 m_3} combined
with the anticommutativity of the fermion operators. (iii) follows from H = QQ^dag + Q^dag Q
and the positivity of each term: <v|QQ^dag|v> = ||Q^dag v||^2 >= 0.

### Proposition 2 (Symmetries of the Hamiltonian)

(i) **SU(2) invariance:** [H, J_a] = 0 for a = 1, 2, 3 (equivalently, [H, J^2] = 0).

(ii) **U(1)_R symmetry:** [H, R] = 0.

(iii) **R-charge of Q:** [Q, R] = Q and [Q^dag, R] = -Q^dag, i.e., Q carries
R-charge +1 and Q^dag carries R-charge -1.

(iv) **Charge conjugation:** CHC^{-1} = H, and C N_psi C^{-1} = -N_psi.

*Remark.* Statement (i) follows from the SU(2) invariance of the 3j symbol.
Statement (iii) follows because Q is cubic in annihilation operators, each of
which carries fermion number -1, so Q changes N_psi by -3, hence R by -1;
equivalently [N_psi, Q] = -3Q gives [R, Q] = -Q.

### Proposition 3 (Normal-Ordered Hamiltonian)

The Hamiltonian admits the normal-ordered form

    H = (J/3) [ (2j+1) - 3(N_psi + j + 1/2) + 3 sum_{m=-j}^{j} O^dag_{j,m} O_{j,m} ]

where O_{j,m} is the spin-j bilinear operator from Definition 6.

*Remark.* The simplicity of this expression -- involving only the l = j Haldane
pseudopotential -- is a special feature of the model. It means that the
interaction, viewed in the quantum Hall picture on S^2, has a single angular
momentum channel.

### Proposition 4 (3j Orthogonality / Bubble Identity)

For all l, l' in {0, 1, ..., 2j} and m, m' with |m| <= l, |m'| <= l':

    sum_{m_1, m_2} ( l   j   j  ) ( l'  j   j  ) = delta_{l,l'} delta_{m,m'} / (2l+1).
                   ( m  m_1 m_2 ) ( m' m_1 m_2 )

*Remark.* This is the standard orthogonality relation for Wigner 3j symbols.
The special case l = l' = j is used repeatedly in the melonic analysis: it
implies that the simplest bubble diagram evaluates to J/N times delta_{m,m'},
reproducing the SYK disorder-averaged propagator without any disorder averaging.

### Proposition 5 (Hilbert Space Decomposition by J_3)

The generating function for J_3 eigenvalues on the full Hilbert space is:

    Tr_H[e^{i theta J_3}] = prod_{m=-j}^{j} (1 + e^{i theta m}).

Define d_n = #{states with J_3 eigenvalue n}. Then:

    d_n = (1/2pi) integral_{-pi}^{pi} d theta  e^{-i n theta} prod_{m=-j}^{j} (1 + e^{i theta m}).

The number of spin-l irreducible representations of SU(2) in H is

    D_l = d_l - d_{l+1}.

The maximum spin is

    l_max = sum_{m=1}^{j} m = j(j+1)/2,

and D_{l_max} = 2 (exactly two copies of the spin-l_max representation).

*Remark.* The joint generating function for J_3 and fermion number is

    Tr_H[e^{i theta J_3} y^{N_psi}] = prod_{m=-j}^{j} (1/sqrt(y) + sqrt(y) e^{i theta m}).

### Proposition 6 (Witten Index)

The Z_3-graded Witten index (where omega = e^{2pi i/3}) is, for r = 1, 2:

    W_r = Tr_H[(-1)^F e^{2pi i r R}] = omega^{-(2j+1)/2} (1 - omega^r)^{2j+1}.

Here (-1)^F = (-1)^{N_psi + (2j+1)/2} is the fermion parity operator.

*Remark.* The Z_3 subgroup of U(1)_R commutes with Q and Q^dag, which is what
makes this index well-defined and non-vanishing. This is the same index as in
N=2 SYK computed in Fu-Gaiotto-Maldacena-Sachdev (2016).

---

## 3. BPS States

### Theorem 1 (BPS Condition)

A state |v> in H satisfies H|v> = 0 if and only if Q|v> = 0 and Q^dag|v> = 0.

*Proof.* If H|v> = 0, then 0 = <v|H|v> = ||Q^dag v||^2 + ||Q v||^2, which forces
Q|v> = 0 and Q^dag|v> = 0. The converse is immediate from H = QQ^dag + Q^dag Q.

*Remark.* States annihilated by H are called BPS states. The theorem shows that
the BPS condition is equivalent to lying in ker(Q) intersect ker(Q^dag).

### Proposition 7 (Maximal-Spin BPS States)

The two states

    |0~>_- = psi^dag_1 psi^dag_2 ... psi^dag_j |0>,
    |0~>_+ = psi^dag_0 psi^dag_1 psi^dag_2 ... psi^dag_j |0>

satisfy H|0~>_+/- = 0. They have quantum numbers:

    J_3 = j(j+1)/2 = l_max,    R = -1/6  (for |0~>_-),    R = +1/6  (for |0~>_+).

These are the unique states at maximal J_3 = l_max and constitute the two copies
of the l_max representation mentioned in Proposition 5.

*Remark.* The proof that E = 0 for these states is given explicitly in the paper's
Appendix D, using a nontrivial identity for restricted sums of squared 3j symbols.

### Conjecture 1 (BPS Degeneracy at R = +/-1/6)

For all odd j >= 1, essentially all BPS states have R-charge R = +/-1/6, with
the number of BPS states given by

    D^{BPS}(j, +1/6) = D^{BPS}(j, -1/6) = 3^j.

More precisely, the number of BPS states with |R| != 1/6 is O(1) as j -> infinity.

*Remark.* This has been verified by exact diagonalization for j = 1, 3, 5, 7, 9, 11.
For j = 1, 3, 5, 11 all BPS states have |R| = 1/6. For j = 7 and j = 9 there
are O(1) "sporadic" exceptions (see Conjecture 4 below). The formula 3^j is
derived from the Witten index under the assumption that all BPS states have |R| = 1/6.

### Conjecture 2 (BPS State Count by Angular Momentum)

Assuming all BPS states have |R| = 1/6, the number of BPS states with J_3
eigenvalue n is given by

    d_n^{BPS} = (1/2pi) integral_{-pi}^{pi} d theta  e^{-i n theta} Z_{BPS}(theta),

where

    Z_{BPS}(theta) = 2 e^{-i theta j(j+1)/2} prod_{m=1}^{j} (1 + e^{i theta m} + e^{2i theta m}).

Equivalently, writing s = l_max - J_3 as the "excitation number" above the
maximal-J_3 vacuum:

    Z_j^{BPS} = sum_{s >= 0} d_s(j) q^s = 2 prod_{m=1}^{j} (1 + q^m + q^{2m}).

---

## 4. Spectral Properties

### Proposition 8 (Fock Vacuum Energy)

The Fock vacuum |0> (defined by psi_m|0> = 0 for all m) has energy and R-charge:

    E_{vac} = J(2j+1)/3,    R_{vac} = -(2j+1)/6.

*Remark.* This follows immediately from Proposition 3 by noting that O_{j,m}|0> = 0
and N_psi|0> = -(j + 1/2).

### Proposition 9 (Few-Fermion Energies)

**(a) One-fermion sector** (R = R_{vac} + 1/3 = -(2j-1)/6): The states
psi^dag_m |0> for m = -j, ..., j form a single spin-j multiplet. Since
O_{j,m} annihilates any single-fermion state, the energy is

    E = (2J/3)(j - 1).

**(b) Two-fermion sector** (R = R_{vac} + 2/3 = -(2j-3)/6): The states
O^dag_{l,m}|0> for l = 1, 3, 5, ..., 2j-1 (odd l only) have two distinct
energies:

    E = J(2j-5)/3    for l != j,
    E = J(2j-2)/3    for l = j.

*Remark.* The high degeneracy at E = J(2j-5)/3 (spanning many different spin
representations) arises because O_{j,m} annihilates all two-fermion states not
in the l = j channel. This is a manifestation of the single Haldane
pseudopotential structure of the Hamiltonian.

### Theorem 2 (Maximal Angular Momentum Energy)

Consider the state with maximal J_3 (and maximal SU(2) spin) at fixed R-charge:

    |l_max^{(n)}> = psi^dag_{j-n} psi^dag_{j-n+1} ... psi^dag_{j-1} psi^dag_j |0>,    n < j,

with R = (2n - 2j + 1)/6 and l_max^{(R)} = j(n+1) - n(n+1)/2. Then:

**(a) Linear regime** (n <= (j-1)/2, equivalently |R| >= j/6):

    E/J = (2j+1)/3 - (n+1).

These are also the **minimum** energy states in their respective R-charge sectors.

**(b) Nonlinear regime** (n > (j-1)/2, equivalently |R| < j/6):

    E/J = (2j+1) sum_{-3(|R| - 1/6) <= m_1 < 0} { sum_{-3(|R| - 1/6) <= m_2 <= -m_1}
          ( j   j   j  )^2 }.
          ( m_1 m_2 -(m_1+m_2) )

**(c)** In particular, E = 0 exactly when R = +/-1/6 (i.e., n = j or n = j-1),
confirming that the maximal-spin states are BPS (Proposition 7).

*Remark.* The transition from linear to nonlinear behavior at n = (j-1)/2
corresponds, in the fuzzy sphere picture, to the angular cap of occupied fermions
reaching an opening angle of 120 degrees. At this point, the interaction term
O_{j,m} begins to have nonzero matrix elements because two of the three
"momentum vectors" at a vertex can both point into the occupied region.

### Proposition 10 (Energy Gap from Schwarzian)

In the melonic regime (small charges, large j), the super-Schwarzian effective action
predicts a gap above the BPS states given by

    E_{gap}(R) = J / (8 N alpha_S) * (|R| - 1/2)^2,

where alpha_S ~ 0.00842 is a numerical constant determined by the large-N
Dyson-Schwinger equations of N=2 SYK.

*Remark.* This formula is valid for |R| < 1/2 and angular momentum l << l_max.
It provides the minimum non-BPS energy at a given R-charge in the small-charge
sector of the theory.

---

## 5. Large-j Asymptotics

### Theorem 3 (State Density Asymptotics)

**(a) Gaussian regime** (|n| << l_max = j(j+1)/2): The number of states with
J_3 eigenvalue n satisfies

    d_n ~ 2^{2j+1} / (sigma sqrt(2 pi)) * exp(-n^2 / (2 sigma^2)),

where sigma = sqrt(j^3/6).

**(b) Cardy regime** (1 << N_hat << l_max, where N_hat = l_max - |n|):

    d_n ~ (1/2) * 1/(6^{1/4}) * N_hat^{-3/4} * exp(2 pi sqrt(N_hat/6)).

**(c) BPS state asymptotics** (assuming Conjecture 1):

In the Gaussian regime (|n| << l_max):

    d_n^{BPS} ~ (2 * 3^j) / (sigma_BPS sqrt(2 pi)) * exp(-n^2 / (2 sigma_BPS^2)),

where sigma_BPS = sqrt(2j^3/9).

In the Cardy regime (1 << N_hat << l_max):

    d_n^{BPS} ~ 1/(3 sqrt(3) N_hat^{3/4}) * exp(2 pi sqrt(N_hat/9)).

*Remark.* These are obtained by saddle-point approximation of the exact integral
formulas in Propositions 5 and Conjecture 2. The Cardy-regime formula for
d_n resembles the density of states of a 2d CFT with central charge c = 1,
which is explained by the emergent CFT_2 described in Section 6. The BPS
Cardy formula has effective central charge c = 2/3.

### Proposition 11 (Melonic Dominance)

In the diagrammatic expansion of singlet correlators at large j:

**(a) Bubble identity:** The simplest melonic self-energy correction evaluates to
J * delta_{m,m'} / N, independent of N, reproducing the SYK result. All melonic
diagrams therefore agree exactly with the N=2 SYK model with the same coupling J.

**(b) Tetrahedron suppression:** The simplest non-melonic vacuum diagram (tetrahedron,
proportional to the 6j symbol with all entries j) is suppressed by a factor of
1/sqrt(j) relative to melonic diagrams. More precisely,

    N^2 { j j j } ~ N^2 / (2^{1/4} sqrt(pi) j^{3/2}) * cos(6(j+1/2) arccos(1/3) + 3pi/4).
         { j j j }

**(c) 9j vanishing:** The 9j symbol with all nine entries equal to an odd integer
j vanishes identically:

    { j j j }
    { j j j } = 0    for j odd.
    { j j j }

*Proof of (c).* Exchange the first two columns of the first three 3j symbols in
the defining sum. This introduces a sign (-1)^{3j} = -1 (since j is odd). Then
relabel summation indices m_{i1} <-> m_{i2} for i = 1, 2, 3. The result is the
original expression times (-1), hence the sum is zero.

**(d) First nonzero non-melonic correction:** The 12j symbol of the second kind
(cube diagram, 8 vertices) gives the first non-vanishing non-melonic correction,
suppressed by (log j)/j relative to melonic diagrams:

    N^4 {12j}_{(II)} ~ N^4 * (log(2^{7/4} * 3j) + gamma) / (3 pi^2 j^4) + O(j^{-9/2}).

### Proposition 12 (Spin-l Representation Multiplicities at Large j)

**(a) Gaussian regime** (l << l_max):

    D_l ~ 2^{2j+1} * l / (sigma^3 sqrt(2 pi)) * exp(-l^2 / (2 sigma^2)),    sigma = sqrt(j^3/6).

**(b) Cardy regime** (1 << l_max - l << l_max):

    D_l ~ (1/2) * 1/(6^{1/4}) * (l_max - l)^{-5/4} * (pi/sqrt(6) - (3/4)(l_max - l)^{-1/2})
          * exp(2 pi sqrt((l_max - l)/6)).

---

## 6. Emergent CFT_2 (Large SU(2) Charge)

### Theorem 4 (CFT_2 Emergence near Maximal Angular Momentum)

In the large-j limit, for states near the maximal J_3 = j(j+1)/2, define the
re-centered fermion operators

    chi_m = psi_{-m},    chi_bar_m = psi^dag_m,

so that chi_m |0~>_+/- = chi_bar_m |0~>_+/- = 0 for m > 0. Then:

**(a) Hilbert space factorization.** The Hilbert space near maximal J_3 decomposes as

    H ~ H^z (x) H^{+/-}

where H^z is the Hilbert space of a chiral boson phi_z containing Fourier modes
n = 0 mod 3, and H^{+/-} is the Hilbert space of two chiral bosons phi_+, phi_-
containing Fourier modes n = +/-1 mod 3.

**(b) Hamiltonian.** The Hamiltonian in this regime is

    H = J * (6 sqrt(3)) / (pi j) * L_tilde_0^z,

where

    L_tilde_0^z = (1/3) * (p^2 - 1/4) / 2 + N_tilde,    N_tilde in Z_>=0,

and p in Z + 1/2 is the "momentum" quantum number of the phi_z boson.

**(c) Decoupling.** The bosons phi_+/- contribute to J_3 but NOT to the energy.
The total L_0 (measuring J_3^max - J_3) is

    L_0 = 3(L_tilde_0^z + L_tilde_0^{+/-}).

**(d) R-charge.** R = p/3, where p is the half-integer momentum of phi_z.

*Remark.* The key input is the large-j asymptotic of the 3j symbol for small m_i:

    ( j   j   j  ) ~ -(1/j) sqrt(2/(pi sqrt(3))) cos(3pi j/2 + 2pi(m_1 - m_2)/3)
    ( m_1 m_2 m_3)

which shows that the supercharge takes the form Q ~ integral d phi  psi(phi) psi(phi + 2pi/3) psi(phi - 2pi/3),
i.e., a product of fermion fields at three points separated by 2pi/3 on a circle.
After bosonization, only the n = 0 mod 3 modes appear in Q, yielding the
factorization.

### Proposition 13 (BPS Partition Function in CFT_2 Regime)

The BPS states near maximal angular momentum are enumerated by

    Z_{BPS} = 2 * Tr_{H^{+/-}}[q^{J_3^max - J_3}] = 2 prod_{k >= 0} 1/((1 - q^{1+3k})(1 - q^{2+3k})).

The factor of 2 corresponds to the two ground states of phi_z (with p = +/-1/2,
giving R = +/-1/6). The infinite product is the partition function of the
phi_+/- bosons.

*Remark.* The BPS states are obtained by acting with phi_+/- oscillator modes
on the two ground states of phi_z, while keeping phi_z in its ground state
(N_tilde = 0, p = +/-1/2). This gives an explicit construction of all BPS
states in the large-angular-momentum regime.

### Proposition 14 (BPS State Validity Range)

The CFT_2 description of BPS states is exact for excitation number s <= j - 1
(where s = J_3^max - J_3). For s >= j, corrections appear: the finite-j
partition function differs from the infinite-j (CFT_2) result.

More precisely:

    d_s(j) = d_s(infinity)    for 0 <= s <= j - 1,
    d_s(j) < d_s(infinity)    for s >= j.

### Proposition 15 (Recursion for BPS Counts)

The BPS state counts at excitation level s satisfy the recursion relation in j:

    d_s(j) - d_s(j-1) = d_{s-j}(j-1) + d_{s-2j}(j-1),

with the convention d_s(j) = 0 for s < 0.

*Remark.* This follows directly from the identity

    prod_{m=1}^{j}(1 + q^m + q^{2m}) = (1 + q^j + q^{2j}) prod_{m=1}^{j-1}(1 + q^m + q^{2m}).

It implies that d_s(j) = d_s(j-1) when s < j, confirming Proposition 14.
At s = j, the first correction is d_j(j) - d_j(j-1) = d_0(j-1) = 2.

### Proposition 16 (Lowest Energy at Fixed R in CFT_2 Regime)

For states near maximal angular momentum with no phi_z oscillators excited
(N_tilde = 0), the energy as a function of R-charge is:

    E = J * (9 sqrt(3)) / (pi j) * (R^2 - 1/36).

In particular, E = 0 for R = +/-1/6, confirming the BPS condition. This
formula is valid for |R| << j/3 and angular momentum near l_max.

---

## 7. Conformal Dimensions (Melonic Regime)

### Proposition 17 (Operator Dimensions at l = 0)

In the melonic large-j limit, for SU(2)-singlet composite operators, the
conformal dimensions h of fermionic operators are determined by the eigenvalue
equations:

**(a) Symmetric channel:**

    1 = kappa^s(h),    kappa^s(h) := -Gamma(5/3) Gamma(5/12 - h/2) Gamma(5/12 + h/2)
                                      / (2^{1/3} Gamma(4/3) Gamma(13/12 - h/2) Gamma(1/12 + h/2)).

**(b) Antisymmetric channel:**

    1 = kappa^a(h),    kappa^a(h) := -Gamma(5/3) Gamma(11/12 - h/2) Gamma(-1/12 + h/2)
                                      / (2^{1/3} Gamma(4/3) Gamma(7/12 - h/2) Gamma(7/12 + h/2)).

**Notable solution:** h = 3/2 is a solution of both equations. One copy gives rise
to the N=2 super-Schwarzian mode (with partners at h = 1, 2). The other gives
a nontrivial operator at h = 3/2.

**Relation:** kappa^a(h) = kappa^s(1 - h).

### Proposition 18 (Operator Dimensions at General l)

For operators in spin-l representations of SU(2), the dimensions are given by

    1 = kappa_tilde(l) * kappa^s(h),    1 = kappa_tilde(l) * kappa^a(h),

where

    kappa_tilde(l) = { j j j }  /  { j j j }
                     { j j l }     { j j 0 }

In the limit j -> infinity:

    kappa_tilde(l) = P_l(-1/2),

where P_l is the Legendre polynomial.

**Special values:**
- kappa_tilde(0) = 1 (reduces to Proposition 17).
- kappa_tilde(1) = -1/2 (yields h = 1/2, corresponding to the conserved SU(2) current).
- kappa_tilde(l) -> 0 as l -> infinity (dimensions approach free-field values).

**Asymptotic dimension formula:** For large l or large excitation number k:

    h^s_{l,k} ~ Delta_psi + Delta_b + 2k + epsilon_{l,k},    Delta_psi = 1/6,    Delta_b = 2/3,

where epsilon_{l,k} -> 0 as l or k -> infinity.

*Remark.* The fact that operator dimensions become independent of l for large l
means the model does NOT produce Kaluza-Klein-type modes (where dimensions would
grow with l). This distinguishes it from models dual to AdS_2 x S^2 geometries.

---

## 8. Open Conjectures

### Conjecture 3 (Maximum Energy)

E_{vac} = J(2j+1)/3 is the maximum eigenvalue of H on the entire Hilbert space H.

*Evidence:* Verified numerically for j <= 11.

### Conjecture 4 (Sporadic BPS States)

For certain values of j, there exist O(1) BPS multiplets at R-charges other
than +/-1/6. The known cases from exact diagonalization are:

| j  | R      | l | # of multiplets |
|----|--------|---|-----------------|
| 7  | +1/2   | 7 | 1               |
| 7  | -1/2   | 7 | 1               |
| 9  | +1/2   | 9 | 2               |
| 9  | -1/2   | 9 | 2               |
| 9  | +5/6   | 0 | 2               |
| 9  | -5/6   | 0 | 2               |
| 11 | (none) | - | -               |

For j = 1, 3, 5, 11 there are no sporadic BPS states.

**Open question:** Do sporadic BPS states persist for arbitrarily large j, or
do they only appear at finitely many values of j?

*Remark.* The R = +/-5/6 BPS states at j = 9 are particularly surprising:
in N=2 SYK there are never any |R| = 5/6 BPS states. The sporadic states
are consistent with the Witten index (Proposition 6) due to cancellations in
the Z_3 grading.

### Conjecture 5 (SU(2) Effective Action)

The low-energy effective action for the SU(2) sector is NOT of the form

    I = (N/J) integral dt Tr[(g^{-1} dg/dt)^2]

(which would give an energy gap proportional to the SU(2) Casimir), but rather
takes the first-order form

    I = integral dt Tr[g^{-1} (dg/dt) rho]

where g parametrizes SU(2) (i.e., g in S^3) and rho is a triplet-valued field
with rho_a = J_a on-shell. This would be consistent with the existence of BPS
states at various angular momenta (a Casimir-type gap would forbid this).

*Evidence:* Numerical diagonalization at j = 11 shows that the energy gap does NOT
grow as the SU(2) Casimir l(l+1), but instead shows a more complex l-dependence
consistent with BPS states at multiple spin values.

### Conjecture 6 (Chaos)

The model is maximally chaotic in the sense of the Maldacena-Shenker-Stanford
bound (Lyapunov exponent lambda_L = 2pi/beta) in the large-j melonic limit
for SU(2)-singlet observables. This follows from the equivalence of the melonic
Dyson-Schwinger equations with those of N=2 SYK.

*Evidence:* The spectral form factor computed numerically at j = 11 in the
R = 1/6, l = 16 sector shows ramp-and-plateau behavior characteristic of
random matrix statistics. At current system sizes, it is not possible to
distinguish between GOE and other random matrix ensembles, or to determine
whether the Thouless time scales as O(1) or O(N).

---

## Appendix A: Key Identities Used in Proofs

### Identity A1 (3j Orthogonality, Full)

    sum_{m_1, m_2, m_3} ( j   j   j  )^2 = 1.
                         ( m_1 m_2 m_3)

### Identity A2 (Restricted Sum of Squared 3j Symbols)

For j odd:

    sum_{m_1, m_2, m_3 != 0} ( j   j   j  )^2 = 1 - 3/(2j+1).
                               ( m_1 m_2 m_3)

By symmetry under sign patterns, the sum restricted to m_1 > 0, m_2 > 0,
m_3 = -(m_1 + m_2) < 0 gives (1/6)(1 - 3/(2j+1)) = (j-1)/(3(2j+1)).

### Identity A3 (6j Symbol Asymptotics)

For j >> 1, the 6j symbol with all entries equal to j satisfies:

    { j j j }  ~ 1/(2^{1/4} sqrt(pi) j^{3/2}) * cos(6(j + 1/2) arccos(1/3) + 3pi/4).
    { j j j }

*Remark.* The phase has a geometric interpretation: it is the Regge action of
3d Euclidean gravity evaluated on a regular tetrahedron with edge lengths j + 1/2.

### Identity A4 (Large-j 3j Symbol for Small m)

For |m_i| << j:

    ( j   j   j  ) ~ -(1/j) sqrt(2/(pi sqrt(3))) cos(3pi j/2 + 2pi(m_1 - m_2)/3).
    ( m_1 m_2 m_3)

---

## Appendix B: Notation Summary

| Symbol | Definition |
|--------|-----------|
| j | Odd positive integer, spin of the fundamental representation |
| N | 2j+1, number of fermion species |
| J | Coupling constant (energy dimension) |
| H | Fermionic Fock space /\*(C^N) |
| psi_m, psi^dag_m | Fermion annihilation/creation operators, m in {-j,...,j} |
| Q, Q^dag | Supercharge and its adjoint |
| H | Hamiltonian {Q, Q^dag} |
| N_psi | Shifted fermion number sum_m psi^dag_m psi_m - (2j+1)/2 |
| R | R-charge = N_psi/3 |
| J_3, J_+, J_- | SU(2) generators |
| l_max | j(j+1)/2, maximum angular momentum |
| O_{l,m} | Spin-l fermion bilinear multiplet |
| C^j_{m_1 m_2 m_3} | Wigner 3j symbol with all spins equal to j |
| d_n | Number of states with J_3 eigenvalue n |
| D_l | Number of spin-l SU(2) representations in H |
| d_n^{BPS} | Number of BPS states with J_3 eigenvalue n |
| W_r | Z_3-graded Witten index (r = 1, 2) |
| alpha_S | Schwarzian coefficient ~ 0.00842 |
| kappa^{s,a}(h) | Kernel eigenvalues for symmetric/antisymmetric channels |
| kappa_tilde(l) | Ratio of 6j symbols determining l-dependent kernel |
