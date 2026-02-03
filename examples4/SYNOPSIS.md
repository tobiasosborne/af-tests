# Synopsis: A Melonic Quantum Mechanical Model Without Disorder

**Authors:** Anna Biggs, Loki L. Lin, Juan Maldacena

**arXiv:** 2601.08908v1

---

## Overview

This paper constructs a quantum mechanical model of interacting fermions that reproduces the low-energy physics of the supersymmetric SYK model but **without any quenched disorder**. The key ingredient is the Wigner 3j symbol of SU(2), which provides a structured, deterministic interaction tensor replacing the random couplings of SYK. The model possesses N=2 supersymmetry, an SU(2) global symmetry, and a U(1)\_R charge. In the large-j limit (where j labels the spin representation and N = 2j+1 is the number of complex fermions), the Feynman diagrams become dominated by melonic graphs, yielding the same Schwinger-Dyson equations as the disordered SYK model. The paper explores numerous physical regimes: near-conformal dynamics governed by a super-Schwarzian action, large R-charge states with simple Fock-space descriptions, and --- most strikingly --- an emergent chiral 1+1 dimensional CFT arising from edge modes on a fuzzy sphere at large SU(2) charge.

---

## 1. Model Definition

### Degrees of Freedom

- **N = 2j + 1** complex fermions $\psi_m$ with $m = -j, -j+1, \ldots, j$, transforming in the spin-j representation of SU(2).
- Canonical anticommutation relations: $\{\psi_m, \psi^\dagger_{m'}\} = \delta_{m,m'}$.
- **j must be an odd integer**, so the symmetry is really SO(3) (since $(-1)^{2j} = +1$ for odd j, meaning the center of SU(2) acts trivially).

### Interaction Tensor: The 3j Symbol

The interaction is built from the Wigner 3j symbol:

$$C^j_{m_1 m_2 m_3} = \begin{pmatrix} j & j & j \\ m_1 & m_2 & m_3 \end{pmatrix}$$

This is the unique (up to normalization) SU(2)-invariant rank-3 tensor on the spin-j representation. It is nonzero only when $m_1 + m_2 + m_3 = 0$ and is totally antisymmetric (for odd j).

### Supercharges

$$Q = \frac{1}{3!} \sqrt{2 \mathsf{J} N} \sum_{m_1, m_2, m_3} C^j_{m_1 m_2 m_3}\, \psi_{m_1} \psi_{m_2} \psi_{m_3}$$

$$Q^\dagger = -\frac{1}{3!} \sqrt{2 \mathsf{J} N} \sum_{m_1, m_2, m_3} C^j_{m_1 m_2 m_3}\, \psi^\dagger_{m_1} \psi^\dagger_{m_2} \psi^\dagger_{m_3}$$

Here $\mathsf{J}$ is an energy coupling constant (written in sans-serif to distinguish from the angular momentum quantum number j).

### Hamiltonian and Supersymmetry

$$H = \{Q, Q^\dagger\}$$

This defines an **N = 2 supersymmetric** quantum mechanics: $Q^2 = 0$, $(Q^\dagger)^2 = 0$, and $H \geq 0$. BPS (zero-energy) states satisfy $Q|\text{BPS}\rangle = Q^\dagger|\text{BPS}\rangle = 0$.

### Conserved Charges

- **Fermion number:** $\mathcal{N}_\psi = \sum_m \psi^\dagger_m \psi_m - \frac{2j+1}{2}$
- **U(1)\_R charge:** $R = \mathcal{N}_\psi / 3$
- **SU(2) generators:**
  - $J_3 = \sum_m m\, \psi^\dagger_m \psi_m$
  - $J_+ = \sum_m \sqrt{j(j+1) - m(m+1)}\, \psi^\dagger_{m+1} \psi_m$
  - $J_- = (J_+)^\dagger$

All of $J_3, J_\pm, R$ commute with $H$ and with $Q, Q^\dagger$ (except that $[R, Q] = Q$ and $[R, Q^\dagger] = -Q^\dagger$).

---

## 2. Normal-Ordered Hamiltonian

The Hamiltonian can be rewritten in normal-ordered form using the **Haldane pseudopotential** decomposition. Defining bilinear operators:

$$O_{\ell, m} = \sqrt{2(2\ell+1)} \sum_{m_1, m_2} \begin{pmatrix} j & j & \ell \\ m_1 & m_2 & -m \end{pmatrix} \psi_{m_1} \psi_{m_2}$$

the normal-ordered Hamiltonian becomes:

$$H = \frac{\mathsf{J}}{3} \left[ (2j+1) - 3\left(\mathcal{N}_\psi + j + \frac{1}{2}\right) + 3 \sum_m O^\dagger_{j,m} O_{j,m} \right]$$

Crucially, **only the spin-j channel** of the two-body interaction appears. This is the highest angular momentum (most repulsive) Haldane pseudopotential, familiar from quantum Hall physics. The operators $O_{\ell, m}$ for $\ell \neq j$ do not appear in H.

---

## 3. Key Physical Regimes

### 3.1 Melonic Regime (Small Charges, Large j)

At zero SU(2) and U(1)\_R chemical potential, the SU(2)-invariant correlators dominate. The diagrammatic analysis reveals:

- **Melonic dominance:** The simplest bubble (melon) diagram contributes a factor $\mathsf{J}$ independent of N, thanks to the orthogonality relation of 3j symbols:
$$\sum_{m_2, m_3} (C^j_{m_1 m_2 m_3})^2 = \frac{1}{N}$$

- **Non-melonic suppression:**
  - The **tetrahedron** diagram involves a 6j symbol and is suppressed by $1/\sqrt{j}$.
  - The **9j symbol** contribution vanishes identically for odd j.
  - The first nonvanishing non-melonic correction comes from a **12j symbol of the second kind**, suppressed by $(\log j)/j$.

- **Intuitive picture:** Think of the fermions as living on a fuzzy sphere in the lowest Landau level. Momentum conservation constrains the three interacting momenta to form an equilateral triangle on the sphere. Melonic diagrams have an enhanced number of internal degrees of freedom compared to non-planar topologies, explaining their dominance.

### 3.2 Near-Conformal Regime (Low Energy, Small Charges)

In the low-energy (IR) limit, the model flows to a near-conformal phase:

- **Conformal dimensions:** $\Delta_\psi = 1/6$, $\Delta_b = 2/3$ (where b is the auxiliary boson in the superfield formulation).
- The low-energy effective action is the **N = 2 super-Schwarzian**, governing the breaking of the superconformal reparametrization symmetry.
- **Operator dimensions** for composite spin-$\ell$ operators are modified at finite j by a factor:
$$\tilde{\kappa}(\ell) = P_\ell(-1/2)$$
  where $P_\ell$ is the Legendre polynomial. At $j = \infty$, $\tilde{\kappa} \to 1$ and one recovers the SYK result.
- **Energy gap** for non-BPS states above the ground state:
$$E_{\text{gap}} = \frac{\mathsf{J}}{8 N \alpha_S} \left(|R| - \frac{1}{2}\right)^2$$
  with the Schwarzian coupling $\alpha_S \approx 0.00842$.

### 3.3 Large R-Charge

Near the edges of the R-charge spectrum (close to the Fock vacuum or fully filled state):

- **Fock vacuum energy:** $E_{\text{vac}} = \mathsf{J}(2j+1)/3$, with $R_{\text{vac}} = -(2j+1)/6$.
- States with a **few fermions** added to (or removed from) the vacuum have energies determined directly by the normal-ordered Hamiltonian.
- Energy levels are **highly degenerate** when the operator $O_{j,m}$ annihilates the state, since the quartic interaction term then vanishes.

### 3.4 Largest Spin per R-Charge

Consider the states obtained by filling the highest-weight orbitals:

$$|\Psi_n\rangle = \psi^\dagger_{j-n+1} \cdots \psi^\dagger_{j-1}\, \psi^\dagger_j\, |0\rangle$$

These have the **maximum $J_3$ eigenvalue** for their given R-charge. In the fuzzy sphere picture, they correspond to filling a **spherical cap** around the north pole:

- **Two regimes:**
  - **Linear energy** for $n \leq (j-1)/2$: the cap is small, and the energy grows linearly with n.
  - **Nonlinear energy** for $n > (j-1)/2$: the cap extends past the equator, and the energy becomes nonlinear.

### 3.5 Large SU(2) Charge --- Emergent CFT\_2 (Most Novel Result)

This is the most striking finding of the paper. Consider states near **maximal $J_3$**, obtained by filling the northern hemisphere of the fuzzy sphere (all orbitals with $m > 0$). The excitations above this half-filled state are **edge modes along the equator**, which organize into a **chiral 1+1 dimensional conformal field theory**.

**Bosonization:** The edge mode field decomposes as:

$$\varphi = \varphi_z + \varphi_+ + \varphi_-$$

where:
- $\varphi_z$ has Fourier modes with momenta $\equiv 0 \pmod{3}$
- $\varphi_+$ has modes $\equiv +1 \pmod{3}$
- $\varphi_-$ has modes $\equiv -1 \pmod{3}$

**Key structural result:** The supercharge Q **only involves $\varphi_z$**, so the Hamiltonian factorizes:

$$H = \frac{\mathsf{J}\, 6\sqrt{3}}{\pi j}\, \tilde{L}_0^z$$

where $\tilde{L}_0^z$ is the Virasoro zero-mode of the $\varphi_z$ sector alone. The Hilbert space factorizes:

$$\mathcal{H} = \mathcal{H}^z \otimes \mathcal{H}^\pm$$

**BPS states** in this regime are the vacuum of $\varphi_z$ tensored with **all** states in $\mathcal{H}^\pm$. The BPS partition function is:

$$Z_{\text{BPS}} = 2 \prod_{k \geq 0} \frac{1}{(1 - q^{1+3k})(1 - q^{2+3k})}$$

This exhibits **Cardy-like growth** of BPS state degeneracies, with the asymptotic number of BPS states growing exponentially.

---

## 4. Hilbert Space Structure

- **Total dimension:** $2^{2j+1}$
- **$J_3$ counting:** $\text{Tr}[e^{i\theta J_3}] = \prod_{m=-j}^{j} (1 + e^{i\theta m})$
- **Maximum spin:** $\ell_{\max} = j(j+1)/2$
- **Gaussian approximation** for small $|n|$ (where n is the $J_3$ eigenvalue):
$$d_n \approx \frac{2^{2j+1}}{\sigma\sqrt{2\pi}} \exp\left(-\frac{n^2}{2\sigma^2}\right), \qquad \sigma = \sqrt{j^3/6}$$
- **Near-maximal $J_3$:** the density of states resembles that of a $c = 1$ CFT, consistent with the emergent chiral boson.

---

## 5. BPS States

### Witten Index with Z\_3 Grading

The standard Witten index $\text{Tr}[(-1)^F]$ vanishes. Instead, one uses a **$\mathbb{Z}_3$-graded** Witten index:

$$W_r = \omega^{-(2j+1)/2} (1 - \omega^r)^{2j+1}$$

where $\omega = e^{2\pi i/3}$ and $r = 1, 2$.

### BPS Degeneracies

- **Assumption (supported by numerics):** most BPS states concentrate at $R = \pm 1/6$, yielding a total BPS degeneracy $D^{\text{BPS}} = 3^j$.
- A **BPS partition function** can be computed from an integral formula that matches the emergent CFT\_2 prediction at large SU(2) charge.
- **Sporadic BPS states** at unusual R-charges: states at $R = \pm 1/2$ appear for $j = 7, 9$, and states at $R = \pm 5/6$ appear for $j = 9$.

---

## 6. Exact Diagonalization

Numerical diagonalization is performed up to **j = 11**, corresponding to a Hilbert space of dimension **8,388,608** ($= 2^{23}$).

### Computational Strategy

- Exploit **SO(3) symmetry** and **R-charge conservation** to block-diagonalize.
- Largest block encountered: **32,540 states**.

### Results

- **Spectral form factor** exhibits the characteristic **ramp-and-plateau** structure, a hallmark of quantum chaos and random matrix universality.
- **Convergence to Schwarzian predictions** is slower than in the disordered SYK model. This is attributed to the $(\log j)/j$ corrections from the 12j symbol, rather than the $1/N$ corrections of SYK.
- The BPS state counts and energy spectra match the analytical predictions across all regimes.

---

## 7. Connections to Other Physics

### Fuzzy Sphere and Quantum Hall Physics

The model has a natural interpretation in terms of a **fuzzy sphere** (the noncommutative geometry associated with a spin-j representation). The fermions $\psi_m$ correspond to orbitals on the sphere in the **lowest Landau level** of a magnetic monopole. The interaction, being the highest Haldane pseudopotential (spin-j channel only), is the most repulsive short-range interaction --- exactly the type that appears in **fractional quantum Hall** physics. The Haldane pseudopotential decomposition of the Hamiltonian makes this connection precise.

### Edge Modes and Chiral CFT

The emergent 1+1d CFT at large SU(2) charge is directly analogous to the **chiral edge modes** of a quantum Hall droplet. Filling the northern hemisphere of the fuzzy sphere creates a droplet whose boundary supports gapless excitations --- a chiral boson living on the equator. The decomposition into $\varphi_z, \varphi_\pm$ sectors (by momentum mod 3) reflects the cubic nature of the interaction.

### Landau Level Intuition for Melonic Dominance

The suppression of non-melonic diagrams has a beautiful geometric explanation. On the fuzzy sphere, momentum conservation forces the three momenta at each interaction vertex to form a closed triangle. For the lowest Landau level, these triangles are constrained to be nearly equilateral. Melonic diagrams, which can be drawn with two interaction vertices connected by three propagators, maximize the available internal degrees of freedom (each propagator independently sums over the sphere). Non-planar topologies like the tetrahedron impose additional constraints that reduce the phase space.

### Relation to Tensor Models

The model fits into the broader program of **tensor models without disorder** initiated by Witten and Klebanov-Tarnopolsky (2016). Those models used rank-3 tensors with O(N)^3 symmetry; this model instead uses the 3j symbol of a single SU(2), achieving melonic dominance through the special properties of angular momentum coupling rather than through a large tensor symmetry group. The original observation that 3j symbols could play this role goes back to **Amit and Roginsky (1979)**, with further development by **Benedetti et al. (2020)**.

### N = 2 SUSY SYK

The disordered counterpart is the **N = 2 supersymmetric SYK model** of Fu, Gaiotto, Maldacena, and Sachdev (2016). The present model reproduces the same:
- Schwinger-Dyson equations (in the melonic limit)
- Super-Schwarzian low-energy effective action
- Conformal dimensions ($\Delta_\psi = 1/6$)
- BPS structure

The advantage is that the deterministic coupling allows study of individual energy levels, spectral statistics, and SU(2) quantum numbers --- none of which are accessible in the disorder-averaged theory.

---

## 8. Key References

| Reference | Description |
|-----------|-------------|
| Sachdev-Ye (1993), Kitaev (2015) | Original SYK model with random couplings |
| Fu-Gaiotto-Maldacena-Sachdev (2016) | N = 2 supersymmetric SYK model |
| Witten (2016), Klebanov-Tarnopolsky (2016) | Tensor models without disorder (melonic dominance) |
| Amit-Roginsky (1979) | Original use of 3j symbols in field-theoretic models |
| Benedetti et al. (2020) | 3j-symbol tensor models, large-N analysis |
| Haldane (1983) | Pseudopotential description of quantum Hall interactions |
| Stanford-Witten (2017) | Schwarzian theory and JT gravity |

---

## 9. Summary of Main Results

1. **A concrete, disorder-free model** with N = 2 SUSY that is melonically dominated for large j, reproducing SYK physics.

2. **Melonic dominance** arises from properties of the 3j symbol; the first correction is suppressed by $(\log j)/j$ (from a 12j symbol), not $1/N$.

3. **Near-conformal dynamics** at low energy governed by the N = 2 super-Schwarzian, with computable corrections.

4. **Emergent chiral CFT** at large SU(2) charge: edge modes on the fuzzy sphere organize into a c = 1 chiral boson, with the Hilbert space factorizing into a sector controlled by the supercharge and a free sector whose states are all BPS.

5. **BPS degeneracy** $D^{\text{BPS}} = 3^j$ with Cardy-like growth, and sporadic BPS states at unusual charges for small j.

6. **Exact diagonalization** up to j = 11 confirms analytical predictions and reveals quantum chaotic behavior (ramp-and-plateau in the spectral form factor).
