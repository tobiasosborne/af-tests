# Hybrid Strategy: Archimedean Closure via State Duality (Revised v2)

## 4. Seminorm and Closure

**4.1.** Define the seminorm on $A_0$:
$$\|a\|_M := \sup_{\varphi \in S_M} |\varphi(a)|$$

**4.2.** By 2.1, $\|a\|_M \leq \sqrt{N_a} < \infty$.

**4.3.** Define $\bar{M} :=$ closure of $M$ with respect to $\|\cdot\|_M$.

**4.4. Lemma**: $\bar{M}$ is a closed convex cone in $(A_0, \|\cdot\|_M)$.

**4.5. Proof of 4.4**:
  - *Cone*: $\lambda m \in M$ for $\lambda \geq 0$, $m \in M$ (immediate from definition 1.2).
  - *Convex*: $m_1 + m_2 \in M$ for $m_1, m_2 \in M$ (immediate).
  - *Closed*: by definition of $\bar{M}$. ∎

**4.6. Remark** (Seminorm structure): $\|\cdot\|_M$ is a seminorm, not a norm. The kernel $\mathcal{N} = \{a : \|a\|_M = 0\}$ consists of elements annihilated by all M-positive states. The theorem characterizes membership in $\bar{M}$ up to $\mathcal{N}$-equivalence.

**4.6.1.** *Clarification*: $\mathcal{N} \subseteq \bar{M}$, since for any $n \in \mathcal{N}$, $\|n - 0\|_M = 0$ and $0 \in M$.

**4.7. Lemma**: On $(A_0)_{\mathrm{sa}}$, $\|\cdot\|_M$ coincides with the constrained C\*-seminorm:
$$\|a\|_{C^*} := \sup_{\pi} \|\pi(a)\|$$
where the supremum is taken over all constrained \*-representations $\pi$ (Definition 1.5).

**4.7.1. Proof**:

**4.7.1.1.** ($\|a\|_{C^*} \leq \|a\|_M$): Let $\pi$ be a constrained representation and $\xi \in \mathcal{H}$ a unit vector. Define $\varphi_\xi(a) := \langle \xi, \pi(a)\xi \rangle$.

**4.7.1.2.** *Claim*: $\varphi_\xi \in S_M$.
  - $\varphi_\xi(1) = \|\xi\|^2 = 1$. ✓
  - For $m = \sum_i a_i^* a_i + \sum_{j,k} b_{jk}^* g_j b_{jk} \in M$:
    - $\varphi_\xi(a_i^* a_i) = \|\pi(a_i)\xi\|^2 \geq 0$
    - $\varphi_\xi(b_{jk}^* g_j b_{jk}) = \langle \pi(b_{jk})\xi, \pi(g_j)\pi(b_{jk})\xi \rangle \geq 0$ since $\pi(g_j) \geq 0$
  - Hence $\varphi_\xi(m) \geq 0$. ✓

**4.7.1.3.** Therefore $|\varphi_\xi(a)| \leq \|a\|_M$ for all unit vectors $\xi$, giving $\|\pi(a)\| \leq \|a\|_M$.

**4.7.1.4.** Taking supremum over all constrained $\pi$: $\|a\|_{C^*} \leq \|a\|_M$.

**4.7.2.** ($\|a\|_M \leq \|a\|_{C^*}$ for $a \in (A_0)_{\mathrm{sa}}$): Let $\varphi \in S_M$.

**4.7.2.1.** By GNS construction, $\varphi$ arises as a vector state from $\pi_\varphi$: $\varphi(a) = \langle \Omega_\varphi, \pi_\varphi(a) \Omega_\varphi \rangle$.

**4.7.2.2.** $\pi_\varphi$ is a constrained representation (proved in 6.2.1).

**4.7.2.3.** For self-adjoint $a$, spectral theory gives $\|\pi_\varphi(a)\| = \sup_{\|\xi\|=1} |\langle \xi, \pi_\varphi(a)\xi \rangle|$.

**4.7.2.4.** Hence $|\varphi(a)| \leq \|\pi_\varphi(a)\| \leq \|a\|_{C^*}$.

**4.7.2.5.** Taking supremum over $\varphi \in S_M$: $\|a\|_M \leq \|a\|_{C^*}$ for $a \in (A_0)_{\mathrm{sa}}$. ∎
