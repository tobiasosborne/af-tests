# Hybrid Strategy: Archimedean Closure via State Duality (Revised v2)

## 5. Dual Characterization

**5.1. Theorem**: For self-adjoint $A \in (A_0)_{\mathrm{sa}}$:
$$A \in \bar{M} \iff \varphi(A) \geq 0 \ \forall \varphi \in S_M$$

**5.2. Proof of ($\Longrightarrow$)**:

**5.2.1.** Suppose $A \in \bar{M}$. Then $\exists$ sequence $(m_n) \subset M$ with $\|A - m_n\|_M \to 0$.

**5.2.2.** For any $\varphi \in S_M$: $|\varphi(A) - \varphi(m_n)| = |\varphi(A - m_n)| \leq \|A - m_n\|_M \to 0$.

**5.2.3.** Hence $\varphi(A) = \lim_n \varphi(m_n) \geq 0$, since $\varphi(m_n) \geq 0$ for all $n$. ∎

**5.3. Proof of ($\Longleftarrow$)**:

**5.3.1.** Suppose $\varphi(A) \geq 0$ for all $\varphi \in S_M$, but $A \notin \bar{M}$.

**5.3.2.** Since $\bar{M}$ is closed and $A \notin \bar{M}$, by definition of closure:
$$\varepsilon := \inf_{m \in \bar{M}} \|A - m\|_M > 0$$

**5.3.3.** *Construction of separating functional on* $\mathrm{span}\{A\}$:

**5.3.3.1.** Define $\psi_0 : \mathrm{span}\{A\} \to \mathbb{R}$ by $\psi_0(\lambda A) = -\lambda \varepsilon$ for $\lambda \in \mathbb{R}$.

**5.3.3.2.** *Claim*: $M \cap \mathrm{span}\{A\} = \{0\}$.

**5.3.3.3.** *Proof of 5.3.3.2*: We show no nonzero multiple of $A$ lies in $M$.

**5.3.3.3.1.** *Case* $\lambda > 0$ *and* $\lambda A \in M$: Then $A = (1/\lambda)(\lambda A) \in M$ since $M$ is a cone. But $M \subseteq \bar{M}$, contradicting $A \notin \bar{M}$.

**5.3.3.3.2.** *Case* $\lambda < 0$ *and* $\lambda A \in M$: Then $-A = (1/|\lambda|)(\lambda A) \in M$ since $M$ is a cone (and $1/|\lambda| > 0$). This reduces to case 5.3.3.3.3.

**5.3.3.3.3.** *Case* $-A \in M$: If $-A \in M$, then $\varphi(-A) \geq 0$ for all $\varphi \in S_M$, so $\varphi(A) \leq 0$. Combined with hypothesis $\varphi(A) \geq 0$, we get $\varphi(A) = 0$ for all $\varphi \in S_M$. Hence $\|A\|_M = 0$, so $A \in \bar{M}$ by 4.6.1. Contradiction.

**5.3.3.3.4.** Therefore $M \cap \mathrm{span}\{A\} = \{0\}$. ∎

**5.3.3.4.** *Verification*: $\psi_0 \geq 0$ on $M \cap \mathrm{span}\{A\} = \{0\}$: $\psi_0(0) = 0 \geq 0$. ✓

**5.3.4.** *Extension via Riesz–Kantorovich theorem*:

**5.3.4.1.** By 2.3, $K := M \cap (A_0)_{\mathrm{sa}}$ is a generating cone for $V := (A_0)_{\mathrm{sa}}$.

**5.3.4.2.** We have $W := \mathrm{span}\{A\} \subseteq V$ and $\psi_0 : W \to \mathbb{R}$ linear with $\psi_0 \geq 0$ on $K \cap W = \{0\}$.

**5.3.4.3.** By the Riesz–Kantorovich extension theorem (see e.g., Aliprantis–Tourky, *Cones and Duality*, Theorem 1.26): For any real vector space $V$ with generating cone $K$, any linear functional $f : W \to \mathbb{R}$ on a subspace $W$ satisfying $f \geq 0$ on $K \cap W$ extends to a linear functional $\tilde{f} : V \to \mathbb{R}$ with $\tilde{f} \geq 0$ on $K$.

**5.3.4.4.** *Remark*: The proof uses Zorn's lemma on the set of extensions ordered by domination.

**5.3.4.5.** Apply to obtain $\psi : (A_0)_{\mathrm{sa}} \to \mathbb{R}$ extending $\psi_0$ with:
  - $\psi(m) \geq 0$ for all $m \in M \cap (A_0)_{\mathrm{sa}}$
  - $\psi(A) = \psi_0(A) = -\varepsilon < 0$

**5.3.5.** *Complex extension*:

**5.3.5.1.** Define $\varphi : A_0 \to \mathbb{C}$ by $\varphi(a) = \psi(\mathrm{Re}(a)) + i\psi(\mathrm{Im}(a))$, where $\mathrm{Re}(a) = (a + a^*)/2$ and $\mathrm{Im}(a) = (a - a^*)/(2i)$.

**5.3.5.2.** *Conjugate symmetry*: $\varphi(a^*) = \psi(\mathrm{Re}(a)) - i\psi(\mathrm{Im}(a)) = \overline{\varphi(a)}$. ✓

**5.3.5.3.** *Positivity on* $M$: For $m \in M$, since $M \subseteq (A_0)_{\mathrm{sa}}$, we have $\varphi(m) = \psi(m) \geq 0$. ✓

**5.3.6.** *Normalization*: Define $\varphi_1 := \varphi / \psi(1)$.

**5.3.6.1.** *Claim*: $\psi(1) > 0$.

**5.3.6.2.** *Proof*: Since $1 = 1^* \cdot 1 \in M$, we have $\psi(1) \geq 0$.

**5.3.6.3.** Suppose $\psi(1) = 0$. By the Archimedean property 1.3, for all $a \in A_0$:
$$N_a \cdot 1 - a^*a \in M \implies 0 \leq \psi(a^*a) \leq N_a \cdot \psi(1) = 0$$

**5.3.6.4.** Hence $\psi(a^*a) = 0$ for all $a \in A_0$.

**5.3.6.5.** For self-adjoint $x$, using the identity from 2.3.1:
$$\psi(x) = \frac{1}{4}\psi((1+x)^2) - \frac{1}{4}\psi((1-x)^2) = 0 - 0 = 0$$

**5.3.6.6.** But $\psi(A) = -\varepsilon \neq 0$ where $A$ is self-adjoint. Contradiction.

**5.3.6.7.** Therefore $\psi(1) > 0$, and $\varphi_1 = \varphi/\psi(1)$ is well-defined.

**5.3.7.** *Verification that* $\varphi_1 \in S_M$:

**5.3.7.1.** $\varphi_1(1) = \varphi(1)/\psi(1) = \psi(1)/\psi(1) = 1$. ✓

**5.3.7.2.** For $m \in M$: $\varphi_1(m) = \varphi(m)/\psi(1) = \psi(m)/\psi(1) \geq 0$. ✓

**5.3.8.** *Contradiction*:

**5.3.8.1.** $\varphi_1(A) = \psi(A)/\psi(1) = -\varepsilon/\psi(1) < 0$.

**5.3.8.2.** This contradicts the hypothesis that $\varphi(A) \geq 0$ for all $\varphi \in S_M$. ∎
