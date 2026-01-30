# Hybrid Strategy: Archimedean Closure via State Duality (Revised v2)

## 2. Boundedness Lemma and Cone Structure

**2.1. Lemma**: For any $\varphi \in S_M$ and $a \in A_0$:
$$|\varphi(a)|^2 \leq \varphi(a^*a) \leq N_a$$
where $N_a$ is the Archimedean bound for $a$.

**2.2. Proof of 2.1**:

**2.2.1.** *First inequality*: Define the sesquilinear form $\langle x, y \rangle_\varphi := \varphi(x^*y)$.

**2.2.1.1.** Since $x^*x \in M$ (taking $a_1 = x$, all other terms zero in 1.2), we have $\varphi(x^*x) \geq 0$.

**2.2.1.2.** Hence the form is positive semidefinite.

**2.2.1.3.** Cauchy–Schwarz gives:
$$|\varphi(a)|^2 = |\langle 1, a \rangle_\varphi|^2 \leq \langle 1,1 \rangle_\varphi \langle a,a \rangle_\varphi = \varphi(1)\varphi(a^*a) = \varphi(a^*a)$$

**2.2.2.** *Second inequality*: By 1.3, $N_a \cdot 1 - a^*a \in M$. Hence $\varphi(N_a \cdot 1 - a^*a) \geq 0$, yielding $\varphi(a^*a) \leq N_a$. ∎

**2.3. Lemma**: $M \cap (A_0)_{\mathrm{sa}}$ is a generating cone for $(A_0)_{\mathrm{sa}}$.

**2.3.1. Proof**: For any self-adjoint $x \in (A_0)_{\mathrm{sa}}$:
$$x = \frac{1}{4}(1+x)^*(1+x) - \frac{1}{4}(1-x)^*(1-x)$$

**2.3.1.1.** Both $(1+x)^*(1+x)$ and $(1-x)^*(1-x)$ are sums of a single $a^*a$ term.

**2.3.1.2.** By definition 1.2, each lies in $M$.

**2.3.1.3.** Since $x$ is self-adjoint, both terms are self-adjoint, hence in $M \cap (A_0)_{\mathrm{sa}}$.

**2.3.1.4.** Therefore every self-adjoint element is a difference of two elements in $M \cap (A_0)_{\mathrm{sa}}$. ∎

**2.4. Corollary**: Any M-positive state is $\|\cdot\|_M$-continuous.

**2.4.1. Proof**: Let $\varphi \in S_M$ and $a \in A_0$.

**2.4.1.1.** By definition 4.1, $\|a\|_M = \sup_{\psi \in S_M} |\psi(a)|$.

**2.4.1.2.** Since $\varphi \in S_M$, we have $|\varphi(a)| \leq \sup_{\psi \in S_M} |\psi(a)| = \|a\|_M$.

**2.4.1.3.** Hence $\varphi$ is $\|\cdot\|_M$-continuous with Lipschitz constant $1$. ∎
