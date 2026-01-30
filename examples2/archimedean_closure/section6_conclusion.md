# Hybrid Strategy: Archimedean Closure via State Duality (Revised v2)

## 6. Conclusion

**6.1.** By 5.1: $A \in \bar{M} \iff A$ is nonnegative on all M-positive states.

**6.2.** *GNS correspondence*:

**6.2.1.** Each M-positive state $\varphi$ induces (via GNS construction) a \*-representation $\pi_\varphi$ where $\pi_\varphi(g_j) \geq 0$.

**6.2.1.1.** *Proof*: Let $b \in A_0$ with $\pi_\varphi(b)\Omega_\varphi \neq 0$ (i.e., $b$ not in the GNS null space $\mathcal{N}_\varphi = \{c : \varphi(c^*c) = 0\}$). Define the unit vector:
$$\xi := \frac{\pi_\varphi(b)\Omega_\varphi}{\|\pi_\varphi(b)\Omega_\varphi\|}$$

**6.2.1.2.** Then:
$$\langle \xi, \pi_\varphi(g_j)\xi \rangle = \frac{\varphi(b^* g_j b)}{\varphi(b^* b)} \geq 0$$
since $b^* g_j b \in M$ by definition 1.2.

**6.2.1.3.** Since vectors $\pi_\varphi(b)\Omega_\varphi$ (for $b \notin \mathcal{N}_\varphi$) are dense in $\mathcal{H}_\varphi$, and $\langle \eta, \pi_\varphi(g_j)\eta \rangle \geq 0$ for all such $\eta$, we have $\pi_\varphi(g_j) \geq 0$ as an operator.

**6.2.2.** The GNS operators are bounded.

**6.2.2.1.** *Proof*: For $a \in A_0$, we need $\|\pi_\varphi(a)\| < \infty$.

**6.2.2.2.** By Archimedean property: $N_a \cdot 1 - a^*a \in M$.

**6.2.2.3.** Hence $b^*(N_a \cdot 1 - a^*a)b = N_a \cdot b^*b - (ab)^*(ab) \in M$ for any $b \in A_0$.

**6.2.2.3.1.** *Justification*: The map $x \mapsto b^* x b$ preserves $M$. For $m = \sum_i c_i^* c_i + \sum_{j,k} d_{jk}^* g_j d_{jk}$:
$$b^* m b = \sum_i (c_i b)^*(c_i b) + \sum_{j,k} (d_{jk} b)^* g_j (d_{jk} b) \in M$$

**6.2.2.4.** Therefore $\varphi((ab)^*(ab)) \leq N_a \cdot \varphi(b^*b)$.

**6.2.2.5.** This gives $\|\pi_\varphi(a)\pi_\varphi(b)\Omega_\varphi\|^2 \leq N_a \|\pi_\varphi(b)\Omega_\varphi\|^2$.

**6.2.2.6.** Hence $\|\pi_\varphi(a)\| \leq \sqrt{N_a}$.

**6.3.** Conversely, every constrained \*-representation $\pi$ (Definition 1.5) yields M-positive states via vector states $\langle \xi, \pi(\cdot)\xi \rangle$ for unit vectors $\xi$.

**6.3.1.** *Proof*: This is verified in 4.7.1.2.

**6.4. Main Theorem**:
$$A \geq 0 \text{ in all constrained *-representations} \iff A \in \bar{M}$$

**6.4.1.** *Clarification*: This characterizes positivity in the universal C\*-algebra $C^*(A_0 \mid g_j \geq 0)$, not algebraic membership in $M$.

**6.4.2.** The closure $\bar{M}$ is computed in the seminorm $\|\cdot\|_M$, which by 4.7 coincides with the constrained C\*-seminorm on self-adjoint elements. ∎
