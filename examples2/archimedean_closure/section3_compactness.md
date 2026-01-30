# Hybrid Strategy: Archimedean Closure via State Duality (Revised v2)

## 3. Compactness of $S_M$

**3.1.** Equip $(A_0)^*$ with the topology of pointwise convergence.

**3.2.** By 2.1, for each $a \in A_0$, the image $\varphi(a)$ lies in a bounded disk: $|\varphi(a)| \leq \sqrt{N_a}$.

**3.3.** Hence $S_M \subseteq \prod_{a \in A_0} D_{\sqrt{N_a}}(0)$, which is compact by Tychonoff.

**3.4.** $S_M$ is closed in this topology: it equals
$$\bigcap_{m \in M} \{\varphi : \varphi(m) \geq 0\} \cap \{\varphi : \varphi(1) = 1\}$$

**3.4.1.** Each set $\{\varphi : \varphi(m) \geq 0\}$ is the preimage of $[0, \infty)$ under the continuous evaluation map $\varphi \mapsto \varphi(m)$.

**3.4.2.** Each such set is closed.

**3.5.** Closed subset of compact $\Longrightarrow$ $S_M$ is compact. ∎
