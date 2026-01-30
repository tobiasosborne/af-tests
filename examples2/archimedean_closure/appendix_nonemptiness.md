# Hybrid Strategy: Archimedean Closure via State Duality (Revised v2)

## Appendix: Non-emptiness of $S_M$

**A.1. Lemma**: $S_M \neq \emptyset$.

**A.2. Proof**: Define $\varphi_0 : A_0 \to \mathbb{C}$ as the "scalar extraction" functional: for $a = \sum_w c_w w$ (where $w$ ranges over words in generators), set $\varphi_0(a) = c_{\emptyset}$ (coefficient of the empty word).

**A.2.1.** $\varphi_0(1) = 1$. ✓

**A.2.2.** For $m = \sum_i a_i^* a_i + \sum_{j,k} b_{jk}^* g_j b_{jk} \in M$:

**A.2.2.1.** The scalar part of $a_i^* a_i$ where $a_i = \sum_\alpha c_\alpha w_\alpha$: The product $a_i^* a_i = \sum_{\alpha,\beta} \bar{c}_\alpha c_\beta \tilde{w}_\alpha w_\beta$ contributes to the scalar only when $\tilde{w}_\alpha w_\beta = \emptyset$, i.e., $w_\beta = w_\alpha$. Hence the scalar part is $\sum_\alpha |c_\alpha|^2 \geq 0$.

**A.2.2.2.** The scalar part of $b_{jk}^* g_j b_{jk}$: The product always contains at least $g_j$, so it never equals the empty word. Hence the scalar part is $0$.

**A.2.3.** Therefore $\varphi_0(m) = \sum_i \sum_\alpha |c_\alpha^{(i)}|^2 \geq 0$. ✓

**A.2.4.** Hence $\varphi_0 \in S_M$. ∎

---

## Revision Notes

This revision addresses the following issues identified in critical review:

1. **Corollary 2.4**: Proof rewritten. The continuity follows directly from the definition: $|\varphi(a)| \leq \sup_{\psi \in S_M}|\psi(a)| = \|a\|_M$ for $\varphi \in S_M$.

2. **Lemma 4.7**: Explicitly stated that the C\*-seminorm is taken over *constrained* representations (Definition 1.5 added). The inequality $\|a\|_{C^*} \leq \|a\|_M$ in 4.7.1.3–4 now correctly uses that vector states from constrained representations are M-positive.

3. **Step 5.3.3.3**: Added missing case 5.3.3.3.2 ($\lambda < 0$), showing it reduces to the $-A \in M$ case via cone closure.

4. **Step 5.3.4**: Riesz extension now cites specific theorem (Riesz–Kantorovich, with reference to Aliprantis–Tourky) and notes dependence on Zorn's lemma.

5. **Step 5.3.7.3**: Removed (was unnecessary for the proof and confused logical dependencies).

6. **Section 6.2.1.1**: Fixed normalization notation with explicit formula and stated assumption that $b \notin \mathcal{N}_\varphi$.

7. **Section 4.6.1**: Added clarification that $\mathcal{N} \subseteq \bar{M}$.
