# Wilde's Conjecture: Path-Integral Representation via Interpolation

## Lamport Hierarchical Proof Document — Version 3.0 (Skeleton)

**Date:** 2026-02-07
**Status:** Skeleton — highest-level structure only. Sub-proofs suppressed.
**Change from v2:** Corrected normalisation of the Frenkel kernel. The reference operator $\tau(t) = \mathbb{1}_A \otimes \rho(t)_B$ has trace $d_A$, not $1$. This replaces the kernel $[\gamma(1+\gamma)]^{-1}$ with $[\gamma(1 + d_A\gamma)]^{-1}$ throughout.

---

## §0. Notation and Definitions

### §0.1 Hilbert Spaces

- $\mathcal{H}_A, \mathcal{H}_B$: finite-dimensional complex Hilbert spaces.
- $d_A := \dim\mathcal{H}_A$, $d_B := \dim\mathcal{H}_B$.
- $\mathcal{H}_{AB} := \mathcal{H}_A \otimes \mathcal{H}_B$, dimension $d_{AB} = d_A d_B$.
- $\mathbb{1}_X$: identity on $\mathcal{H}_X$.

### §0.2 Operators

- $X \geq 0$: positive semidefinite (PSD).
- $X > 0$: strictly positive definite (full rank).
- Positive part: for Hermitian $X = \sum_i \lambda_i |e_i\rangle\langle e_i|$, define $X_+ := \sum_{\lambda_i > 0} \lambda_i |e_i\rangle\langle e_i|$.
- Spectral projector: $\mathbf{1}\{X > 0\} := \sum_{\lambda_i > 0} |e_i\rangle\langle e_i|$.
- Trace norm: $\|X\|_1 := \operatorname{Tr}\sqrt{X^\dagger X}$.

### §0.3 States

- Density operator: $\rho \geq 0$, $\operatorname{Tr}[\rho] = 1$. Set of density operators: $\mathcal{D}(\mathcal{H})$.
- Partial trace: $\rho_B := \operatorname{Tr}_A[\rho_{AB}]$.
- Trace distance: $T(\rho,\sigma) := \tfrac{1}{2}\|\rho - \sigma\|_1$.

### §0.4 Entropic Quantities

- Von Neumann entropy: $S(\rho) := -\operatorname{Tr}[\rho\log\rho]$. Natural logarithm throughout. Convention $0\log 0 := 0$.
- Conditional entropy: $H(A|B)_\rho := S(\rho_{AB}) - S(\rho_B)$.
- Relative entropy (Umegaki): $D(\rho\|\sigma) := \operatorname{Tr}[\rho(\log\rho - \log\sigma)]$ when $\operatorname{supp}(\rho) \subseteq \operatorname{supp}(\sigma)$; else $+\infty$.
- Binary entropy: $h_2(\varepsilon) := -\varepsilon\log\varepsilon - (1-\varepsilon)\log(1-\varepsilon)$.
- Key identity:

$$H(A|B)_\rho = -D(\rho_{AB} \| \mathbb{1}_A \otimes \rho_B) \tag{CE-RE}$$

> **⟨0.4⟩ PROOF of (CE-RE).** $D(\rho_{AB}\|\mathbb{1}_A \otimes \rho_B) = \operatorname{Tr}[\rho_{AB}\log\rho_{AB}] - \operatorname{Tr}[\rho_{AB}(\mathbb{1}_A \otimes \log\rho_B)]$ using $\log(\mathbb{1}_A \otimes \rho_B) = \mathbb{1}_A \otimes \log\rho_B$. The second term equals $\operatorname{Tr}[\rho_B\log\rho_B] = -S(\rho_B)$ by the partial trace. Hence $D = -S(\rho_{AB}) + S(\rho_B) = -H(A|B)_\rho$. $\square$
>
> **⟨0.4⟩ NOTE.** The normalisation subtlety arises not here but when applying the Frenkel integral formula (FR-1) — which requires trace-1 second argument — to $\tau = \mathbb{1}_A \otimes \rho_B$ with $\operatorname{Tr}[\tau] = d_A$. This changes the integration kernel; see §0.7.

### §0.5 Hockey-Stick Divergence

For PSD operators $\rho, \sigma$ and threshold $\gamma > 0$:

$$E_\gamma(\rho\|\sigma) := \operatorname{Tr}(\rho - \gamma\sigma)_+$$

SDP form: $E_\gamma(\rho\|\sigma) = \max_{0 \leq M \leq \mathbb{1}} \operatorname{Tr}[M(\rho - \gamma\sigma)]$. The maximiser is $P_\gamma = \mathbf{1}\{\rho - \gamma\sigma > 0\}$.

### §0.6 Frenkel's Integral Representation (Normalised Form)

For density operators $\rho, \sigma$ (both trace-1) with $\operatorname{supp}(\rho) \subseteq \operatorname{supp}(\sigma)$:

$$D(\rho\|\sigma) = \int_0^\infty \frac{E_\gamma(\rho\|\sigma) - (1-\gamma)_+}{\gamma(1+\gamma)}\,d\gamma \tag{FR-1}$$

### §0.7 Frenkel's Representation for Unnormalised Reference

> **⟨0.7⟩ LEMMA.** Let $\rho$ be a density operator ($\operatorname{Tr}[\rho] = 1$) and $\tau \geq 0$ with $\operatorname{Tr}[\tau] = c > 0$ and $\operatorname{supp}(\rho) \subseteq \operatorname{supp}(\tau)$. Define $\omega := \tau/c$, so $\operatorname{Tr}[\omega] = 1$. Then:
>
> $$D(\rho\|\tau) = D(\rho\|\omega) - \log c = \int_0^\infty \frac{E_\gamma(\rho\|\omega) - (1-\gamma)_+}{\gamma(1+\gamma)}\,d\gamma - \log c$$
>
> Substituting $E_\gamma(\rho\|\omega) = E_\gamma(\rho\|\tau/c) = E_{\gamma/c}(\rho\|\tau)$ and changing variable $\beta = \gamma/c$:
>
> $$\boxed{D(\rho\|\tau) = \int_0^\infty \frac{E_\beta(\rho\|\tau) - (1 - c\beta)_+}{\beta\,(1 + c\beta)}\,d\beta \;-\; \log c} \tag{FR-c}$$

> **⟨0.7⟩ COROLLARY.** For bipartite states: set $\tau = \mathbb{1}_A \otimes \rho_B$, $c = d_A$:
>
> $$D(\rho_{AB}\|\mathbb{1}_A \otimes \rho_B) = \int_0^\infty \frac{E_\gamma(\rho_{AB}\|\mathbb{1}_A \otimes \rho_B) - (1 - d_A\gamma)_+}{\gamma(1 + d_A\gamma)}\,d\gamma - \log d_A \tag{FR-bip}$$
>
> The integration kernel is $[\gamma(1 + d_A\gamma)]^{-1}$, **not** $[\gamma(1+\gamma)]^{-1}$.

### §0.8 Max-Relative Entropy

$$M(\rho,\sigma) := \inf\{\lambda \geq 0 : \rho \leq \lambda\sigma\}$$

For bipartite states: $M(\rho_{AB}, \mathbb{1}_A \otimes \rho_B) \leq d_A$.

> **⟨0.8⟩ NOTE on the bound.** $\rho_{AB} \leq d_A(\mathbb{1}_A \otimes \rho_B)$ for any bipartite state. This is the standard operator inequality from the partial trace. Hence $E_\gamma(\rho_{AB}\|\mathbb{1}_A\otimes\rho_B) = 0$ for $\gamma \geq d_A$, and the upper limit of integration in (FR-bip) is effectively $d_A$.

---

## §1. Statement of the Conjecture

**Conjecture (Wilde).** Let $\rho_{AB}, \sigma_{AB} \in \mathcal{D}(\mathcal{H}_{AB})$ with $T(\rho_{AB}, \sigma_{AB}) \leq \varepsilon$ where $0 \leq \varepsilon \leq 1 - 1/d_A^2$. Then:

$$|H(A|B)_\rho - H(A|B)_\sigma| \leq \varepsilon\log(d_A^2 - 1) + h_2(\varepsilon)$$

---

## §2. The Interpolating Path

> **⟨2⟩ DEFINITION.** Define:
> - $\rho(t) := (1-t)\,\rho_{AB} + t\,\sigma_{AB}$, $\quad t \in [0,1]$
> - $\delta_{AB} := \sigma_{AB} - \rho_{AB}$ (traceless Hermitian, the perturbation)
> - $\delta_B := \sigma_B - \rho_B = \operatorname{Tr}_A[\delta_{AB}]$
> - $\rho(t)_B := \operatorname{Tr}_A[\rho(t)] = (1-t)\rho_B + t\sigma_B$
> - $\tau(t) := \mathbb{1}_A \otimes \rho(t)_B$ (the conditional reference; $\operatorname{Tr}[\tau(t)] = d_A$)
> - $\omega(t) := \tau(t)/d_A = \frac{1}{d_A}\mathbb{1}_A \otimes \rho(t)_B$ (normalised reference; $\operatorname{Tr}[\omega(t)] = 1$)

> **⟨2⟩ ASSUMPTION (Full rank).** $\rho_{AB}, \sigma_{AB} > 0$. This ensures $\rho(t) > 0$, $\rho(t)_B > 0$ for all $t \in [0,1]$.

**Key properties:**
- $\dot\rho(t) = \delta_{AB}$, $\dot\rho(t)_B = \delta_B$, $\dot\tau(t) = \mathbb{1}_A \otimes \delta_B$, $\dot\omega(t) = \frac{1}{d_A}\mathbb{1}_A \otimes \delta_B$.
- $\frac{1}{2}\|\delta_{AB}\|_1 = T(\rho,\sigma) \leq \varepsilon$.

---

## §3. Derivative of Conditional Entropy

> **⟨3⟩ PROPOSITION.** Under the full-rank assumption:
> $$\frac{d}{dt} H(A|B)_{\rho(t)} = \operatorname{Tr}\!\Big[\delta_{AB}\Big(\mathbb{1}_A \otimes \log\rho(t)_B - \log\rho(t)_{AB}\Big)\Big] \tag{DER}$$

*Proof sketch.* Use $H(A|B)_{\rho(t)} = -D(\rho(t)\|\tau(t))$ and differentiate $D(\rho(t)\|\tau(t))$ as a sum of two terms. The first gives $\operatorname{Tr}[\delta_{AB}\log\rho(t)]$ (using the Fréchet derivative identity $\operatorname{Tr}[\rho\,D_{\log}(\rho)[H]] = \operatorname{Tr}[H]$ and $\operatorname{Tr}[\delta_{AB}] = 0$). The second gives $\operatorname{Tr}[\delta_B\log\rho(t)_B]$ (the Fréchet derivative of $\log\tau(t)$ contributes $\operatorname{Tr}[\rho(t)_B\,D_{\log}(\rho(t)_B)[\delta_B]] = \operatorname{Tr}[\delta_B] = 0$). Combining yields (DER). $\square$

> **⟨3⟩ COROLLARY (FTC).**
> $$H(A|B)_\sigma - H(A|B)_\rho = \int_0^1 \frac{d}{dt}H(A|B)_{\rho(t)}\,dt \tag{FTC}$$

---

## §4. Hockey-Stick Form of the Derivative

### §4.1 Derivative of the Hockey-Stick Divergence

> **⟨4.1⟩ LEMMA.** For smooth families $A(t), B(t)$ with $B(t) > 0$, at generic $\gamma$ (no zero eigenvalue of $A(t) - \gamma B(t)$):
> $$\frac{d}{dt}\operatorname{Tr}(A(t) - \gamma B(t))_+ = \operatorname{Tr}\!\big[P_\gamma(t)\,(\dot A(t) - \gamma\dot B(t))\big]$$
> where $P_\gamma(t) := \mathbf{1}\{A(t) - \gamma B(t) > 0\}$.

### §4.2 Substituting the Corrected Frenkel Formula

> **⟨4.2⟩ PROPOSITION.** For each $t \in [0,1]$:
> $$\frac{d}{dt}D(\rho(t)\|\tau(t)) = \int_0^{M(t)} \frac{\operatorname{Tr}\!\big[P_\gamma(t)\,\delta_{AB}^{(\gamma)}\big]}{\gamma(1 + d_A\gamma)}\,d\gamma \tag{DER-HS}$$
>
> where:
> - $P_\gamma(t) := \mathbf{1}\{\rho(t) - \gamma\,\tau(t) > 0\} = \mathbf{1}\{\rho(t)_{AB} - \gamma\,\mathbb{1}_A \otimes \rho(t)_B > 0\}$
> - $\delta_{AB}^{(\gamma)} := \delta_{AB} - \gamma\,\mathbb{1}_A \otimes \delta_B$ (the "conditional perturbation" at threshold $\gamma$)
> - $M(t) := M(\rho(t)_{AB},\,\mathbb{1}_A \otimes \rho(t)_B) \leq d_A$

*Proof sketch.* Differentiate (FR-bip) under the integral sign (justified by dominated convergence). The term $(1 - d_A\gamma)_+$ and $\log d_A$ are $t$-independent, so drop out. Apply ⟨4.1⟩ with $\dot A = \delta_{AB}$, $\dot B = \mathbb{1}_A \otimes \delta_B$. The kernel $[\gamma(1 + d_A\gamma)]^{-1}$ is inherited from (FR-bip). The integrand vanishes for $\gamma > M(t)$. $\square$

---

## §5. The Main Result

> **⟨5⟩ THEOREM (Path-Integral Hockey-Stick Representation).** Under the full-rank assumption:
>
> $$\boxed{H(A|B)_\sigma - H(A|B)_\rho = -\int_0^1\!\int_0^{M(t)} \frac{\operatorname{Tr}\!\big[P_\gamma(t)\,\delta_{AB}^{(\gamma)}\big]}{\gamma(1 + d_A\gamma)}\,d\gamma\,dt} \tag{MAIN}$$
>
> with all symbols as defined in §2 and §4.2.

*Proof.* Combine (FTC), $H(A|B)_{\rho(t)} = -D(\rho(t)\|\tau(t))$, and (DER-HS). Fubini applies since the integrand is bounded on $[0,1] \times [0, d_A]$. $\square$

---

## §6. Structural Properties

### §6.1 Single Linear Functional

At each $(t,\gamma)$, the integrand $\Phi(t,\gamma) := \operatorname{Tr}[P_\gamma(t)\,\delta_{AB}^{(\gamma)}]$ is a single trace inner product. The projector $P_\gamma(t)$ depends only on $\rho(t)$ and its marginal, not separately on $\rho$ or $\sigma$.

### §6.2 Partial Trace of the Conditional Perturbation

> **⟨6.2⟩ LEMMA.**
> $$\operatorname{Tr}_A\!\big[\delta_{AB}^{(\gamma)}\big] = (1 - \gamma\, d_A)\,\delta_B$$
>
> *Proof.* $\operatorname{Tr}_A[\delta_{AB}^{(\gamma)}] = \operatorname{Tr}_A[\delta_{AB}] - \gamma\,\operatorname{Tr}_A[\mathbb{1}_A \otimes \delta_B] = \delta_B - \gamma\,d_A\,\delta_B$. $\square$
>
> **Consequence:** $\delta_{AB}^{(\gamma)}$ is A-traceless at $\gamma = 1/d_A$, not at $\gamma = 1$.
>
> The A-traceless conditional perturbation — the component of $\delta_{AB}$ not explained by the marginal perturbation — is:
>
> $$\delta_{AB}^{(1/d_A)} = \delta_{AB} - \frac{1}{d_A}\,\mathbb{1}_A \otimes \delta_B$$

### §6.3 Fubini Reordering

> **⟨6.3⟩ COROLLARY.**
> $$H(A|B)_\sigma - H(A|B)_\rho = -\int_0^{d_A} \frac{1}{\gamma(1 + d_A\gamma)} \left[\int_0^1 \operatorname{Tr}\!\big[P_\gamma(t)\,\delta_{AB}^{(\gamma)}\big]\,dt\right] d\gamma$$

---

## §7. Equivalent Formulation with Normalised Reference

> **⟨7⟩ REMARK.** If one prefers the standard $[\gamma(1+\gamma)]^{-1}$ kernel, work with the normalised reference $\omega(t) = \tau(t)/d_A$. Define:
> - $\tilde{P}_\gamma(t) := \mathbf{1}\{\rho(t) - \gamma\,\omega(t) > 0\} = P_{\gamma/d_A}(t)$
> - $\tilde{M}(t) := M(\rho(t), \omega(t)) = d_A\, M(t) \leq d_A^2$
>
> Then:
> $$H(A|B)_\sigma - H(A|B)_\rho = -\int_0^1\!\int_0^{\tilde{M}(t)} \frac{\operatorname{Tr}\!\big[\tilde{P}_\gamma(t)\,(\delta_{AB} - \tfrac{\gamma}{d_A}\,\mathbb{1}_A\otimes\delta_B)\big]}{\gamma(1+\gamma)}\,d\gamma\,dt$$
>
> This form has the standard kernel but a rescaled perturbation and upper limit $d_A^2$.

---

## §8. Open Obligations

| ID | Description | Status |
|----|-------------|--------|
| O1 | Justify $d/dt \leftrightarrow \int d\gamma$ exchange (dominated convergence) | OPEN (routine) |
| O2 | Non-full-rank regularisation | OPEN (standard) |
| O3 | Bound $\lvert\int_0^1 \operatorname{Tr}[P_\gamma(t)\,\delta_{AB}^{(\gamma)}]\,dt\rvert$ as function of $\gamma$ and $\varepsilon$ | OPEN — key question |
| O4 | Numerical verification of (MAIN) for small systems | OPEN |
| O5 | Evaluate $\int_0^{d_A} f(\gamma)\,[\gamma(1+d_A\gamma)]^{-1}\,d\gamma$ for the bound from O3 | OPEN |

---

## §9. References

1. Wilde (2018): M. M. Wilde, "Optimized quantum $f$-divergences and data processing," J. Phys. A 51, 374002.
2. Berta–Lami–Tomamichel (2024): M. Berta, L. Lami, M. Tomamichel, "Continuity of entropies via integral representations," arXiv:2408.15226v2.
3. Frenkel (2022): P. E. Frenkel, "Integral formula for quantum relative entropy implies data processing inequality," Quantum 7, 1102.
4. Liu–Hirche–Cheng (2025): P.-C. Liu, C. Hirche, H.-C. Cheng, "Layer Cake Representations for Quantum Divergences," arXiv:2507.07065v2.
5. Audenaert (2007): K. M. R. Audenaert, "A sharp continuity estimate for the von Neumann entropy," J. Phys. A 40, 8127.
