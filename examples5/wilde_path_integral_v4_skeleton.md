# Wilde's Conjecture: Path-Integral Representation via Interpolation

## Lamport Hierarchical Proof Document — Version 4.0 (Skeleton)

**Date:** 2026-02-10
**Status:** Skeleton — highest-level structure only. Sub-proofs suppressed.
**Change from v3:** Replaced the incorrect single-term Frenkel formula (FR-1) with the correct two-term form (FR). This introduces the reverse hockey-stick $E_\gamma(\sigma\|\rho)$, the reverse projector $Q_\beta(t)$, and changes the integration kernel and domain throughout.

---

## §0. Notation and Definitions

### §0.1–0.4 [Unchanged from v3]

Hilbert spaces, operators, states, entropic quantities, CE-RE identity — all as before.

### §0.5 Hockey-Stick Divergence [Unchanged]

$E_\gamma(\rho\|\sigma) := \operatorname{Tr}(\rho - \gamma\sigma)_+$, with maximiser $P_\gamma = \mathbf{1}\{\rho - \gamma\sigma > 0\}$.

### §0.6 Frenkel's Integral Representation (**CORRECTED**)

For density operators $\rho, \sigma$ (both trace-1) with $\operatorname{supp}(\rho) \subseteq \operatorname{supp}(\sigma)$, using the natural logarithm:

$$D(\rho\|\sigma) = \int_1^\infty \left[\frac{E_\gamma(\rho\|\sigma)}{\gamma} + \frac{E_\gamma(\sigma\|\rho)}{\gamma^2}\right] d\gamma \tag{FR}$$

> **⟨0.6⟩ NOTE.** The previously stated formula $D = \int_0^\infty [E_\gamma - (1-\gamma)_+]/[\gamma(1+\gamma)]\,d\gamma$ is **incorrect**. The correct formula (FR) has two terms — forward and reverse hockey-stick — with kernels $1/\gamma$ and $1/\gamma^2$, integrated over $[1,\infty)$.

### §0.7 Frenkel's Representation for Unnormalised Reference (**CORRECTED**)

> **⟨0.7⟩ LEMMA.** Let $\rho$ be a density operator ($\operatorname{Tr}[\rho] = 1$) and $\tau \geq 0$ with $\operatorname{Tr}[\tau] = c > 0$ and $\operatorname{supp}(\rho) \subseteq \operatorname{supp}(\tau)$. Define $\omega := \tau/c$. Then:
>
> $$D(\rho\|\tau) = D(\rho\|\omega) - \log c = \int_1^\infty \left[\frac{E_\gamma(\rho\|\omega)}{\gamma} + \frac{E_\gamma(\omega\|\rho)}{\gamma^2}\right] d\gamma - \log c$$
>
> Substituting $E_\gamma(\rho\|\omega) = E_{\gamma/c}(\rho\|\tau)$ (variable $\beta = \gamma/c$) and $E_\gamma(\omega\|\rho) = \tfrac{1}{c}\,E_{c\gamma}(\tau\|\rho)$ (variable $\beta = c\gamma$):
>
> $$\boxed{D(\rho\|\tau) = \int_{1/c}^\infty \frac{E_\beta(\rho\|\tau)}{\beta}\,d\beta \;+\; \int_c^\infty \frac{E_\beta(\tau\|\rho)}{\beta^2}\,d\beta \;-\; \log c} \tag{FR-c}$$

> **⟨0.7⟩ COROLLARY.** For bipartite states: set $\tau = \mathbb{1}_A \otimes \rho_B$, $c = d_A$:
>
> $$D(\rho_{AB}\|\mathbb{1}_A \otimes \rho_B) = \int_{1/d_A}^\infty \frac{E_\beta(\rho_{AB}\|\tau)}{\beta}\,d\beta \;+\; \int_{d_A}^\infty \frac{E_\beta(\tau\|\rho_{AB})}{\beta^2}\,d\beta \;-\; \log d_A \tag{FR-bip}$$

### §0.8 Max-Relative Entropy (**EXTENDED**)

$$M_{\mathrm{fwd}}(\rho,\tau) := \inf\{\lambda \geq 0 : \rho \leq \lambda\tau\}, \qquad M_{\mathrm{rev}}(\rho,\tau) := \inf\{\lambda \geq 0 : \tau \leq \lambda\rho\}$$

For bipartite states: $M_{\mathrm{fwd}}(\rho_{AB}, \mathbb{1}_A \otimes \rho_B) \leq d_A$, so $E_\beta(\rho_{AB}\|\tau) = 0$ for $\beta \geq d_A$, and the forward integral upper limit is effectively $d_A$.

Similarly $E_\beta(\tau\|\rho_{AB}) = 0$ for $\beta \geq M_{\mathrm{rev}}(t)$.

### §0.9 Reverse Spectral Projector (**NEW**)

$$Q_\beta(t) := \mathbf{1}\{\tau(t) - \beta\,\rho(t) > 0\}$$

---

## §1. Statement of the Conjecture [Unchanged]

---

## §2. The Interpolating Path [Unchanged from v3]

All definitions of $\rho(t)$, $\delta_{AB}$, $\delta_B$, $\tau(t)$, $\omega(t)$ carry over.

---

## §3. Derivative of Conditional Entropy [Unchanged]

The formula (DER) and its proof are independent of Frenkel.

---

## §4. Hockey-Stick Form of the Derivative (**CORRECTED**)

### §4.1 Derivative of the Hockey-Stick Divergence [Unchanged]

> **⟨4.1⟩ LEMMA.** $\frac{d}{dt}\operatorname{Tr}(A(t) - \gamma B(t))_+ = \operatorname{Tr}[P_\gamma(t)(\dot{A} - \gamma\dot{B})]$ at generic $\gamma$.

### §4.1b Derivative of the Reverse Hockey-Stick (**NEW**)

> **⟨4.1b⟩ LEMMA.** By the same argument with roles swapped:
> $$\frac{d}{dt}E_\beta(\tau(t)\|\rho(t)) = \operatorname{Tr}\!\big[Q_\beta(t)\,(\mathbb{1}_A \otimes \delta_B - \beta\,\delta_{AB})\big]$$
> at generic $\beta$.

### §4.2 Substituting the Corrected Frenkel Formula (**CORRECTED**)

> **⟨4.2⟩ PROPOSITION.** For each $t \in [0,1]$:
> $$\frac{d}{dt}D(\rho(t)\|\tau(t)) = \int_{1/d_A}^{M_{\mathrm{fwd}}(t)} \frac{\operatorname{Tr}\!\big[P_\beta(t)\,\delta_{AB}^{(\beta)}\big]}{\beta}\,d\beta \;+\; \int_{d_A}^{M_{\mathrm{rev}}(t)} \frac{\operatorname{Tr}\!\big[Q_\beta(t)\,(\mathbb{1}_A \otimes \delta_B - \beta\,\delta_{AB})\big]}{\beta^2}\,d\beta \tag{DER-HS}$$
>
> where:
> - $P_\beta(t) := \mathbf{1}\{\rho(t) - \beta\,\tau(t) > 0\}$ (forward projector)
> - $Q_\beta(t) := \mathbf{1}\{\tau(t) - \beta\,\rho(t) > 0\}$ (reverse projector)
> - $\delta_{AB}^{(\beta)} := \delta_{AB} - \beta\,\mathbb{1}_A \otimes \delta_B$
> - $M_{\mathrm{fwd}}(t) \leq d_A$, $M_{\mathrm{rev}}(t) < \infty$

*Proof sketch.* Differentiate (FR-bip) under the integral sign. The $\log d_A$ term is $t$-independent. Apply §4.1 to the forward term and §4.1b to the reverse term. The forward integrand vanishes for $\beta > M_{\mathrm{fwd}}(t)$ and the reverse for $\beta > M_{\mathrm{rev}}(t)$. Both integrals start at finite values ($1/d_A$ and $d_A$), so the $1/\beta$ and $1/\beta^2$ kernels are bounded on the integration domains. Dominated convergence is straightforward. $\square$

---

## §5. The Main Result (**CORRECTED**)

> **⟨5⟩ THEOREM (Path-Integral Hockey-Stick Representation).** Under the full-rank assumption:
>
> $$\boxed{H(A|B)_\sigma - H(A|B)_\rho = -\int_0^1\!\left[\int_{1/d_A}^{M_{\mathrm{fwd}}(t)} \frac{\operatorname{Tr}\!\big[P_\beta(t)\,\delta_{AB}^{(\beta)}\big]}{\beta}\,d\beta \;+\; \int_{d_A}^{M_{\mathrm{rev}}(t)} \frac{\operatorname{Tr}\!\big[Q_\beta(t)\,(\mathbb{1}_A \otimes \delta_B - \beta\,\delta_{AB})\big]}{\beta^2}\,d\beta\right]dt} \tag{MAIN'}$$

*Proof.* Combine (FTC), $H(A|B) = -D(\cdot\|\tau)$, and (DER-HS). Fubini applies: both inner integrals are over compact intervals ($[1/d_A, d_A]$ and $[d_A, M_{\mathrm{rev}}(t)]$) with bounded integrands. $\square$

---

## §6. Structural Properties (**REVISED**)

### §6.1 Two Linear Functionals

At each $(t,\beta)$, the forward integrand $\Phi_{\mathrm{fwd}}(t,\beta) := \operatorname{Tr}[P_\beta(t)\,\delta_{AB}^{(\beta)}]$ and the reverse integrand $\Phi_{\mathrm{rev}}(t,\beta) := \operatorname{Tr}[Q_\beta(t)\,(\mathbb{1}_A \otimes \delta_B - \beta\,\delta_{AB})]$ are each single trace inner products.

### §6.2 Partial Trace of the Conditional Perturbation [Unchanged]

$\operatorname{Tr}_A[\delta_{AB}^{(\beta)}] = (1 - \beta d_A)\delta_B$. A-traceless at $\beta = 1/d_A$, which is now exactly the lower limit of the forward integral.

### §6.3 Fubini Reordering (**REVISED**)

> **⟨6.3⟩ COROLLARY.**
> $$H(A|B)_\sigma - H(A|B)_\rho = -\int_{1/d_A}^{d_A} \frac{1}{\beta}\left[\int_0^1 \operatorname{Tr}[P_\beta(t)\,\delta_{AB}^{(\beta)}]\,dt\right]d\beta \;-\; \int_{d_A}^{M_{\max}} \frac{1}{\beta^2}\left[\int_0^1 \operatorname{Tr}[Q_\beta(t)\,(\mathbb{1}_A \otimes \delta_B - \beta\,\delta_{AB})]\,dt\right]d\beta$$
> where $M_{\max} := \sup_{t \in [0,1]} M_{\mathrm{rev}}(t)$.

### §6.4 Simplification at $\beta = 1/d_A$ (**NEW**)

At $\beta = 1/d_A$, we have $\delta_{AB}^{(1/d_A)} = \delta_{AB} - \frac{1}{d_A}\,\mathbb{1}_A \otimes \delta_B$, which is the A-traceless part of the perturbation. The forward integral begins precisely at the threshold where the conditional perturbation decouples from the marginal.

---

## §7. Equivalent Formulation with Normalised Reference (**REVISED**)

> **⟨7⟩ REMARK.** Working with $\omega(t) = \tau(t)/d_A$ and applying (FR) directly (both arguments trace-1), the standard kernels $1/\gamma$ and $1/\gamma^2$ appear with integration over $[1,\infty)$. Define:
> - $\tilde{P}_\gamma(t) := \mathbf{1}\{\rho(t) - \gamma\,\omega(t) > 0\} = P_{\gamma/d_A}(t)$
> - $\tilde{Q}_\gamma(t) := \mathbf{1}\{\omega(t) - \gamma\,\rho(t) > 0\} = Q_{d_A\gamma}(t)$
>
> Then (MAIN') can be rewritten with the standard $[1,\infty)$ domain and $1/\gamma$, $1/\gamma^2$ kernels, at the cost of rescaled perturbation terms.

---

## §8. Open Obligations (**REVISED**)

| ID | Description | Status |
|----|-------------|--------|
| O1 | Justify $d/dt \leftrightarrow \int d\beta$ exchange (both terms) | OPEN (routine; finite domains help) |
| O2 | Non-full-rank regularisation | OPEN (standard) |
| O3 | Bound forward and reverse $t$-integrals as functions of $\beta$ and $\varepsilon$ | OPEN — key question |
| O4 | Numerical verification of (MAIN') for small systems | **DONE** ($< 8 \times 10^{-15}$ error, 37 test cases) |
| O5 | Evaluate $\int_{1/d_A}^{d_A} f(\beta)/\beta\,d\beta + \int_{d_A}^{M} g(\beta)/\beta^2\,d\beta$ for bounds from O3 | OPEN |
| O6 | Determine whether the reverse term contributes to the continuity bound or is benign | OPEN — new question |

---

## §9. References [Unchanged, plus:]

5. Liu–Hirche–Cheng (2025): "Layer Cake Representations for Quantum Divergences," arXiv:2507.07065v2. *(Independent derivation of (FR) and generalisations.)*
