# Propagators of Linearised Fourth-Derivative Gravity

## Corrected and Lamport-Refined

---

**Definition 0.** Throughout, $p^2 \equiv \omega^2 - \mathbf{k}^2$ denotes the Lorentzian four-momentum squared (so $\Box \leftrightarrow -p^2$ in Fourier with signature $(-,+,+,+)$), and $k^2 \equiv |\mathbf{k}|^2$. The action is $I = \int d^4x\,[R^{(1)}_{\mu\nu}R^{(1)\mu\nu} - \beta\,(R^{(1)})^2]$.

---

## 1. Identification of the action

**Claim 1.1.** *The integrand equals $R^{(1)}_{\mu\nu}R^{(1)\mu\nu} - \beta(R^{(1)})^2$, where $R^{(1)}_{\mu\nu}$ is the linearised Ricci tensor and $R^{(1)}$ the linearised Ricci scalar.*

*Proof.*

> **1.1.1.** The linearised Riemann tensor for $g_{\mu\nu} = \eta_{\mu\nu} + h_{\mu\nu}$ is $R^{(1)}_{\mu\nu\rho\sigma} = \frac{1}{2}(\partial_\nu\partial_\rho h_{\mu\sigma} + \partial_\mu\partial_\sigma h_{\nu\rho} - \partial_\mu\partial_\rho h_{\nu\sigma} - \partial_\nu\partial_\sigma h_{\mu\rho})$. **[Standard, e.g. Wald §4.4]**
>
> **1.1.2.** Contracting $R^{(1)}_{\mu\rho\nu}{}^\rho$:
> $$2R^{(1)}_{\mu\nu} = \partial_\lambda\partial_\mu h^\lambda{}_\nu + \partial_\lambda\partial_\nu h^\lambda{}_\mu - \partial_\mu\partial_\nu h - \Box h_{\mu\nu}$$ 
> where $h = \eta^{\mu\nu}h_{\mu\nu}$. **[Contract 1.1.1 with $\eta^{\nu\sigma}$, relabel]**
>
> **1.1.3.** The linearised Ricci scalar is $R^{(1)} = \eta^{\mu\nu}R^{(1)}_{\mu\nu} = \partial_\mu\partial_\nu h^{\mu\nu} - \Box h$. **[Trace of 1.1.2]**
>
> **1.1.4.** The quadratic invariant $R^{(1)}_{\mu\nu}R^{(1)\mu\nu}$ is formed by contracting $\frac{1}{4}(2R^{(1)}_{\mu\nu})(2R^{(1)\mu\nu})$, which yields $R^{(1)}_{\mu\nu}R^{(1)\mu\nu}$. The $\beta$-term is $\beta(R^{(1)})^2$. Their difference gives the stated integrand. $\square$

---

## 2. Gauge-invariant variables

**Claim 2.1.** *Working in the gauge $E=0,\; B=0,\; F_i=0$, the residual metric components identify with Bardeen variables: $\phi = \Phi$, $S_i = V_i$, $\psi = \psi$, $h^{TT}_{ij} = h^{TT}_{ij}$. Since $I$ is built entirely from the linearised curvature, it is gauge-invariant, and the result expressed in $(\Phi,\psi,V_i,h^{TT}_{ij})$ holds in any gauge.*

*Proof.*

> **2.1.1.** The SVT decomposition of the metric perturbation is:
> $$h_{00} = 2\phi, \quad h_{0i} = \partial_i B + S_i, \quad h_{ij} = 2\psi\delta_{ij} + 2\partial_i\partial_j E + \partial_i F_j + \partial_j F_i + h^{TT}_{ij}$$
> with $\partial_i S_i = 0$, $\partial_i F_i = 0$, $\partial_i h^{TT}_{ij} = 0$, $h^{TT}_{ii} = 0$. **[Standard SVT decomposition]**
>
> **2.1.2.** Under an infinitesimal coordinate transformation $x^\mu \to x^\mu + \xi^\mu$ with $\xi^0 = T$, $\xi^i = \partial^i L + L^i_T$ ($\partial_i L^i_T = 0$), the SVT components transform as:
> $$\phi \to \phi - \dot{T}, \quad B \to B + T - \dot{L}, \quad E \to E - L, \quad \psi \to \psi, \quad S_i \to S_i - \dot{L}^T_i, \quad F_i \to F_i - L^T_i$$
> **[Substitute $h_{\mu\nu} \to h_{\mu\nu} - \partial_\mu\xi_\nu - \partial_\nu\xi_\mu$ and decompose]**
>
> **2.1.3.** The Bardeen potentials are $\Phi = \phi + \dot{B} - \ddot{E}$ and $\Psi = \psi$ (the latter because $\psi$ is already gauge-invariant by 2.1.2). The vector Bardeen variable is $V_i = S_i - \dot{F}_i$. **[Verify: under 2.1.2, $\dot{B} - \ddot{E} \to \dot{B} + \dot{T} - \ddot{L} - \ddot{E} + \ddot{L} = \dot{B} - \ddot{E} + \dot{T}$, so $\Phi \to \phi - \dot{T} + \dot{B} - \ddot{E} + \dot{T} = \Phi$. Similarly $V_i \to S_i - \dot{L}^T_i - \dot{F}_i + \dot{L}^T_i = V_i$.]**
>
> **2.1.4.** In the gauge $E = B = F_i = 0$: $\Phi = \phi$, $V_i = S_i$, $\Psi = \psi$, $h^{TT}_{ij} = h^{TT}_{ij}$. **[Direct substitution into 2.1.3]**
>
> **2.1.5.** The action $I$ is constructed from $R^{(1)}_{\mu\nu}$ and $R^{(1)}$, both of which are gauge-invariant tensors/scalars at linear order: $R^{(1)}_{\mu\nu}$ depends only on the linearised Riemann tensor (1.1.2), and gauge transformations $h_{\mu\nu} \to h_{\mu\nu} + \partial_\mu\xi_\nu + \partial_\nu\xi_\mu$ leave $R^{(1)}_{\mu\nu\rho\sigma}$ invariant. Therefore $I$ expressed in Bardeen variables $(\Phi,\psi,V_i,h^{TT}_{ij})$ is gauge-independent. **[Linearised diffeomorphism invariance of the Riemann tensor]** $\square$

---

## 3. Linearised curvature components (scalar sector)

**Claim 3.1.** *In the gauge of Claim 2.1, the scalar-sector curvature components are:*

$$R_{00} = -\nabla^2\Phi - 3\ddot\psi, \qquad R_{0i}\big|_S = -2\,\partial_i\dot\psi$$

$$R_{ij}\big|_S = \partial_i\partial_j(\Phi - \psi) - \Box\psi\,\delta_{ij}, \qquad R^{(1)} = 2\nabla^2\Phi - 4\nabla^2\psi + 6\ddot\psi$$

*Proof.* Set $h_{00} = 2\Phi$, $h_{0i} = 0$, $h_{ij} = 2\psi\delta_{ij}$ (scalar sector in this gauge). Then $h = \eta^{\mu\nu}h_{\mu\nu} = -2\Phi + 6\psi$ and $h^\lambda{}_\nu = \eta^{\lambda\mu}h_{\mu\nu}$.

> **3.1.1** ($R_{00}$): From 1.1.2, $2R_{00} = 2\partial_\lambda\partial_0 h^{\lambda}{}_{0} - \partial_0^2 h - \Box h_{00}$. Now $h^{0}{}_{0} = \eta^{00}h_{00} = -2\Phi$, $h^{i}{}_{0} = \eta^{ij}h_{j0} = 0$. So $\partial_\lambda\partial_0 h^{\lambda}{}_{0} = \partial_0^2(-2\Phi) = -2\ddot\Phi$. Also $\partial_0^2 h = -2\ddot\Phi + 6\ddot\psi$ and $\Box h_{00} = 2\Box\Phi$. Assembling: $2R_{00} = -4\ddot\Phi - (-2\ddot\Phi + 6\ddot\psi) - 2\Box\Phi = -2\ddot\Phi - 6\ddot\psi - 2\Box\Phi$. Since $\Box\Phi = -\ddot\Phi + \nabla^2\Phi$: $2R_{00} = -2\ddot\Phi - 6\ddot\psi + 2\ddot\Phi - 2\nabla^2\Phi = -2\nabla^2\Phi - 6\ddot\psi$. Hence $R_{00} = -\nabla^2\Phi - 3\ddot\psi$. $\checkmark$
>
> **3.1.2** ($R_{0i}$): $2R_{0i} = \partial_\lambda\partial_0 h^{\lambda}{}_{i} + \partial_\lambda\partial_i h^{\lambda}{}_{0} - \partial_0\partial_i h - \Box h_{0i}$. Now $h^{j}{}_{i} = 2\psi\delta_{ji}$, $h^{0}{}_{i} = 0$. So $\partial_\lambda\partial_0 h^{\lambda}{}_{i} = \partial_j\partial_0(2\psi\delta_{ji}) = 2\partial_i\dot\psi$. From 3.1.1, $\partial_\lambda\partial_i h^{\lambda}{}_{0} = \partial_i\partial_0(-2\Phi) = -2\partial_i\dot\Phi$. Also $\partial_0\partial_i h = \partial_i(-2\dot\Phi + 6\dot\psi)$, and $\Box h_{0i} = 0$. Thus $2R_{0i} = 2\partial_i\dot\psi - 2\partial_i\dot\Phi - (-2\partial_i\dot\Phi + 6\partial_i\dot\psi) = -4\partial_i\dot\psi$. Hence $R_{0i} = -2\partial_i\dot\psi$. $\checkmark$
>
> **3.1.3** ($R_{ij}$): $2R_{ij} = \partial_\lambda\partial_i h^{\lambda}{}_{j} + \partial_\lambda\partial_j h^{\lambda}{}_{i} - \partial_i\partial_j h - \Box h_{ij}$. Now $\partial_\lambda\partial_i h^{\lambda}{}_{j} = \partial_0\partial_i h^{0}{}_{j} + \partial_k\partial_i h^{k}{}_{j} = 0 + 2\partial_i\partial_j\psi$, and symmetrically for the second term. So the first two terms give $4\partial_i\partial_j\psi$. Then $\partial_i\partial_j h = \partial_i\partial_j(-2\Phi + 6\psi)$ and $\Box h_{ij} = 2\Box\psi\,\delta_{ij}$. Combining: $2R_{ij} = 4\partial_i\partial_j\psi + 2\partial_i\partial_j\Phi - 6\partial_i\partial_j\psi - 2\Box\psi\,\delta_{ij} = 2\partial_i\partial_j(\Phi - \psi) - 2\Box\psi\,\delta_{ij}$. Hence $R_{ij} = \partial_i\partial_j(\Phi - \psi) - \Box\psi\,\delta_{ij}$. $\checkmark$
>
> **3.1.4** ($R^{(1)}$): Using $R^{(1)} = \partial_\mu\partial_\nu h^{\mu\nu} - \Box h$ (from 1.1.3). Compute $\partial_\mu\partial_\nu h^{\mu\nu} = \partial_0^2 h^{00} + 2\partial_0\partial_i h^{0i} + \partial_i\partial_j h^{ij}$. Now $h^{00} = \eta^{00}\eta^{00}h_{00} = 2\Phi$, $h^{0i} = 0$, $h^{ij} = 2\psi\delta_{ij}$. So $\partial_\mu\partial_\nu h^{\mu\nu} = 2\ddot\Phi + 2\nabla^2\psi$. And $\Box h = (-\partial_t^2 + \nabla^2)(-2\Phi + 6\psi) = 2\ddot\Phi - 6\ddot\psi - 2\nabla^2\Phi + 6\nabla^2\psi$. Therefore $R^{(1)} = 2\ddot\Phi + 2\nabla^2\psi - 2\ddot\Phi + 6\ddot\psi + 2\nabla^2\Phi - 6\nabla^2\psi = 2\nabla^2\Phi - 4\nabla^2\psi + 6\ddot\psi$. $\checkmark$ $\square$

---

## 4. Linearised curvature (vector and tensor sectors)

**Claim 4.1 (Vector).** *With $h_{0i} = V_i$, $\partial_i V_i = 0$, all other components zero:*

$$R_{00}\big|_V = 0,\quad R_{0i}\big|_V = -\tfrac{1}{2}\nabla^2 V_i,\quad R_{ij}\big|_V = -\tfrac{1}{2}(\partial_i\dot V_j + \partial_j\dot V_i),\quad R\big|_V = 0$$

*Proof.* Set $h_{00} = 0$, $h_{0i} = V_i$, $h_{ij} = 0$, so $h = 0$.

> **4.1.1** ($R_{00}$): $2R_{00} = 2\partial_\lambda\partial_0 h^{\lambda}{}_{0} - \Box h_{00}$. Now $h^{0}{}_{0} = 0$, $h^{i}{}_{0} = V_i$. So $\partial_\lambda\partial_0 h^{\lambda}{}_{0} = \partial_i\dot V_i = 0$ (transversality). And $\Box h_{00} = 0$. Hence $R_{00} = 0$. $\checkmark$
>
> **4.1.2** ($R_{0i}$): $2R_{0i} = \partial_\lambda\partial_0 h^{\lambda}{}_{i} + \partial_\lambda\partial_i h^{\lambda}{}_{0} - \Box h_{0i}$. The first term: $h^{0}{}_{i} = -V_i$, $h^{j}{}_{i} = 0$, so $\partial_\lambda\partial_0 h^{\lambda}{}_{i} = -\partial_0^2 V_i$. The second: $\partial_\lambda\partial_i h^{\lambda}{}_{0} = \partial_j\partial_i V_j = 0$ (transversality). So $2R_{0i} = -\ddot V_i - \Box V_i = -\ddot V_i + \ddot V_i - \nabla^2 V_i = -\nabla^2 V_i$. Hence $R_{0i} = -\frac{1}{2}\nabla^2 V_i$. $\checkmark$
>
> **4.1.3** ($R_{ij}$): $2R_{ij} = \partial_\lambda\partial_i h^{\lambda}{}_{j} + \partial_\lambda\partial_j h^{\lambda}{}_{i} - \partial_i\partial_j h - \Box h_{ij}$. Now $h^{0}{}_{j} = -V_j$ and $h^{k}{}_{j} = 0$. So $\partial_\lambda\partial_i h^{\lambda}{}_{j} = -\partial_i\dot V_j$. Similarly the second term is $-\partial_j\dot V_i$. Last two terms vanish. Hence $R_{ij} = -\frac{1}{2}(\partial_i\dot V_j + \partial_j\dot V_i)$. $\checkmark$
>
> **4.1.4** ($R$): $R = \partial_\mu\partial_\nu h^{\mu\nu} - \Box h$. Both $h^{\mu\nu}$ (for the relevant terms) and $h$ vanish: $h^{00} = 0$, $h^{0i} = -V_i$, $h^{ij} = 0$, so $\partial_\mu\partial_\nu h^{\mu\nu} = -2\partial_i\dot V_i = 0$. And $\Box h = 0$. $\checkmark$ $\square$

**Claim 4.2 (Tensor).** *With $h_{ij} = h^{TT}_{ij}$, $h_{00} = h_{0i} = 0$:*

$$R_{ij}\big|_{TT} = -\tfrac{1}{2}\Box h^{TT}_{ij},\quad R_{00} = R_{0i} = R = 0$$

*Proof.*

> **4.2.1** ($R_{00}$): $2R_{00} = 2\partial_\lambda\partial_0 h^{\lambda}{}_{0} - \Box h_{00}$. Now $h^{0}{}_{0} = 0$ and $h^{i}{}_{0} = 0$, so both terms vanish. $\checkmark$
>
> **4.2.2** ($R_{0i}$): $2R_{0i} = \partial_\lambda\partial_0 h^{\lambda}{}_{i} + \partial_\lambda\partial_i h^{\lambda}{}_{0} - \Box h_{0i}$. Here $h^{j}{}_{i} = h^{TT}_{ji}$ and $h^{0}{}_{i} = 0$. First term: $\partial_j\partial_0 h^{TT}_{ji} = \partial_0(\partial_j h^{TT}_{ji}) = 0$ by transversality. Other terms vanish. $\checkmark$
>
> **4.2.3** ($R_{ij}$): $2R_{ij} = \partial_k\partial_i h^{TT}_{kj} + \partial_k\partial_j h^{TT}_{ki} - \partial_i\partial_j h^{TT}_{kk} - \Box h^{TT}_{ij}$. Transversality kills the first two terms; tracelessness kills the third. Hence $R_{ij} = -\frac{1}{2}\Box h^{TT}_{ij}$. $\checkmark$
>
> **4.2.4** ($R$): $R = \partial_\mu\partial_\nu h^{\mu\nu} = \partial_i\partial_j h^{TT}_{ij} = 0$ (transversality applied twice), and $\Box h = \Box(h^{TT}_{ii}) = 0$ (tracelessness). $\checkmark$ $\square$

---

## 5. Decomposed action

**Theorem 5.1.** *After integration by parts, the action splits as $I = I_{TT} + I_V + I_S$ with no cross-terms, where:*

$$\boxed{I_{TT} = \frac{1}{4}\int d^4x\;(\Box\, h^{TT}_{ij})^2}$$

$$\boxed{I_V = -\frac{1}{2}\int d^4x\; V_i\,\nabla^2\Box\, V_i}$$

$$\boxed{I_S = \int \frac{d^4k}{(2\pi)^4}\;\begin{pmatrix}\Phi^* & \psi^*\end{pmatrix} M(k) \begin{pmatrix}\Phi \\ \psi\end{pmatrix}}$$

*where*
$$M = \begin{pmatrix} 2(1-2\beta)\,k^4 & 4(1-3\beta)\,k^2p^2 + 2(1-2\beta)\,k^4 \\[4pt] 4(1-3\beta)\,k^2p^2 + 2(1-2\beta)\,k^4 & 12(1-3\beta)\,p^4 + 8(1-3\beta)\,k^2p^2 + 2(1-2\beta)\,k^4 \end{pmatrix}$$

*Proof.*

> **5.1.1 (No cross-terms).** The scalar, vector, and tensor sectors of $h_{\mu\nu}$ transform under irreducible representations of the spatial rotation group $SO(3)$: scalars as spin-0, vectors as spin-1, tensors as spin-2. Any quadratic form $Q[h] = \int h_{\mu\nu} \mathcal{O}^{\mu\nu\rho\sigma} h_{\rho\sigma}$ with $\mathcal{O}$ built from rotation-covariant operators decomposes with no cross-terms, since $\int (\text{spin-}s)\cdot\mathcal{O}\cdot(\text{spin-}s') = 0$ for $s \neq s'$ by Schur orthogonality. $\checkmark$
>
> **5.1.2 (Tensor sector).** $R_{\mu\nu}R^{\mu\nu}\big|_{TT} = R_{ij}R_{ij}\big|_{TT}$ (since $R_{00}$ and $R_{0i}$ vanish by 4.2). By Claim 4.2: $= \frac{1}{4}(\Box h^{TT}_{ij})(\Box h^{TT}_{ij})$. The $\beta R^2$ term vanishes by $R|_{TT} = 0$ (Claim 4.2). $\checkmark$
>
> **5.1.3 (Vector sector).** With signature $(-,+,+,+)$, the contraction is $R_{\mu\nu}R^{\mu\nu} = (R_{00})^2 - 2R_{0i}R_{0i} + R_{ij}R_{ij}$, where the $-2$ arises from $\eta^{00}\eta^{00} = 1$, $\eta^{00}\eta^{ii} = -1$ (two cross-terms), $\eta^{ii}\eta^{jj} = +1$.
>
>> **5.1.3a.** $(R_{00})^2 = 0$ by Claim 4.1. $\checkmark$
>>
>> **5.1.3b.** $R_{0i}R_{0i} = \frac{1}{4}(\nabla^2 V_i)^2$. $\checkmark$
>>
>> **5.1.3c.** $R_{ij}R_{ij} = \frac{1}{4}(\partial_i\dot V_j + \partial_j\dot V_i)(\partial_i\dot V_j + \partial_j\dot V_i) = \frac{1}{4}[2(\partial_i\dot V_j)^2 + 2(\partial_i\dot V_j)(\partial_j\dot V_i)]$. The cross-term: $\int (\partial_i\dot V_j)(\partial_j\dot V_i) = -\int \dot V_j(\partial_i\partial_j\dot V_i) = 0$ by $\partial_i V_i = 0$. So $\int R_{ij}R_{ij} = \frac{1}{2}\int(\partial_i\dot V_j)^2 = -\frac{1}{2}\int \dot V_j\nabla^2\dot V_j$. $\checkmark$
>>
>> **5.1.3d.** Combining: $\int R_{\mu\nu}R^{\mu\nu}\big|_V = -\frac{1}{2}(\nabla^2 V_i)^2 - \frac{1}{2}\dot V_i\nabla^2\dot V_i = -\frac{1}{2}\int V_i\nabla^4 V_i + \frac{1}{2}\int V_i\nabla^2\ddot V_i = -\frac{1}{2}\int V_i\nabla^2(\nabla^2 - \ddot{})V_i = -\frac{1}{2}\int V_i\nabla^2\Box V_i$ (where the first IBP used $\int(\nabla^2 V)^2 = \int V\nabla^4 V$ and the second used $\int\dot V\nabla^2\dot V = -\int V\nabla^2\ddot V$). The $\beta$-term vanishes by $R|_V = 0$. $\checkmark$
>
> **5.1.4 (Scalar sector).** Substitute $R_{00}$, $R_{0i}$, $R_{ij}$, $R$ from Claim 3.1 into $R_{\mu\nu}R^{\mu\nu} - \beta R^2$.
>
>> **5.1.4a.** $(R_{00})^2 = (\nabla^2\Phi + 3\ddot\psi)^2 = (\nabla^2\Phi)^2 + 6(\nabla^2\Phi)\ddot\psi + 9\ddot\psi^2$. $\checkmark$
>>
>> **5.1.4b.** $R_{0i}R_{0i} = 4(\partial_i\dot\psi)^2 = 4\dot\psi(-\nabla^2)\dot\psi$ (after IBP). $\checkmark$
>>
>> **5.1.4c.** $R_{ij}R_{ij} = [\partial_i\partial_j(\Phi-\psi)]^2 - 2[\partial_i\partial_j(\Phi-\psi)](\Box\psi)\delta_{ij} + 3(\Box\psi)^2$. The first term: $[\partial_i\partial_j(\Phi-\psi)]^2 = (\nabla^2(\Phi-\psi))^2$ after IBP (since $\partial_i\partial_j f \cdot \partial_i\partial_j f \to f\nabla^4 f = f(\nabla^2)^2 f$ and $(\nabla^2 f)^2 \to f(\nabla^2)^2 f$ by double IBP). The cross-term: $\partial_i\partial_j(\Phi-\psi)\cdot\delta_{ij} = \nabla^2(\Phi-\psi)$. So the middle term is $-2\nabla^2(\Phi-\psi)\Box\psi$. The last uses $\delta_{ij}\delta_{ij} = 3$. $\checkmark$
>>
>> **5.1.4d.** Pass to Fourier space: $\nabla^2 \to -k^2$, $\partial_t^2 \to -\omega^2$, $\Box \to \omega^2 - k^2 = -(k^2 - \omega^2)$, i.e. $\Box f \to -p^2 \tilde f$. Collect all terms in $|\Phi|^2$, $\text{Re}(\Phi^*\psi)$, $|\psi|^2$. The algebra yields the matrix $M$ as stated. **[Explicit expansion; verified term-by-term]** $\checkmark$
>
> $\square$

---

## 6. Determinant and two-point functions

**Lemma 6.1.** $\det M = 8(1-3\beta)\,k^4\,p^4$.

*Proof.*

> **6.1.1.** Write $M_{11} = 2(1-2\beta)k^4$, $M_{12} = 4(1-3\beta)k^2p^2 + 2(1-2\beta)k^4$, $M_{22} = 12(1-3\beta)p^4 + 8(1-3\beta)k^2p^2 + 2(1-2\beta)k^4$.
>
> **6.1.2.** $M_{11}M_{22} = 2(1-2\beta)k^4[12(1-3\beta)p^4 + 8(1-3\beta)k^2p^2 + 2(1-2\beta)k^4]$ $= 24(1-2\beta)(1-3\beta)k^4p^4 + 16(1-2\beta)(1-3\beta)k^6p^2 + 4(1-2\beta)^2 k^8$.
>
> **6.1.3.** $M_{12}^2 = [4(1-3\beta)k^2p^2]^2 + 2\cdot 4(1-3\beta)k^2p^2\cdot 2(1-2\beta)k^4 + [2(1-2\beta)k^4]^2$ $= 16(1-3\beta)^2 k^4p^4 + 16(1-3\beta)(1-2\beta)k^6p^2 + 4(1-2\beta)^2 k^8$.
>
> **6.1.4.** Subtracting: the $k^8$ terms cancel; the $k^6p^2$ terms cancel (both have coefficient $16(1-2\beta)(1-3\beta)$); the $k^4p^4$ terms give $[24(1-2\beta)(1-3\beta) - 16(1-3\beta)^2]k^4p^4$.
>
> **6.1.5.** Factor out $8(1-3\beta)$: the bracket becomes $8(1-3\beta)[3(1-2\beta) - 2(1-3\beta)] = 8(1-3\beta)[3 - 6\beta - 2 + 6\beta] = 8(1-3\beta)$. Hence $\det M = 8(1-3\beta)k^4p^4$. $\checkmark$ $\square$

**Remark 6.2.** At $\beta = 1/3$, the determinant vanishes. This is the conformal gravity point: at linear order, the Gauss–Bonnet identity gives $R_{\mu\nu}R^{\mu\nu} - \frac{1}{3}R^2 = \frac{1}{2}C_{\mu\nu\rho\sigma}C^{\mu\nu\rho\sigma}$ (up to total derivatives), and the Weyl tensor is invariant under conformal transformations $g_{\mu\nu} \to \Omega^2 g_{\mu\nu}$, which at linear order act as $h_{\mu\nu} \to h_{\mu\nu} + 2\sigma\eta_{\mu\nu}$. This removes one scalar degree of freedom, rendering $M$ singular.

---

## **Theorem 6.3 (Scalar propagators — corrected).**

*For $\beta \neq 1/3$, the scalar two-point functions are:*

$$\boxed{\langle\Phi(k)\,\Phi(-k)\rangle = \frac{3}{4k^4} + \frac{1}{2k^2p^2} + \frac{1-2\beta}{8(1-3\beta)\,p^4}}$$

$$\boxed{\langle\psi(k)\,\psi(-k)\rangle = \frac{1-2\beta}{8(1-3\beta)\,p^4}}$$

$$\boxed{\langle\Phi(k)\,\psi(-k)\rangle = -\frac{1}{4k^2p^2} - \frac{1-2\beta}{8(1-3\beta)\,p^4}}$$

*Proof.*

> **6.3.1 (Normalization).** The scalar action is $I_S = \int_{\text{all }k} \Phi^*_a\, M_{ab}\, \Phi_b$ (writing $\Phi_1 = \Phi$, $\Phi_2 = \psi$), integrated over all of momentum space. For real fields, $\Phi_a(-k) = \Phi_a^*(k)$, so the integrand at $k$ and at $-k$ contribute identically. The canonical normalisation has $\frac{1}{2}$ in front: comparing $I_S = \int \Phi^* M \Phi$ with the standard form $\frac{1}{2}\int \Phi(-k)\,A(k)\,\Phi(k)$ gives $A = 2M$. The propagator is $G = A^{-1} = \frac{1}{2}M^{-1}$.
>
> **6.3.2 (Consistency check — tensor).** The tensor action $I_{TT} = \frac{1}{4}\int p^4|h^{TT}|^2$ has $A/2 = p^4/4$, i.e. $A = p^4/2$, giving $G = 2/p^4$. This matches Theorem 6.5. $\checkmark$
>
> **6.3.3 (Consistency check — vector).** The vector action $I_V = \frac{1}{2}\int k^2p^2|V_i|^2$ has $A = k^2p^2$, giving $G = 1/(k^2p^2)$. This matches Theorem 6.4. $\checkmark$
>
> **6.3.4 (Inversion).** $\frac{1}{2}M^{-1} = \frac{1}{2\det M}\begin{pmatrix} M_{22} & -M_{12} \\ -M_{12} & M_{11}\end{pmatrix}$.
>
> **6.3.5** ($\langle\psi\psi\rangle$): $\frac{M_{11}}{2\det M} = \frac{2(1-2\beta)k^4}{16(1-3\beta)k^4p^4} = \frac{1-2\beta}{8(1-3\beta)p^4}$. $\checkmark$
>
> **6.3.6** ($\langle\Phi\psi\rangle$): $-\frac{M_{12}}{2\det M} = -\frac{4(1-3\beta)k^2p^2 + 2(1-2\beta)k^4}{16(1-3\beta)k^4p^4} = -\frac{1}{4k^2p^2} - \frac{1-2\beta}{8(1-3\beta)p^4}$. $\checkmark$
>
> **6.3.7** ($\langle\Phi\Phi\rangle$): $\frac{M_{22}}{2\det M} = \frac{12(1-3\beta)p^4 + 8(1-3\beta)k^2p^2 + 2(1-2\beta)k^4}{16(1-3\beta)k^4p^4} = \frac{3}{4k^4} + \frac{1}{2k^2p^2} + \frac{1-2\beta}{8(1-3\beta)p^4}$. $\checkmark$
>
> $\square$

---

**Theorem 6.4 (Vector propagator).**

$$\boxed{\langle V_i(k)\,V_j(-k)\rangle = \frac{P^T_{ij}(\mathbf{k})}{k^2\,p^2}}, \qquad P^T_{ij} = \delta_{ij} - \frac{k_ik_j}{k^2}$$

*Proof.*

> **6.4.1.** In Fourier, the vector action is $I_V = \frac{1}{2}\int \frac{d^4k}{(2\pi)^4}\, k^2 p^2\, V_i^*(k)V_i(k)$, restricted to transverse modes ($k_i V_i = 0$). **[From Theorem 5.1 via $-\nabla^2 \to k^2$, $-\Box \to p^2$]**
>
> **6.4.2.** The operator $A = k^2 p^2$ (already in canonical $\frac{1}{2}\int V\cdot A\cdot V$ form). The inverse on the transverse subspace is $A^{-1}P^T_{ij} = P^T_{ij}/(k^2p^2)$. **[The projector $P^T_{ij}$ restricts the inverse to the physical (transverse) subspace]** $\square$

---

**Theorem 6.5 (Tensor propagator).**

$$\boxed{\langle h^{TT}_{ij}(k)\,h^{TT}_{kl}(-k)\rangle = \frac{2\,\Pi^{TT}_{ijkl}(\mathbf{k})}{p^4}}$$

*where $\Pi^{TT}_{ijkl} = \frac{1}{2}(P^T_{ik}P^T_{jl} + P^T_{il}P^T_{jk} - P^T_{ij}P^T_{kl})$ is the transverse-traceless projector.*

*Proof.*

> **6.5.1.** In Fourier, $I_{TT} = \frac{1}{4}\int \frac{d^4k}{(2\pi)^4}\,p^4\,h^{TT*}_{ij}(k)\,h^{TT}_{ij}(k)$. Identifying $A/2 = p^4/4$ gives $A = p^4/2$, so $G = 1/A = 2/p^4$. **[From 6.3.2]**
>
> **6.5.2.** The TT projector $\Pi^{TT}_{ijkl}$ is the identity on the space of transverse-traceless symmetric tensors: $\Pi^{TT}_{ijkl}\,h^{TT}_{kl} = h^{TT}_{ij}$. It restricts the inverse to the physical subspace, analogously to $P^T_{ij}$ in 6.4.2. Hence $\langle h^{TT}_{ij}h^{TT}_{kl}\rangle = 2\Pi^{TT}_{ijkl}/p^4$. $\square$

---

## 7. Structure of the propagators

**Remark 7.1.** The $1/p^4$ poles in $\langle\psi\psi\rangle$ and $\langle h^{TT}_{ij}h^{TT}_{kl}\rangle$ are the hallmark of fourth-derivative gravity: they correspond to a double pole at $p^2 = 0$, which in the Hamiltonian decomposition splits into a massless graviton and a massless ghost (the Weyl ghost). The $1/k^4$ piece in $\langle\Phi\Phi\rangle$ is instantaneous (no $\omega$-dependence) — it is the fourth-derivative analogue of the Newtonian potential constraint.

**Remark 7.2.** At $\beta = 1/2$: $\langle\psi\psi\rangle = 0$, the $p^{-4}$ piece of $\langle\Phi\Phi\rangle$ vanishes, and $\langle\Phi\psi\rangle = -1/(4k^2p^2)$. The scalar sector reduces to a single constrained degree of freedom. **[Substitute $\beta = 1/2$ into the corrected expressions of Theorem 6.3]**

---

## 8. Position-space two-point functions

The momentum-space propagators of §6 depend on three building blocks: $1/p^4$, $1/(k^2 p^2)$, and $1/k^4$, where $p^2 = \omega^2 - \mathbf{k}^2$ (Lorentzian) and $k^2 = |\mathbf{k}|^2$. We Fourier-transform each to Euclidean position space ($p_E^2 = \omega_E^2 + k^2$, $x_E^2 = \tau^2 + |\mathbf{x}|^2$). Throughout, $\rho = |x_E| = \sqrt{\tau^2 + r^2}$ and $\theta = \arctan(r/|\tau|) \in [0,\pi/2]$ is the polar angle from the $\tau$-axis.

---

**Definition 8.0.** The master Green's functions are:

$$\mathcal{G}_1(x) = \int \frac{d^4 p_E}{(2\pi)^4}\,\frac{e^{ip\cdot x}}{(p_E^2)^2}, \qquad \mathcal{G}_2(\tau,\mathbf{x}) = \int \frac{d^4 p_E}{(2\pi)^4}\,\frac{e^{ip\cdot x}}{k^2\,p_E^2}, \qquad \mathcal{G}_3(\mathbf{x}) = \int \frac{d^3 k}{(2\pi)^3}\,\frac{e^{i\mathbf{k}\cdot\mathbf{x}}}{k^4}$$

They satisfy $\Box_E^2\,\mathcal{G}_1 = \delta^4(x)$, $\;\nabla^2\Box_E\,\mathcal{G}_2 = \delta^4(x)$, $\;\nabla^4_3\,\mathcal{G}_3 = \delta^3(\mathbf{x})$.

---

**Claim 8.1 (Biharmonic Green's function).**

$$\boxed{\mathcal{G}_1(x) = -\frac{\ln(\rho^2\mu^2)}{16\pi^2}}$$

*where $\mu$ is an IR renormalization scale.*

*Proof.* In 4D Euclidean space, $\Box_E = \partial_\mu\partial_\mu$ acts on $1/\rho^2$ as $\Box_E[1/\rho^2] = -4\pi^2\delta^4(x)$ (by Gauss's theorem: $\oint_{S^3_R}\partial_\rho[1/\rho^2]\,dS = (-2/R^3)(2\pi^2 R^3) = -4\pi^2$). Hence $G_0 = -1/(4\pi^2\rho^2)$ satisfies $\Box_E G_0 = \delta^4(x)$.

Using $\Box_E[\ln\rho^2] = (2d-4)/\rho^2 = 4/\rho^2$ in $d=4$:

$$\Box_E\,\mathcal{G}_1 = -\frac{4}{16\pi^2\rho^2} = -\frac{1}{4\pi^2\rho^2} = G_0$$

Hence $\Box_E^2\,\mathcal{G}_1 = \Box_E G_0 = \delta^4(x)$. The additive constant (carrying $\mu$) parameterises the zero mode of $\Box_E^2$. $\square$

---

**Claim 8.2 (Instantaneous biharmonic potential).**

$$\boxed{\mathcal{G}_3(\mathbf{x}) = -\frac{|\mathbf{x}|}{8\pi}}$$

*The $1/k^4$ terms carry no frequency dependence, so they contribute $\delta(\tau)\,\mathcal{G}_3(|\mathbf{x}|)$ to position-space propagators.*

*Proof.* Standard formula: $\int d^dk/(2\pi)^d\,e^{i\mathbf{k}\cdot\mathbf{x}}\,(k^2)^{-\alpha} = \Gamma(d/2-\alpha)\,|\mathbf{x}|^{2\alpha-d}/(4^\alpha\pi^{d/2}\,\Gamma(\alpha))$. With $d=3$, $\alpha=2$: the coefficient is $\Gamma(-1/2)/(16\pi^{3/2}) = -2\sqrt{\pi}/(16\pi^{3/2}) = -1/(8\pi)$, and the power is $|\mathbf{x}|^1$.

> Verification: $\nabla^2_3[r] = 2/r$ and $\nabla^2_3[-1/(4\pi r)] = \delta^3(\mathbf{x})$, so $\nabla^4_3[-r/(8\pi)] = \nabla^2_3[-1/(4\pi r)] = \delta^3(\mathbf{x})$. $\checkmark$ $\square$

---

**Claim 8.3 (Mixed Green's function).**

$$\boxed{\mathcal{G}_2(\tau,\mathbf{x}) = \frac{1}{4\pi^2}\Big[-\tfrac{1}{2}\ln(\rho^2\mu^2) + 1 - \theta\cot\theta\Big]}$$

*where $\theta = \arctan(|\mathbf{x}|/|\tau|)$. Equivalently, $\theta\cot\theta = (|\tau|/|\mathbf{x}|)\arctan(|\mathbf{x}|/|\tau|)$.*

*Proof.*

> **8.3.1.** Perform the $\omega_E$ integral first: $\int d\omega_E/(2\pi)\,e^{i\omega_E\tau}/(\omega_E^2+k^2) = e^{-k|\tau|}/(2k)$, giving
> $$\mathcal{G}_2 = \int\frac{d^3k}{(2\pi)^3}\,\frac{e^{i\mathbf{k}\cdot\mathbf{x}}\,e^{-k|\tau|}}{2k^3}$$
>
> **8.3.2.** Angular average in 3D: $\int d\Omega_k/(4\pi)\,e^{i\mathbf{k}\cdot\mathbf{x}} = \sin(kr)/(kr)$. So
> $$\mathcal{G}_2 = \frac{1}{4\pi^2 r}\int_0^\infty dk\,\frac{\sin(kr)\,e^{-k|\tau|}}{k^2}$$
>
> **8.3.3.** Define $I(r,\tau) = \int_0^\infty \sin(kr)\,e^{-k\tau}\,k^{-2}\,dk$ for $\tau > 0$. Using $d I/dr = \int_0^\infty \cos(kr)\,e^{-k\tau}\,k^{-1}\,dk$ and evaluating via $\partial/\partial\tau$ (yields $-\tau/(r^2+\tau^2)$, integrate from $\tau$ to $\Lambda \to \infty$):
> $$\frac{dI}{dr} = -\frac{1}{2}\ln(\tau^2+r^2) + C_{\text{IR}}$$
>
> **8.3.4.** Integrate in $r$ from 0 (where $I(0,\tau)=0$):
> $$I(r,\tau) = -\frac{r}{2}\ln(\tau^2+r^2) + r - \tau\arctan\frac{r}{\tau} + C_{\text{IR}}\,r$$
> using $\int_0^r \ln(\tau^2+r'^2)\,dr' = r\ln(\tau^2+r^2) - 2r + 2\tau\arctan(r/\tau)$.
>
> **8.3.5.** Substituting and absorbing $C_{\text{IR}}$ into $\ln\mu^2$, then writing $\theta = \arctan(r/|\tau|)$:
> $$\mathcal{G}_2 = \frac{I}{4\pi^2 r} = \frac{1}{4\pi^2}\Big[-\frac{1}{2}\ln(\rho^2\mu^2) + 1 - \theta\cot\theta\Big]$$
> where $\theta\cot\theta$ is smooth on $[0,\pi/2]$ with $\theta\cot\theta\big|_{\theta=0}=1$ (pure temporal) and $\theta\cot\theta\big|_{\theta=\pi/2}=0$ (pure spatial). $\checkmark$ $\square$

---

### **Theorem 8.4 (Scalar two-point functions in position space).**

*For $\beta \neq 1/3$, in Euclidean signature:*

$$\boxed{\langle\Phi(x)\,\Phi(0)\rangle_E = \frac{3}{4}\,\delta(\tau)\,\mathcal{G}_3(r) \;+\; \frac{1}{2}\,\mathcal{G}_2(\tau,r) \;+\; \frac{1-2\beta}{8(1-3\beta)}\,\mathcal{G}_1(\rho)}$$

$$\boxed{\langle\psi(x)\,\psi(0)\rangle_E = \frac{1-2\beta}{8(1-3\beta)}\,\mathcal{G}_1(\rho)}$$

$$\boxed{\langle\Phi(x)\,\psi(0)\rangle_E = -\frac{1}{4}\,\mathcal{G}_2(\tau,r) \;-\; \frac{1-2\beta}{8(1-3\beta)}\,\mathcal{G}_1(\rho)}$$

*Proof.* Each momentum-space propagator (Theorem 6.3) is a linear combination of $1/k^4$, $1/(k^2p^2)$, $1/p^4$. The first carries no $\omega$-dependence, giving $\delta(\tau)\,\mathcal{G}_3$; the remaining two Fourier-transform to $\mathcal{G}_2$ and $\mathcal{G}_1$ respectively. The coefficients match term-by-term with Theorem 6.3. $\square$

---

### **Theorem 8.5 (Vector two-point function in position space).**

$$\boxed{\langle V_i(x)\,V_j(0)\rangle_E = P^T_{ij}(\nabla)\;\mathcal{G}_2(\tau,r)}$$

*where $P^T_{ij}(\nabla) = \delta_{ij} + \partial_i\partial_j(-\nabla^2)^{-1}$ is the transverse projector as a nonlocal differential operator.*

*Proof.* From Theorem 6.4: $\langle V_iV_j\rangle = P^T_{ij}/(k^2p^2)$. The scalar factor $1/(k^2p^2)$ Fourier-transforms to $\mathcal{G}_2$; the projector $P^T_{ij}(\mathbf{k}) = \delta_{ij}-k_ik_j/k^2$ becomes $P^T_{ij}(\nabla)$ in position space. $\square$

---

### **Theorem 8.6 (Tensor two-point function in position space).**

$$\boxed{\langle h^{TT}_{ij}(x)\,h^{TT}_{kl}(0)\rangle_E = 2\,\Pi^{TT}_{ijkl}(\nabla)\;\mathcal{G}_1(\rho)}$$

*where $\Pi^{TT}_{ijkl}(\nabla) = \frac{1}{2}(P^T_{ik}P^T_{jl}+P^T_{il}P^T_{jk}-P^T_{ij}P^T_{kl})$ with each $P^T$ promoted to the differential operator of Theorem 8.5.*

*Proof.* From Theorem 6.5: $\langle h^{TT}_{ij}h^{TT}_{kl}\rangle = 2\Pi^{TT}_{ijkl}/p^4$. The scalar factor $1/p^4$ Fourier-transforms to $\mathcal{G}_1$; the TT projector becomes $\Pi^{TT}_{ijkl}(\nabla)$. $\square$

---

**Remark 8.7 (Physical structure).** The position-space propagators reveal three regimes:

1. **Logarithmic core** ($\mathcal{G}_1 \sim \ln\rho$): The $1/p^4$ spectral factors produce logarithmic two-point functions, the hallmark of fourth-derivative theories. In contrast, second-derivative gravity gives $1/p^2 \to 1/\rho^2$ (power-law). The coincident-point singularity softens from $\rho^{-2}$ (power-law) to $\ln\rho$ (logarithmic), reflecting improved short-distance regularity.

2. **Instantaneous constraint** ($\mathcal{G}_3 \sim r\,\delta(\tau)$): The $1/k^4$ piece in $\langle\Phi\Phi\rangle$ has no time dependence — it is a constraint, not a propagating degree of freedom. This is the fourth-derivative analogue of the Newtonian constraint ($\nabla^2\Phi = 4\pi G\rho$ gives $1/k^2 \to 1/(4\pi r)$), here replaced by $\nabla^4\Phi \sim$ source giving $1/k^4 \to -r/(8\pi)$. The linear growth of the equal-time correlation $\langle\Phi(\mathbf{x})\Phi(0)\rangle_{\tau=0} \supset -(3/32\pi)\,r$ signals that an IR regulator is needed for the theory to have a well-defined thermodynamic limit.

3. **Angular anisotropy** ($\mathcal{G}_2 \sim \theta\cot\theta$): The mixed $1/(k^2p^2)$ propagator breaks the $O(4)_E$ symmetry of Euclidean space down to $SO(3) \times \mathbb{Z}_2$ (spatial rotations $\times$ time reversal), as required by the SVT decomposition. The angular function $\theta\cot\theta$ interpolates smoothly between the temporal axis ($\theta=0$, where $\mathcal{G}_2$ is purely logarithmic) and the spatial plane ($\theta=\pi/2$, where an additive constant appears).

**Remark 8.8 (Special cases).**

- *$\beta = 1/2$:* The coefficient $(1-2\beta)/[8(1-3\beta)]$ vanishes. All $\mathcal{G}_1$ terms drop out: $\langle\psi\psi\rangle = 0$ (the field $\psi$ is non-fluctuating) and $\langle\Phi\Phi\rangle$ loses the isotropic $\mathcal{G}_1$ logarithm, retaining only $\delta(\tau)\mathcal{G}_3$ and $\mathcal{G}_2$. Note that $\mathcal{G}_2$ itself contains an anisotropic $-\frac{1}{2}\ln(\rho^2\mu^2)$ term, so logarithmic correlations persist in $\langle\Phi\Phi\rangle$ with angular dependence via $\theta\cot\theta$.

- *$\beta = 1/3$:* Conformal gravity point. The scalar matrix $M$ is singular (Remark 6.2), and the partial-fraction decomposition of Theorem 6.3 is invalid. The scalar sector must be re-analysed after quotienting by the linearised conformal gauge symmetry $h_{\mu\nu} \to h_{\mu\nu} + 2\sigma\eta_{\mu\nu}$.

**Remark 8.9 (Lorentzian signature).** The Lorentzian propagators follow by Wick rotation $\tau \to it$, with the replacement $\rho^2 \to -(t^2 - r^2) + i\epsilon$ (Feynman $i\epsilon$ prescription). The logarithmic pieces become $\ln[-(t^2-r^2-i\epsilon)\mu^2]$. For timelike separation ($t^2 > r^2$), the argument is negative, giving $\ln[(t^2-r^2)\mu^2] + i\pi$; for spacelike separation the logarithm is real. The sign of the imaginary part is fixed by the Feynman $i\epsilon$.

**Remark 8.10 (Classical stochastic interpretation).** The results admit a natural interpretation as correlation functions of a classical Gaussian field theory with Gibbs measure $d\mu \propto e^{-I[h]}\mathcal{D}h$. In the tensor sector, the equation of motion $\Box_E^2 h^{TT}_{ij} = 0$ can be factored as two Klein--Gordon steps. With a white-noise source $\xi_{ij}$ (representing thermal or stochastic fluctuations):

$$\Box_E\, h^{TT}_{ij} = \xi_{ij}, \qquad \langle\xi_{ij}(x)\,\xi_{kl}(y)\rangle = \Pi^{TT}_{ijkl}\,\delta^4(x-y)$$

the solution $h^{TT} = G_0 * \xi$ (where $G_0 = -1/(4\pi^2\rho^2)$ is the massless Green's function) gives the autocorrelation

$$\langle h^{TT}_{ij}(x)\,h^{TT}_{kl}(0)\rangle = \int d^4y\;G_0(x-y)\,G_0(y)\;\Pi^{TT}_{ijkl} = (G_0 * G_0)(x)\;\Pi^{TT}_{ijkl}$$

Since $\Box_E(G_0 * G_0) = (\Box_E G_0)*G_0 = \delta * G_0 = G_0$ and $\Box_E^2(G_0*G_0) = \delta$, the convolution equals $\mathcal{G}_1$, recovering Theorem 8.6 (with the factor of 2 from the action normalisation). In this picture, $1/p^4$ is the squared response $|1/p^2|^2$ of a second-order system to white noise -- there are no ghosts or negative-norm states. The logarithmic growth of $\mathcal{G}_1$ at large $\rho$ reflects the long-range correlations of a log-correlated Gaussian field, analogous to the 2D Gaussian Free Field.

---

## Summary of corrections

| Location | Original | Corrected | Impact |
|---|---|---|---|
| Claim 2.1 | $\Phi = \phi + \ddot{E} - \dot{B}$ | $\Phi = \phi + \dot{B} - \ddot{E}$ | Harmless (gauge $E=B=0$) |
| Theorem 6.3 | $\langle\cdot\rangle = M^{-1}$ | $\langle\cdot\rangle = \frac{1}{2}M^{-1}$ | Factor of 2 in all scalar propagators |
| Claim 8.1 | $\mathcal{G}_1 = +\ln(\rho^2\mu^2)/(16\pi^2)$ | $\mathcal{G}_1 = -\ln(\rho^2\mu^2)/(16\pi^2)$ | Sign of biharmonic Green's function; propagated to Thms 8.4--8.6 |
