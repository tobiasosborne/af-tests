# HANDOFF: Fisher Superadditivity Proof Tree

**Session date:** 2026-02-08
**Tool:** `af` (Adversarial Proof Framework) in `examples7/`
**Agents used:** 13 total (7 provers, 6 verifiers) across 3 waves

---

## 1. The Conjecture

For all monic real-rooted polynomials `p, q` of degree `n` with simple roots:

```
1/Phi_n(p ⊞_n q) >= 1/Phi_n(p) + 1/Phi_n(q)
```

where `⊞_n` is the MSS finite free additive convolution and
`Phi_n(p) = sum_i H_p(lambda_i)^2` is the finite free Fisher information.

**Source document:** `examples7/fisher_subordination_proof2.md`

---

## 2. Proof Tree State

```
af status -d examples7/
```

- **41 nodes**, 20 validated, 20 pending, 1 archived
- **17 open challenges** (1 critical, 4 major, 7 minor, 5 note)
- **Critical path:** `1 -> 1.5 -> 1.5.3 -> 1.5.3.2`

### What Is Validated (solid foundation)

| Node | Content | Validated by |
|------|---------|-------------|
| 1.1 | Setup: equivalence to harmonic-mean form `Phi_n(r) <= Phi_n(p)*Phi_n(q)/(Phi_n(p)+Phi_n(q))` | verifier-1 |
| 1.2 + children | Base case n=1: trivially true (`Phi_1 = 0`) | verifier-3 |
| 1.3 + children | Base case n=2: **exact equality** via Pythagorean discriminant `D = (a-b)^2 + (c-d)^2` | verifier-4 |
| 1.4 + children | Key lemma: `H_r(lambda_i) = (1/2) sum_k 1/(lambda_i - gamma_k)` where gamma_k are critical points of `r` | verifier-5 |

### What Was Explored But Blocked

| Node | Approach | Finding |
|------|----------|---------|
| 1.5.1 | Random matrix decomposition | **Archived** — observational only, contributes nothing to proof |
| 1.5.2 | Finite free cumulant representation | Cumulants additive, but `Phi_n` is rational (not polynomial) in them. **Prover declared dead end; VERIFIER REFUTED THIS** (see breakthrough below) |
| 1.5.3 | Cauchy-Schwarz on H vectors | **Blocked** — H_p, H_q, H_r live in different R^n spaces; finite subordination fails |

### What Is Open

| Node | Content | Status |
|------|---------|--------|
| 1.5 | Main inequality (harmonic-mean form) | Pending — needs new proof strategy |
| 1.5.2 | Cumulant approach | Has critical challenge (ch-2f457f6e4c5) refuting "dead end" conclusion |
| 1.5.3 | Cauchy-Schwarz approach | Accepted with gaps G1-G5 documented |
| 1.5.4 + children | Strictness characterization | Proved conditionally (see Section 5) |

---

## 3. THE BREAKTHROUGH: Cumulant Decomposition

**This is the most important finding. Verifier-6 (challenge ch-02f2a6f96a1) refuted Prover-4's "dead end" conclusion.**

### The Key Identity

For centered polynomials (WLOG by translation invariance of `Phi_n` and commutativity of `⊞_n` with shifts):

```
1/Phi_n = C_n * kappa_2 + R_n(kappa_2, kappa_3, ..., kappa_n)
```

where:
- `C_n = 2/(n(n-1))` (the linear coefficient: `C_2=1, C_3=2/9, C_4=1/12`)
- `kappa_k` are the finite free cumulants (additive under `⊞_n`)
- `R_n` is the **correction term** (vanishes when `kappa_3 = ... = kappa_n = 0`)

### Why This Works

The linear term `C_n * kappa_2` is **additive** under `⊞_n`:
```
C_n * kappa_2(p ⊞_n q) = C_n * kappa_2(p) + C_n * kappa_2(q)
```

So the conjecture reduces to proving the correction `R_n` is **superadditive**:
```
R_n(kappa(p) + kappa(q)) >= R_n(kappa(p)) + R_n(kappa(q))
```

### Status by Degree

| n | `C_n` | Correction `R_n` | Superadditivity of `R_n` |
|---|-------|-------------------|--------------------------|
| 2 | 1 | 0 (no correction) | Trivial |
| 3 | 2/9 | `-2k3^2/(27k2^2)` (negative, see below) | **PROVED ANALYTICALLY** |
| 4 | 1/12 | `(-16k2^3*k3^2 - 4k2^2*k4^2 + 20k2*k3^2*k4 - 8k3^4 - k4^3) / (24*(16k2^5 - ...))` | **Verified numerically** (15K trials, 0 violations) |
| general | 2/(n(n-1)) | rational expression | **OPEN** |

### The n=3 Analytical Proof (Complete)

```
1/Phi_3 = (2/9)*k2 - (2/27)*k3^2/k2^2
```

Superadditivity of `R_3(k2, k3) = -2k3^2/(27k2^2)`:
Need: `k3_p^2/k2_p^2 + k3_q^2/k2_q^2 >= (k3_p+k3_q)^2/(k2_p+k2_q)^2`

This follows from positive-definiteness of the 2x2 matrix:
```
M = [[t^3(2s+t), -s^2*t^2], [-s^2*t^2, s^3(2t+s)]]
```
with `s = k2_p, t = k2_q`. Since `det(M) = 2s^3*t^3*(s+t)^2 > 0` and trace > 0, done.

---

## 4. Confirmed Obstructions (Do NOT Retry)

### Finite Subordination Fails at Finite n

The naive subordination `G_r(z) = G_p(omega_p(z))` with `omega_p + omega_q = z + F_r(z)` is **inconsistent** at the roots of `r`:

- Residue matching forces `omega_p'(lambda_i) = 1`
- But `F_r'(lambda_i) = n` (elementary computation: `F_r = nr/r'`)
- So `omega_p' + omega_q' = 1 + 1 = 2` but `1 + F_r' = 1 + n`
- Contradiction for `n >= 2`

**Verified both algebraically and numerically.** Do not attempt subordination-based proofs.

### Direct Cauchy-Schwarz Fails

The vectors `H_p = (H_p(mu_1), ..., H_p(mu_n))`, `H_q = (H_q(nu_1), ..., H_q(nu_n))`, `H_r = (H_r(lambda_1), ..., H_r(lambda_n))` are indexed by **different root sets**. There is no canonical inner product between them without subordination (which fails, see above).

---

## 5. Equality Characterization (Node 1.5.4)

**Unconditional results** (do not depend on main inequality):

- **n=2:** Equality always holds. `gap(r)^2 = gap(p)^2 + gap(q)^2` (Pythagorean).
- **n=3 equality case:** Equality iff both `p, q` are equally-spaced (arithmetic progression roots). Then `r` is also equally-spaced with gap `sqrt(s^2 + t^2)`.

**Conditional results** (require main inequality):

- **n=3 strictness:** Non-equal-gap pairs give strict inequality.
- **n >= 4:** Strict inequality for ALL pairs (even equally-spaced), because `⊞_n` does not preserve equal-gap structure for `n >= 4`.

Supporting scripts: `final_analysis.py`, `equality_analysis.py`, `compute_strictness.py`

---

## 6. Registered Definitions and External References

### Definitions (`af defs`)
- `P_n` — monic real-rooted polynomials with simple roots
- `finite_free_convolution` — MSS convolution formula
- `Cauchy_transform` — `G_p(z) = (1/n) p'(z)/p(z)`
- `discrete_Hilbert_transform` — `H_p(lambda_i) = sum_{j!=i} 1/(lambda_i - lambda_j)`
- `Phi_n` — finite free Fisher information
- `derived_polynomial` — `p^{(1)} = p'/n`

### External References (`af externals`)
- `MSS_real_rootedness` — MSS 2015, Theorem 4.4
- `MSS_random_matrix` — MSS 2015, Theorem 4.2
- `MSS_derivative_formula` — MSS 2015, Proposition 4.5: `(p ⊞_n q)' = n(p^{(1)} ⊞_{n-1} q^{(1)})`
- `Cauchy_Schwarz_inequality` — Standard

---

## 7. Open Challenges to Address

### Blocking (must resolve before acceptance)

| ID | Node | Severity | Issue |
|----|------|----------|-------|
| ch-2f457f6e4c5 | 1.5.2.3 | **critical** | Non sequitur: "Phi_n rational in cumulants" does NOT imply "cumulant approach insufficient". Verifier proved n=3 analytically. |
| ch-02f2a6f96a1 | 1.5.2 | major | The cumulant approach YIELDS a proof path (`1/Phi_n = C_n*k2 + R_n` decomposition). Node must be rewritten. |
| ch-671c03bf9fc | 1.5.2 | major | Parent node frames cumulants as exploratory. Should be reframed as the primary proof strategy. |
| ch-0cff5418e0b | 1.5.2.1 | major | Proof sketch contains a FALSE algebraic identity. Cumulant additivity is correct but the justification needs rewriting. |
| ch-961e6bfb36d | 1.5.2.3 | major | Additional evidence that correction term is superadditive for n=4. |

### Non-blocking (accept with notes)

Minor/note challenges on nodes 1.1, 1.2, 1.2.5, 1.4, 1.4.1, 1.4.2, 1.4.6, 1.5.3, 1.5.3.3, 1.5.3.4. These are expositional precision issues, not mathematical errors.

---

## 8. Recommended Next Steps (Priority Order)

### P0: Rewrite node 1.5.2 around the cumulant decomposition

The current 1.5.2 tree declares cumulants a dead end. The verifier proved otherwise. The next orchestrator should:

1. Claim 1.5.2, amend its statement to reflect `1/Phi_n = C_n*k2 + R_n` as the proof strategy
2. Resolve challenges ch-2f457f6e4c5 and ch-02f2a6f96a1
3. Add the n=3 analytical proof as a validated child node

### P1: Prove R_4 superadditivity analytically

The correction for n=4 is:
```
R_4(k2,k3,k4) = (-16*k2^3*k3^2 - 4*k2^2*k4^2 + 20*k2*k3^2*k4 - 8*k3^4 - k4^3)
                 / (24*(16*k2^5 - 8*k2^2*k3^2 - k2*k4^2 + 2*k3^2*k4))
```

This is verified numerically (15K trials, 0 violations). The analytical proof likely requires a generalization of the 2x2 positive-definiteness argument from n=3 to a higher-dimensional quadratic form.

### P2: Find general pattern for R_n

Conjecture: `C_n = 2/(n(n-1))` for all n. Verify for n=5,6. The general `R_n` should have a structural form that makes superadditivity provable by induction or by a general convexity argument.

### P3: Alternative — Costa/heat flow approach

Verifier-7 (challenge ch-6dfe2174164) identified a partially promising approach via concavity of `1/Phi_n` along semicircular flow (analogous to Costa's entropy power inequality proof). Key ingredients:
- `Phi_n(D_c(p)) = Phi_n(p)/c^2` (quadratic scaling under dilation)
- Dilation commutes with `⊞_n`
- `1/Phi_n` is concave along semicircular interpolation (verified numerically)

### P4: Resolve minor challenges

Address the ~12 non-blocking minor/note challenges to clean up the proof tree.

---

## 9. Commands Reference

```bash
# View full proof state
af status -d examples7/

# View specific node
af get 1.5.2 -d examples7/

# View all challenges
af challenges -d examples7/

# View available work
af jobs -d examples7/

# Claim a node for prover work
af claim 1.5.2 --owner prover-X --role prover -d examples7/

# Claim a node for verifier work
af claim 1.4.1 --owner verifier-X --role verifier -d examples7/

# Refine a claimed node
af refine 1.5.2 --owner prover-X -s "New child statement" -d examples7/

# Challenge a node
af challenge 1.5.2 --reason "..." --severity major -d examples7/

# Accept a node
af accept 1.5.2 --agent verifier-X -d examples7/

# Release a claim
af release 1.5.2 --owner prover-X -d examples7/

# Resolve a challenge
af resolve-challenge ch-XXXX --owner prover-X -d examples7/
```

---

## 10. Key Insight for the Next Orchestrator

**The adversarial framework worked exactly as intended:** a prover declared a dead end, and a verifier caught the logical error and found the correct proof path. The cumulant decomposition `1/Phi_n = C_n*k2 + R_n` is the breakthrough — it reduces the conjecture to proving superadditivity of a specific rational correction term. This is done for n=3 (analytically) and n=4 (numerically, 15K trials). The general case is the remaining challenge.

**Do NOT:**
- Retry subordination-based approaches (proven to fail at finite n)
- Retry direct Cauchy-Schwarz on H vectors (vectors live in different spaces)
- Trust node 1.5.2.3's "dead end" conclusion (it's wrong — see ch-2f457f6e4c5)

**DO:**
- Build on the `1/Phi_n = C_n*k2 + R_n` decomposition
- Try to prove R_n superadditivity for general n, possibly by induction
- Consider the Costa/heat flow alternative as a backup
- Spawn adversarial verifiers for every claimed proof — they found the breakthrough this time
