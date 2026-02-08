# HANDOFF: Fisher Superadditivity Proof Tree

**Session date:** 2026-02-08 (Sessions 130-131)
**Tool:** `af` (Adversarial Proof Framework) in `examples7/`
**Agents used:** 19 total (9 provers, 10 verifiers) across 5 waves

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

## 2. Breakthrough: Cumulant Decomposition

```
1/Phi_n = C_n * kappa_2 + R_n(kappa_2, ..., kappa_n)
```

- **C_n = 4/(n^2*(n-1))** [VALIDATED by verifier-10, verifier-10b]
  - Original claim C_n = 2/(n(n-1)) was WRONG (off by factor 2/n)
  - C_2=1, C_3=2/9, C_4=1/12, C_5=1/25, C_6=1/45
- **kappa_k** = finite free cumulants (additive under MSS convolution)
- **R_n** = nonlinear correction (always <= 0, weight-2 homogeneous)
- Conjecture REDUCES TO: R_n is superadditive

---

## 3. Current Proof State

### VALIDATED NODES (adversarially verified)
- **Node 1.5.2.5**: n=3 proof COMPLETE (Cauchy-Schwarz on k3^2/k2^2)
- **Node 1.5.2.6.1**: R_4 k3=0 case PROVED analytically [VALIDATED by verifier-11]
  - Proof: Key Lemma (sA+tB <= (s+t)C) + Cauchy-Schwarz
  - 15 independent checks, ~1.5M numerical trials, 0 violations
- **Node 1.5.5.1**: General C_n formula + R_n pattern [VALIDATED by verifier-10b]
  - C_n = 4/(n^2(n-1)) for n=2,...,10
  - R_n superadditivity: 0 violations for n=3,4,5,6
  - R_4 exact rational formula verified

### OPEN (main remaining challenge)
- **Full R_4 analytical proof (k3 nonzero)**: NOT CLOSED
  - Joint concavity FAILS (Hessian indefinite)
  - Term-by-term partial fraction subadditivity FAILS
  - PROVER-12 tried decomposition into Term_A + Term_B — neither individually subadditive
  - Numerically verified: 0/447K violations
  - Promising: SOS certificate, perturbation from k3=0, matrix Cauchy-Schwarz

### NUMERICAL ONLY
- R_5, R_6 superadditivity: 0 violations (no analytical proof)
- General R_n pattern: numerically confirmed for n=2,...,10

---

## 4. Agent Summary (this session pair 130-131)

### Wave 1 (from crashed orchestrator, completed)
- PROVER-8: Rewrote node 1.5.2, resolved 4 challenges
- PROVER-9: R_4 structural analysis (node 1.5.2.6)
- PROVER-10: General R_n pattern, Hermite proof of C_n
- VERIFIER-8: n=3 proof correct
- VERIFIER-9: R_4 formula confirmed, C_n error found

### Wave 2 (Session 130)
- **PROVER-10b** (a9e9996): C_n for n=2,...,10, R_n superadditivity → node 1.5.5.1
- **PROVER-11** (abecf90): k3=0 PROVED, full case numerically verified → node 1.5.2.6.1
- **VERIFIER-10** (aae363f): C_n formula audit, node 1.5.2 amended

### Wave 3 (Session 131)
- **VERIFIER-11** (aa10331): k3=0 proof VALID → node 1.5.2.6.1 VALIDATED
- **VERIFIER-10b** (adb15a3): C_n + R_n claims VALID → node 1.5.5.1 VALIDATED
- **PROVER-12** (a07f251): Full R_4 attempt — did NOT close proof, found Term_A/B decomp fails

---

## 5. Key Files

### Reports
- `R4_proof_result.md` — PROVER-11's k3=0 proof writeup
- `R4_proof_attempt.md` — PROVER-9's structural analysis
- `R4_verification.md` — VERIFIER-9's R_4 audit
- `Rn_general_report.md` — PROVER-10b's general pattern report
- `n3_proof_verification.md` — VERIFIER-8's n=3 audit
- `verifier11_report.md` — VERIFIER-11's k3=0 verification
- `verifier10b_report.md` — VERIFIER-10b's C_n verification

### Verification Scripts
- `R4_prover11_final.py` — Consolidated R_4 verification (all tests pass)
- `Rn_prover10b.py` — Comprehensive R_n computation
- `verifier11_check.py` — 15-check adversarial k3=0 verification
- `verifier10b_check.py` — Independent C_n/R_n verification

---

## 6. Orchestrator Assessment: The Polynomial Approach Has Hit a Wall

**Node requiring radical revision: 1.5.2.6** (R_4 superadditivity)

The current approach — decompose R_n into polynomials, then prove non-negativity
of the gap polynomial via algebraic manipulation — has been exhaustively tried
by 4 prover agents and **every standard technique has failed**:

| Technique | Result | Why it fails |
|-----------|--------|--------------|
| Joint concavity of -R_4 | FAILED | Hessian is indefinite |
| SOS on gap numerator | FAILED | Mixed-sign cross terms |
| Perspective function | BLOCKED | Denominator not linear in k4 |
| Titu/Engel Cauchy-Schwarz | INAPPLICABLE | Denominator nonlinear (degree 10) |
| Partial fraction subadditivity | FAILED | -K4/(24K2) term not subadditive |
| Term_A + Term_B decomposition | FAILED | Neither piece individually subadditive |

This pattern — where the inequality is numerically rock-solid (0/2M+ violations)
but resists all polynomial-level proofs — strongly suggests **the inequality is
true for structural reasons that pure algebraic manipulation cannot access.**

### The analogy with classical information theory

The classical analog, Stam's inequality (1/I(X+Y) >= 1/I(X) + 1/I(Y)), is NOT
proved by expanding in cumulants and doing polynomial arithmetic. It's proved via:
- **de Bruijn's identity** (Fisher info = derivative of entropy along heat flow)
- **Data processing inequality** (Fisher info decreases under channels)
- **Optimal transport** arguments

The finite free version likely needs a similarly structural argument.

### Directions for novel prover agents

The next orchestrator should spawn provers that explore **non-polynomial** approaches:

1. **Finite free heat flow / Ornstein-Uhlenbeck**: Is there a discrete analog of
   de Bruijn's identity for Phi_n? The MSS convolution with a Gaussian polynomial
   should monotonically decrease Phi_n — if this can be established, it may yield
   the inequality via a semigroup argument.

2. **Monotonicity under natural operations**: Does Phi_n satisfy a data processing
   inequality? If there's a "channel" operation on polynomials that contracts Phi_n,
   and MSS convolution factors through it, the inequality follows.

3. **Representation theory of S_n**: MSS convolution comes from expected
   characteristic polynomials of random matrices. The cumulants kappa_k have
   algebraic meaning in terms of S_n representations. Perhaps R_n superadditivity
   follows from a representation-theoretic identity.

4. **Log-convexity / Schur-convexity of root gaps**: The inequality may follow
   from properties of the root interlacing that MSS convolution guarantees,
   rather than from the cumulant expansion.

5. **Direct n=4 via different parametrization**: Instead of (k2,k3,k4), use
   the roots directly. Phi_4 has a clean expression in terms of root gaps
   delta_ij = lambda_i - lambda_j. The MSS convolution has known root interlacing
   properties. Perhaps the inequality follows from these geometric constraints.

6. **McCrimmon-style operator identity**: In Jordan algebra theory, many
   identities that resist direct polynomial proof follow from operator identities
   (U, T, L operators). Is there an operator framework for Phi_n?

### What to preserve from current work

The cumulant decomposition framework IS correct and useful:
- C_n = 4/(n^2(n-1)) is validated
- The reduction to R_n superadditivity is clean
- The k3=0 case and n=3 case are proved and can serve as base cases
- The numerical infrastructure is solid for testing new ideas

The framework should be KEPT but the proof strategy for the core inequality
needs to come from outside the "polynomial gap non-negativity" paradigm.

---

## 7. DO NOT RETRY (exhaustively failed approaches)

- Joint concavity of -R_4 or f(u,v)
- Titu/Engel or standard Cauchy-Schwarz on the fraction
- Perspective function / convex conjugate
- Term-by-term partial fraction subadditivity
- Direct SOS decomposition of gap numerator in (s,t,u,v,m,w) variables
- Any approach that starts with "expand the gap polynomial and show it's non-negative"

---

## 8. Previous Sessions

### Session 131 (this): Wave 3 — 2 verifiers validated, 1 prover didn't close. Orchestrator assessment added.
### Session 130: Wave 2 — k3=0 proved, C_n verified, R_n pattern confirmed
### Session 129: Crashed orchestrator recovery, Wave 1 results collected
