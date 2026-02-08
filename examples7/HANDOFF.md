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

## 6. Next Steps (Priority Order)

1. **Full R_4 analytical proof** — The key open problem
   - Try SDP/SOS on gap numerator polynomial
   - Try generalized matrix Cauchy-Schwarz (2x2 or 3x3)
   - Try perturbation from proved k3=0 case

2. **General R_n proof** — Would close the conjecture for all n
   - Induction on n?
   - Universal structure in R_n?

3. **DO NOT RETRY**: Joint concavity, Titu/Engel, perspective function, term-by-term partial fractions

---

## 7. Previous Sessions

### Session 131 (this): Wave 3 — 2 verifiers validated, 1 prover didn't close
### Session 130: Wave 2 — k3=0 proved, C_n verified, R_n pattern confirmed
### Session 129: Crashed orchestrator recovery, Wave 1 results collected
