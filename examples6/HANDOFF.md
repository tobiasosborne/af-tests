# HANDOFF — Fisher Subordination Proof (examples6)

## What This Is

An adversarial proof formalization of the **finite free Fisher information superadditivity conjecture**:

> For monic real-rooted polynomials p, q of degree n with simple roots,
> 1/Phi_n(p boxplus_n q) >= 1/Phi_n(p) + 1/Phi_n(q)

Built with the `af` CLI tool (Adversarial Proof Framework). There are **two** af workspaces:

1. **`fisher_proof/`** — Original proof tree (44 nodes, 61% complete). Established definitions, subordination, chain rule. Hard Lemma 2 remains open.
2. **`strategy3_proof/`** — Modified Strategy 3 attack on Hard Lemma 2 (19 nodes, 6 validated). Created in Session 127.

The source conjecture document is `fisher_subordination_proof.md`.

---

## Quick Start for Next Orchestrator

```bash
cd examples6/strategy3_proof
af status          # 19-node proof tree
af challenges      # 3 open (1 critical, 1 major, 1 minor)
af jobs            # available work
```

**READ THIS ENTIRE HANDOFF BEFORE SPAWNING AGENTS.** The adversarial findings below contain critical information that will prevent wasted work.

---

## Strategy 3 Proof — Current State (Session 127)

### Proof Tree (19 nodes)

```
1   Main conjecture (modified Strategy 3)                        pending
├─ 1.1  Definitions (ADMITTED from fisher_proof)                 admitted
├─ 1.2  Chain rule (ADMITTED from fisher_proof)                  admitted
├─ 1.3  Correction: partition of unity is FALSE                  ✓ validated
│  └─ 1.3.1  Proof: omega_1'+omega_2'=2 NOT 1                   ✓ validated
├─ 1.4  Vector reformulation: u=h+alpha, v=h+beta               ✓ validated
│  └─ 1.4.1  Full proof with norm/bijection details              ✓ validated
├─ 1.5  Clean reformulation: AB >= ||h||^4                       ✓ validated
│  └─ 1.5.1  Algebraic equivalence + n=2 equality               ✓ validated
├─ 1.6  Numerical verification (n=2..8)                          pending
│  └─ 1.6.1  Full results (HAS CRITICAL CHALLENGE)              pending
├─ 1.7  Key structural constraint                                pending
│  ├─ 1.7.1  Analysis: <h,alpha> >= 0 TRUE (800+ trials)        pending
│  ├─ 1.7.2  Sub-lemma: <h,alpha> >= 0 (UNPROVED)               pending  ← KEY
│  └─ 1.7.3  Equality for equally spaced roots                  pending
├─ 1.8  Modified Cauchy-Schwarz approach                         pending
│  ├─ 1.8.1  CS analysis: naive CS too weak                      pending
│  └─ 1.8.2  Inductive approach via derivative identity          pending  ← PROMISING
└─ 1.9  QED (conditional, HAS MAJOR CHALLENGE)                  pending
```

**Statistics:** 19 nodes total — 6 validated, 2 admitted, 11 pending. 3 open challenges.

---

## The Mathematical Situation

### What Is Proved (validated, no gaps)

1. **Partition of unity is FALSE.** omega_1'(nu_k) = omega_2'(nu_k) = 1, so their sum is 2, not 1. The original Strategy 3 from fisher_proof is wrong as stated.

2. **Vector reformulation.** Define u_k = H_p(lambda_{sigma(k)}), v_k = H_q(mu_{tau(k)}), h_k = H_r(nu_k). Then:
   - ||u||^2 = Phi_n(p), ||v||^2 = Phi_n(q), ||h||^2 = Phi_n(r)
   - u = h + alpha, v = h + beta (from chain rule)
   - alpha - beta = u - v (compatibility)

3. **Clean reformulation.** The target inequality is equivalent to:
   - (Phi_n(p) - Phi_n(r))(Phi_n(q) - Phi_n(r)) >= Phi_n(r)^2
   - Equivalently AB >= ||h||^4 where A = ||u||^2 - ||h||^2, B = ||v||^2 - ||h||^2
   - **EQUALITY holds at n=2** (proved analytically)

4. **Numerical confirmation.** Inequality verified for n=2..8 across 4000+ random trials with high-precision (mpmath 100-digit) confirmation of edge cases.

### What Is Conjectured (strong numerical evidence, no proof)

5. **<h,alpha> >= 0 always** (sub-lemma, node 1.7.2). Equivalently sum_k H_r(nu_k) * H_p(lambda_k) >= Phi_n(r). TRUE in 800+ trials across n=2..6 with correct order-preserving sigma.

6. **A > 0 and B > 0 always** (Fisher info decreases under convolution). TRUE in all trials.

### What Is Open (the hard part)

7. **Prove AB >= ||h||^4.** This is the FULL inequality. Note:
   - <h,alpha> >= 0 alone gives only AB >= 0 (too weak)
   - Naive Cauchy-Schwarz gives Phi_r^2 <= Phi_p * Phi_q (also too weak — this is GM bound, we need HM bound)
   - The ||alpha||^2 and ||beta||^2 terms are ESSENTIAL (4<h,alpha><h,beta> >= ||h||^4 fails in ~16% of cases)
   - The full product (2<h,alpha> + ||alpha||^2)(2<h,beta> + ||beta||^2) >= ||h||^4 always holds but no proof exists

---

## Critical Adversarial Finding: The Sigma Pairing

**This is the most important finding from Session 127. Read carefully.**

The numerical prover (agent aea7b8e) claimed `<h,alpha> < 0` in many trials. Both the verifier (agent aac7997) and the structural prover (agent adce425) **independently** challenged this, discovering:

- The numerical prover used an **incorrect bijection sigma** (nearest-neighbor matching)
- The **correct sigma is ORDER-PRESERVING** — forced by the Herglotz property of omega_1 (maps C^+ to C^+), which makes omega_1 globally monotone on R
- With the correct sigma, `<h,alpha> >= 0` in **ALL** tested cases (800+ trials)
- At n=2, proved symbolically: `<h,alpha> = 2(sqrt(D) - s)/(s*D) > 0` since `sqrt(s^2+t^2) > s`

This is tracked as **critical challenge `ch-640cc7d38a4`** on node 1.6.1. The challenge should be resolved by amending node 1.6.1 to use the correct sigma.

**For the next orchestrator:** When spawning numerical agents, ALWAYS specify that sigma must be order-preserving (identity permutation on sorted roots).

---

## Open Challenges

| Challenge ID | Node | Severity | Issue |
|---|---|---|---|
| `ch-640cc7d38a4` | 1.6.1 | **critical** | Numerical prover used wrong sigma. Results about `<h,alpha> < 0` are WRONG. |
| `ch-8d1ffefda33` | 1.9 | **major** | QED is conditional on AB >= \|\|h\|\|^4 being proved (not yet done). |
| `ch-6eba2806382` | 1.5 | minor | Positivity of norms should be stated explicitly. Easy fix. |

---

## Most Promising Proof Directions

### Direction 1: Inductive Approach via Derivative Identity (node 1.8.2)

**The MSS derivative identity** `r'(x) = n * (p^{(1)} boxplus_{n-1} q^{(1)})(x)` is EXACT (verified numerically with error = 0). Here p^{(1)} = (1/n)p' has roots at the critical points of p.

**Idea:** Base case n=2 is proved (equality). If the inequality holds at degree n-1, can it be "lifted" to degree n?

**Obstacle:** The ratio Phi_n(p) / Phi_{n-1}(p^{(1)}) is NOT constant (ranges 1.6 to 6). A simple scaling argument fails. Need a formula relating Phi_n to Phi_{n-1} and the interlacing structure.

**Status:** Promising but needs a key lemma connecting Phi_n and Phi_{n-1}. No one has attempted this yet.

### Direction 2: Prove Sub-Lemma <h,alpha> >= 0 (node 1.7.2)

**Statement:** sum_k H_r(nu_k) * H_p(lambda_k) >= sum_k H_r(nu_k)^2 = Phi_n(r)

**Why it matters:** It's a necessary sub-lemma (numerically always true) that constrains the proof space. Even though it alone doesn't close AB >= ||h||^4, it's a natural intermediate step.

**Possible approaches:**
- Herglotz convexity: omega_1 maps C^+ to C^+, omega_1'(nu_k) = 1, so the "curvature" omega_1'' has constrained sign
- Matrix model: trace inequality involving resolvent Hessian of log-determinant
- Monotone coupling: omega_1 is globally monotone on R, so lambda_k and nu_k are "monotonically coupled"

### Direction 3: Direct Algebraic Identity for AB - ||h||^4

For the MSS convolution specifically, there may be a closed-form expression for AB - ||h||^4 in terms of the polynomial coefficients that is manifestly non-negative.

**Key fact:** At n=2, AB - ||h||^4 = 0 EXACTLY (not just numerically). At n=3 with equally spaced roots, also equality. This suggests the "excess" AB - ||h||^4 might factor as a sum of squares or have a spectral interpretation.

### Direction 4: Reformulate as Phi_r <= HM(Phi_p, Phi_q)

The target inequality is equivalent to: Phi_r <= 2*Phi_p*Phi_q / (Phi_p + Phi_q) = HM(Phi_p, Phi_q).

This is a single inequality about three scalars defined by root configurations. May be amenable to:
- Matrix trace inequality (random matrix model A + UBU*)
- Monotonicity/concavity of 1/Phi under convolution
- Information-theoretic arguments (1/Phi is the "Fisher reciprocal")

---

## Equality Case Structure

**n=2:** EXACT equality always. Proved algebraically: D = (b-a)^2 + (d-c)^2, AB = 4/D^2 = Phi_2(r)^2.

**n=3 with equally spaced roots:** EXACT equality. The convolution preserves equal spacing, and gap_r^2 = gap_p^2 + gap_q^2 (Pythagorean).

**n >= 3 generic:** STRICT inequality. Minimum ratio AB/||h||^4 approaches 1 as p approaches q.

**Interpretation:** The inequality says "the squared effective gap of the free convolution is at least the sum of the squared effective gaps." This is a finite analogue of the free Cramer-Rao inequality.

---

## What NOT to Do (Traps)

1. **Do NOT assume partition of unity.** omega_1' + omega_2' = 2, NOT 1. This is validated.
2. **Do NOT use nearest-neighbor sigma.** The correct bijection is ORDER-PRESERVING (identity on sorted roots). Using nearest-neighbor gives wrong sign for <h,alpha>.
3. **Do NOT expect naive Cauchy-Schwarz to close.** It gives Phi_r^2 <= Phi_p*Phi_q (GM bound). We need the strictly stronger HM bound.
4. **Do NOT assume <h,alpha> alone suffices.** Even with <h,alpha> >= 0, you still need the ||alpha||^2, ||beta||^2 terms to close AB >= ||h||^4.
5. **Do NOT confuse MSS convolution with Haar unitary average.** They coincide at n=2 but differ for n >= 3. The correct formula is: c_k = sum_{i+j=k} [(n-i)!(n-j)! / (n!(n-k)!)] * a_i * b_j.

---

## Orchestration Notes

- **Subagent rule:** Every job must be a fresh subagent (no agent reuse). Max 5 parallel.
- **Verifier standard:** Accept ONLY airtight steps. Challenge anything with gaps, sign errors, unstated assumptions. Look for counterexamples.
- **Prover standard:** Be honest about gaps. A sorry with notes beats a false claim.
- **Sigma convention:** ALWAYS specify order-preserving sigma when spawning numerical agents.
- All work stays in `examples6/`. Do NOT touch the Lean project files.

### How to Work With af

```bash
# See what needs doing
af jobs
af challenges

# Prover workflow
af claim <node> --owner <name> --role prover
af refine <node> --owner <name> -s "statement"
af amend <node> --owner <name> --statement "corrected text"
af resolve-challenge <challenge-id> --owner <name> --response "..."
af release <node> --owner <name>

# Verifier workflow
af claim <node> --owner <name> --role verifier
af accept <node> --agent <name>
af challenge <node> --owner <name> --reason "..."
af release <node> --owner <name>

# Admit without proof (introduces taint)
af admit <node>
```

---

## Suggested Next Session Plan

### Phase 1: Resolve Critical Challenge (10 min)

1. Resolve `ch-640cc7d38a4` on node 1.6.1: amend the numerical verification to use order-preserving sigma, confirm <h,alpha> >= 0.
2. Resolve `ch-6eba2806382` on node 1.5: add explicit positivity statement.

### Phase 2: Prove Sub-Lemma <h,alpha> >= 0 (node 1.7.2) (main effort)

Spawn 2-3 prover agents to try different approaches in parallel:
- **Prover A:** Herglotz convexity / omega_1'' sign argument
- **Prover B:** Matrix model trace inequality
- **Prover C:** Direct computation from subordination equation F(z,w) = 0

Spawn 1 verifier to review any claimed proofs.

### Phase 3: Attack AB >= ||h||^4 (if sub-lemma proved)

Spawn provers for the inductive approach (node 1.8.2):
- Find the relationship between Phi_n(p) and Phi_{n-1}(p^{(1)})
- Attempt to lift the n-1 inequality to degree n
- Look for a direct algebraic identity for AB - ||h||^4

---

## fisher_proof Workspace (Original, for Reference)

```bash
cd examples6/fisher_proof
af status          # 44 nodes, 61% complete
af progress        # completion metrics
```

Key validated results to ADMIT into strategy3_proof if needed:
- Definitions (1.1): P_n, boxplus_n, G_p, H_p, Phi_n
- Base case n=2 (1.4): equality
- Subordination construction (1.5): omega_1, omega_2 exist as algebraic Herglotz functions
- Chain rule (1.6): omega_1'(nu_k) = 1, H_r = H_p - alpha

---

## Files

```
examples6/
├── fisher_subordination_proof.md   # Source proof strategy document
├── HANDOFF.md                      # This file
├── fisher_proof/
│   ├── meta.json                   # af workspace metadata
│   ├── ledger/                     # 233 event log entries
│   └── strategy_reports.md         # 3 proof strategies for Hard Lemma 2
└── strategy3_proof/
    ├── meta.json                   # af workspace metadata
    ├── ledger/                     # 61 event log entries
    ├── numerical_verify.py         # Main numerical verification
    ├── verify_pairing.py           # Subordination pairing analysis
    ├── verify_edge_cases.py        # Edge cases (degenerate, spread-out)
    ├── verify_careful.py           # High-precision mpmath verification
    ├── verify_formula.py           # MSS formula verification
    ├── verify_violations.py        # False violation investigation
    ├── investigate_correct_mss.py  # Haar vs permutation comparison
    ├── investigate_deep.py         # Deep structural analysis
    ├── investigate_exact.py        # Correct MSS formula tests
    ├── investigate_final.py        # Definitive comprehensive test
    ├── investigate_gram.py         # Gram matrix analysis
    ├── investigate_induction.py    # Derivative identity and induction
    ├── investigate_light.py        # Gap structure and monotone coupling
    ├── investigate_n2_exact.py     # Exact n=2 symbolic analysis
    └── investigate_structural.py   # Initial structural investigation
```
