# HANDOFF — Fisher Subordination Proof (examples6)

## What This Is

An adversarial proof formalization of the **finite free Fisher information superadditivity conjecture**:

> For monic real-rooted polynomials p, q of degree n with simple roots,
> 1/Phi_n(p boxplus_n q) >= 1/Phi_n(p) + 1/Phi_n(q)

Built with the `af` CLI tool (Adversarial Proof Framework). The workspace is at `examples6/fisher_proof/`. The source conjecture is in `examples6/fisher_subordination_proof.md`.

## Quick Start

```bash
cd examples6/fisher_proof
af status          # see proof tree (44 nodes)
af progress        # completion metrics (61%)
af challenges      # 12 open, mostly minor
af jobs            # available work
```

## Proof Architecture (node tree)

```
1   Main conjecture
├─ 1.1  Definitions (P_n, boxplus_n, G_p, H_p, Phi_n)     ✓ validated
├─ 1.2  Admitted: MSS real-rootedness                       ✓ admitted
├─ 1.3  Admitted: MSS derivative identity                   ✓ admitted
├─ 1.4  Base case n=2 (EQUALITY holds)                      ✓ validated
├─ 1.5  Finite subordination                                ✓ mostly validated
│  ├─ 1.5.1  Polynomial equation construction               ✓ validated
│  ├─ 1.5.2  Selection principle (ALL n roots in C^+)       ✓ validated (corrected)
│  ├─ 1.5.3  Herglotz property / branch selection           ~ needs child 1.5.3.1 verified
│  └─ 1.5.4  Algebraic (NOT rational) structure             ~ amended, pending review
├─ 1.6  Chain rule for discrete Hilbert transform            ✓ mostly validated
│  ├─ 1.6.1  Pole matching                                  ✓ validated
│  ├─ 1.6.2  Injectivity of sigma (corrected proof)         ✓ validated
│  ├─ 1.6.3  Bijectivity                                    ✓ validated
│  ├─ 1.6.4  Laurent expansion setup                        ✓ validated
│  ├─ 1.6.5  Residue matching (omega_1' = 1)                ✓ validated
│  └─ 1.6.6  Chain rule QED                                 ✓ validated
├─ 1.7  Main inequality (Hard Lemma 2)                      ✗ OPEN
│  ├─ 1.7.1  Vector reformulation                           ✓ validated
│  ├─ 1.7.2  Target inequality in vector form               ✓ validated
│  ├─ 1.7.3  Constraints on (alpha, beta) — corrected       ~ pending review
│  └─ 1.7.4  Status: UNPROVED                               ~ pending review
└─ 1.8  QED summary                                         ~ pending review
   ├─ 1.8.1  Proved components
   ├─ 1.8.2  Open gaps
   ├─ 1.8.3  Admitted results
   └─ 1.8.4  Proof status
```

## Key Discoveries Made This Session

### 1. Selection Principle Correction (node 1.5.2)
**Original claim (FALSE):** Exactly one of n preimages of G_p(w)=c lies in C^+.
**Corrected (PROVED):** ALL n preimages lie in C^+.
- Proof: (A) f(w) = p'(w) - nc·p(w) has no real roots (imaginary part argument). (B) No roots in C^- (anti-Herglotz property of G_p).
- Consequence: branch selection for omega_1 uses asymptotics (omega_1(z) ~ z), not uniqueness.

### 2. Subordination Functions Are Algebraic, Not Rational (node 1.5.4)
Verified at n=2: omega_1 involves sqrt of a degree-4 polynomial. The rational Herglotz partial-fraction representation is INVALID. This killed the original proof strategy for the main inequality.

### 3. Injectivity of Sigma (node 1.6.2)
Original counting argument was flawed. Corrected via: (a) real preimages of roots of p under omega_1 must be roots of r, (b) this forces omega_1 to have zero real poles, (c) hence omega_1 is globally monotone on R, hence injective.

## The Open Problem: Hard Lemma 2

The inequality `||u||^2 ||v||^2 >= ||h||^2(||u||^2 + ||v||^2)` where u = h + alpha, v = h + beta, and alpha, beta come from the algebraic subordination structure.

**FAILS for arbitrary vectors** (counterexample: h=(1,0), alpha=(10,0), beta=(0,0)).

Three proof strategies are documented in `strategy_reports.md`:

### Strategy 3 Is Most Promising (Partition of Unity)

It gives a **conditional proof** reducing everything to two claims:

**Claim A (Partition of unity):** omega_1'(nu_k) + omega_2'(nu_k) = 1 at roots of r.

**Claim B (Key Lemma):** sum_k H_p(omega_1(nu_k))^2 · omega_1'(nu_k) <= Phi_n(p).

If both hold, the main theorem follows by Cauchy-Schwarz (Titu/Engel form).

### CRITICAL TENSION
The chain rule (node 1.6.5, validated) proves omega_1'(nu_k) = 1. If omega_2'(nu_k) = 1 also holds, then omega_1' + omega_2' = 2, NOT 1. This **contradicts** the partition of unity.

**Immediate action for next session:** Verify numerically at n=2:
- Compute omega_1'(nu_k) and omega_2'(nu_k) at the roots of r = p boxplus_2 q
- Check whether they sum to 1 or 2
- If 2: Strategy 3 as stated is wrong, but the algebraic structure may support a modified decomposition (e.g., omega_1'/(omega_1' + omega_2') is the correct weight)
- If 1: the chain rule proof in 1.6.5 has a sign/normalization error that needs fixing

## Open Challenges (12 remaining)

Mostly minor (formatting, dependency declarations, presentation). The only blocking ones:
- `ch-62991d27985` on 1.7.4 (major): status node falsely endorses constraint (ii) which was corrected
- `ch-bffa7e064f3` on 1.7.4 (note): missing explicit counterexample

## How to Work With af

```bash
# See what needs doing
af jobs
af challenges

# Prover workflow
af claim <node> --owner <name> --role prover
af refine <node> --owner <name> -s "statement" -t claim
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

## Orchestration Notes

- **Subagent rule:** Every job must be a fresh subagent (no agent reuse). Max 5 parallel.
- **Verifier standard:** Accept ONLY airtight steps. Challenge anything with gaps, sign errors, unstated assumptions. Look for counterexamples.
- **Prover standard:** Be honest about gaps. A sorry with notes beats a false claim.
- All work stays in `examples6/`. Do NOT touch the Lean project files.

## Files

```
examples6/
├── fisher_subordination_proof.md   # Source proof strategy document
├── HANDOFF.md                      # This file
└── fisher_proof/
    ├── meta.json                   # af workspace metadata
    ├── ledger/                     # 233 event log entries (append-only)
    └── strategy_reports.md         # 3 proof strategies for Hard Lemma 2
```
