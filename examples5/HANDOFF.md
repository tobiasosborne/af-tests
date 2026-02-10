# Wilde's Conjecture — Proof Tree Handoff

**Last updated:** 2026-02-10
**Status:** Critical error identified and marked; corrected structure scaffolded

---

## What This Is

A formal adversarial proof tree (built with `af`) for a path-integral
hockey-stick representation of conditional entropy differences — the key
intermediate result toward Wilde's continuity conjecture.

**Proof workspace:** `./wilde_proof/`

---

## The Error (v3 → v4)

### Root Cause

The v3 proof used an **incorrect single-term Frenkel formula**:

```
D(ρ‖σ) = ∫₀^∞ [E_γ(ρ‖σ) − (1−γ)₊] / [γ(1+γ)] dγ    ← WRONG
```

This fails a basic numerical test: for ρ = |0⟩⟨0|, σ = I/2 (d=2), it
gives 0.432 instead of log(2) ≈ 0.693.

### Correct Formula (FR)

The Frenkel representation has **two** hockey-stick terms:

```
D(ρ‖σ) = ∫₁^∞ [ E_γ(ρ‖σ)/γ + E_γ(σ‖ρ)/γ² ] dγ
```

The second term involves the **reverse** hockey-stick divergence E_γ(σ‖ρ)
with a 1/γ² kernel. This was confirmed independently by Liu–Hirche–Cheng
(2025), arXiv:2507.07065v2.

### Impact on the Proof Tree

| Nodes | Status | Detail |
|-------|--------|--------|
| 1.1–1.5 | **Unaffected** | Full-rank assumption, CE-RE, FTC, DER, forward HS derivative |
| 1.6.1 | **Critical challenge** | Cites the wrong FR-bip formula |
| 1.6, 1.6.2–1.6.5 | **Critical/major challenges** | DER-HS uses single integral with wrong kernel |
| 1.7, 1.7.3–1.7.6 | **Critical challenges** | MAIN formula + Fubini argument use wrong DER-HS |
| 1 (root) | **Critical challenge** | Statement is the single-integral MAIN, not corrected MAIN' |

---

## What Was Done This Session

1. **Raised 13 critical/major challenges** on all nodes affected by the
   wrong Frenkel formula (nodes 1, 1.6–1.6.5, 1.7.3–1.7.6)

2. **Added corrected definitions:**
   - `frenkel_integral_corrected` — two-term FR, FR-c, and FR-bip formulas
   - `reverse_spectral_projector` — Q_β(t), M_fwd(t), M_rev(t)

3. **Added external reference:**
   - `liu_hirche_cheng_2025` — independent confirmation of the correct formula

4. **Added node 1.8 (HS-DER-rev)** with 4 children (1.8.1–1.8.4):
   the reverse hockey-stick derivative d/dt E_β(τ(t)‖ρ(t)) =
   Tr[Q_β(t)(𝟙_A⊗δ_B − βδ_AB)], proved by the same off-block-diagonal
   argument as node 1.5

5. **Added v4 skeleton** (`wilde_path_integral_v4_skeleton.md`) and
   **corrected LaTeX** (`wilde_proof_corrected.tex`) documenting the
   full corrected proof structure

---

## Current State

```
Proof tree:  41 nodes (36 validated, 5 pending)
Challenges:  13 open (all critical/major on error-affected nodes)
Definitions: 10 (including 2 new corrected ones)
Externals:   1 (Liu–Hirche–Cheng 2025)
```

### Corrected Main Result (MAIN')

```
H(A|B)_σ − H(A|B)_ρ = −∫₀¹ [ ∫_{1/d_A}^{M_fwd(t)} Tr[P_β(t) δ_AB^{(β)}]/β dβ
                              + ∫_{d_A}^{M_rev(t)} Tr[Q_β(t)(𝟙_A⊗δ_B − βδ_AB)]/β² dβ ] dt
```

Verified numerically to < 8×10⁻¹⁵ error across 37 test cases (see
`wilde_numerics/verify_hockey_stick.jl`).

---

## What Needs Doing Next

### Priority 1: Resolve challenges on nodes 1.6–1.7

The challenged nodes need their statements **amended** to use the corrected
two-term formula. The corrected content is fully specified in
`wilde_proof_corrected.tex` (nodes marked CORRECTED). Workflow:

1. Claim each challenged node as prover
2. `af amend` the statement to the corrected version (from the tex)
3. `af resolve-challenge` each open challenge
4. Release and have verifier re-validate

**Obstacle:** `af amend` requires the node to be in `pending` state, but
challenged nodes are still `validated`. May need to `af archive` the old
nodes and create fresh replacements, or check if `af` supports a
validated→pending transition.

### Priority 2: Validate new node 1.8 (HS-DER-rev)

Node 1.8 and children 1.8.1–1.8.4 are `pending`. A verifier should review
and accept them — the proof is a straightforward role-swap of node 1.5.

### Priority 3: Update root node statement

Node 1 needs its statement changed from MAIN to MAIN'. This is the last
step after 1.6 and 1.7 are corrected.

### Priority 4: Open obligations from v4 skeleton (§8)

| ID | Description | Status |
|----|-------------|--------|
| O1 | Justify d/dt ↔ ∫dβ exchange (both terms) | OPEN (routine) |
| O2 | Non-full-rank regularisation | OPEN (standard) |
| O3 | Bound forward and reverse t-integrals as f(β,ε) | OPEN — key |
| O4 | Numerical verification of MAIN' | **DONE** |
| O5 | Evaluate ∫f(β)/β dβ + ∫g(β)/β² dβ for bounds from O3 | OPEN |
| O6 | Is the reverse term benign for the continuity bound? | OPEN — new |

---

## Key Files

| File | Purpose |
|------|---------|
| `wilde_proof/` | `af` proof workspace (nodes, ledger, defs, externals) |
| `wilde_path_integral_v3_skeleton.md` | Old (incorrect) proof skeleton |
| `wilde_path_integral_v4_skeleton.md` | Corrected proof skeleton |
| `wilde_proof_corrected.tex` | Full corrected proof tree as LaTeX |
| `wilde_numerics/verify_hockey_stick.jl` | Numerical verification (37 tests) |
| `wilde_numerics/corrected_formula.tex` | Derivation of corrected FR-bip |

---

## Quick Start for Next Session

```bash
cd examples5/wilde_proof
af status                    # See tree with challenges
af challenges                # List all 13 open challenges
af get 1.6.1                 # See the critical Frenkel error
af jobs --role verifier      # 5 pending nodes to review (1.8.*)
```
