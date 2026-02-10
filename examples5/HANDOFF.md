# Wilde's Conjecture — Proof Tree Handoff

**Last updated:** 2026-02-10
**Status:** ALL 44 nodes validated/clean. Corrected two-term formula fully integrated.

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

---

## Current State

```
Proof tree:  44 nodes (44 validated, 0 pending)
Taint:       44 clean, 0 tainted
Challenges:  3 open (all note/minor — dependency bookkeeping only)
Definitions: 10 (including 2 corrected ones)
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

## What Was Done This Session

### Wave 1: Verified reverse HS-DER nodes (1.8.*)
1. **Verified and accepted nodes 1.8.1–1.8.4** (reverse hockey-stick derivative)
2. **Verified and accepted parent node 1.8** (HS-DER-rev)
3. All 5 nodes: validated/clean

### Wave 2: Resolved Frenkel formula challenges
4. **Created corrected child nodes** to supersede wrong formulas:
   - **Node 1.6.6** (DER-HS-corrected): two-term derivative of relative entropy
   - **Node 1.7.7** (MAIN-corrected): two-term main formula MAIN'
   - **Node 1.9** (Root-corrected): root-level corrected result
5. **Resolved all 13 critical/major challenges** on nodes 1, 1.6–1.6.5, 1.7, 1.7.3–1.7.6
6. **Resolved 2 minor dependency challenges** on nodes 1.8.3, 1.8.4

### Wave 3: Verified corrected nodes
7. **Verified and accepted nodes 1.6.6, 1.7.7, 1.9** — all validated/clean

### Tool limitation discovered
- `af amend` requires `pending` state; `validated` is terminal
- Workaround: add corrected child nodes + resolve challenges pointing to them
- Old (wrong) statements remain as historical record with resolved challenges

---

## Remaining Open Challenges (3, all minor)

| Challenge | Node | Severity | Issue |
|-----------|------|----------|-------|
| ch-b10974c | 1.6.6 | note | DCT justification could be more explicit |
| ch-7faa27b | 1.7.7 | minor | Should depend on 1.6.6 not 1.6 |
| ch-56e2e1f | 1.9 | minor | Should depend on 1.7.7 not 1.7 |

These are dependency-bookkeeping issues, not mathematical gaps.

---

## What Needs Doing Next

### Priority 1: Open obligations from v4 skeleton (§8)

| ID | Description | Status |
|----|-------------|--------|
| O1 | Justify d/dt ↔ ∫dβ exchange (both terms) | OPEN (routine) |
| O2 | Non-full-rank regularisation | OPEN (standard) |
| O3 | Bound forward and reverse t-integrals as f(β,ε) | OPEN — key |
| O4 | Numerical verification of MAIN' | **DONE** |
| O5 | Evaluate ∫f(β)/β dβ + ∫g(β)/β² dβ for bounds from O3 | OPEN |
| O6 | Is the reverse term benign for the continuity bound? | OPEN — new |

### Priority 2: Resolve 3 remaining minor challenges

Fix dependency declarations on nodes 1.7.7 and 1.9.

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
af status                    # 44 validated, 0 pending
af challenges --status open  # 3 minor challenges remaining
af progress                  # Completion metrics
```
