# Handoff: examples11 — Mixed State Tomography (arXiv:2511.15806)

## Paper
**"Mixed state tomography reduces to pure state tomography"**
Pelecanos, Spilecki, Tang, Wright (2024) — arXiv:2511.15806

## Status: COMPLETE (100% validated)

All 45 proof nodes formalized, all 11 adversarial challenges resolved, all nodes validated.

## Structure

- **45 proof nodes** across 7 parts + top-level claim
- **25 definitions** (density matrix, fidelity, Schur-Weyl duality, GPS estimator, etc.)
- **18 external references** (12 with PDFs in `refs/`)
- **8 outline stages** mapped (S1-Prelim through S8-Applications)
- **249 ledger entries** recording the full formalization trace

## Proof Tree (7 parts)

| Part | Label | Nodes | Content |
|------|-------|-------|---------|
| I | S1-Prelim | 1.1.1–1.1.6 | SoS partial trace, Jucys-Murphy, symmetric subspace projector, SWAP identities |
| II | S2-Purification | 1.2.1–1.2.6 | Double Schur basis lemmas, random purification formula, acorn trick (Thm 1.1) |
| III | S3-PureTomo | 1.3.1–1.3.5 | Hayashi algorithm, t-designs, GKKT moment bounds, concentration, Thm 1.2 |
| IV | S4-MixedTomo | 1.4.1–1.4.3 | Purification + pure tomo + partial trace = mixed tomo (Thm 1.3) |
| V | S5-GPSPure | 1.5.1–1.5.7 | Moment operators, first/second moment, GPS pure state moments (Thm 1.4) |
| VI | S6-GPSMixed | 1.6.1–1.6.4 | Partial trace helper, Mix(GPS) loose (Thm 1.5), Mix+(GPS) tight (Thm 1.6) |
| VII | S7-PGM + S8-Apps | 1.7.1–1.7.6 | PGM interpretation, limited-entanglement, shadow tomo, metrology |

## Adversarial Verification (11 challenges, all resolved)

### Critical/Major fixes (4)
1. **1.3.1** (major): Beta distribution parameter — was Beta(1,d-1), corrected to Beta(n+1,d-1)
2. **1.3.4** (major): Covering net radius — was 1/3, corrected to 1/4 per paper line 1348
3. **1.3.5** (critical): q parameter + fidelity argument — was q=epsilon/2 with hand-wave, corrected to q=sqrt(epsilon) with full Davis-Kahan argument
4. **1.2.4** (major): Schur transform channel description — 6-step procedure now matches paper exactly

### Minor acknowledgements (7)
- 1.1.3: Missing dependency on Proposition 2.2
- 1.1.5: Missing dependencies on Propositions 2.4, 2.6
- 1.2.1: Scope note on ell(lambda) <= r vs min(d,r)
- 1.3.3: Moment bound range (2 <= k <= t/3 vs all integers)
- 1.4.1: Error metric clarification (fidelity vs trace distance)
- 1.4.2: Error budget split (delta/2 + delta/2)
- 1.7.4: Error metric (fidelity vs trace distance)

## Files

| File | Description |
|------|-------------|
| `main.tex` | Full paper source (2115 lines) |
| `purifychan.tex` | Purification channel details (350 lines) |
| `pgm.tex` | PGM appendix (138 lines) |
| `ledger/` | 249 formalization trace entries |
| `externals/` | 18 external reference records |
| `refs/` (repo root) | 12 downloaded reference PDFs |

## No remaining work

The formalization is complete. All nodes validated with quality score 100/100.
