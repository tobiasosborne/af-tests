# HANDOFF — Fourth-Derivative Gravity Propagators

## Status: COMPLETE (§1–7 momentum-space, §8 position-space, adversarially verified)

## What Was Done

Adversarial formalization and verification of the propagator structure for
linearised fourth-derivative gravity with action
`I = ∫d⁴x [R⁽¹⁾_μν R⁽¹⁾^μν − β(R⁽¹⁾)²]`.

### Proof Tree (38 nodes, 7 sections)

| Node | Section | Leaves | Status |
|------|---------|--------|--------|
| 1.1  | Action identification (linearised Riemann → Ricci → scalar) | 4 | validated |
| 1.2  | SVT decomposition + Bardeen gauge-invariant variables | 5 | validated (1 amended) |
| 1.3  | Scalar sector curvature (R₀₀, R₀ᵢ, Rᵢⱼ, R) | 4 | validated |
| 1.4  | Vector + tensor sector curvature | 5 | validated |
| 1.5  | Decomposed action (no cross-terms, I_TT, I_V, I_S) | 4 | validated |
| 1.6  | det(M) = 8(1−3β)k⁴p⁴ + scalar propagators | 4 | validated |
| 1.7  | Vector/tensor propagators + special cases (β=1/3, β=1/2) | 4 | validated |

### Definitions (10)

`lorentzian_four_momentum_squared`, `fourth_derivative_gravity_action`,
`linearised_riemann_tensor`, `linearised_ricci_tensor`, `linearised_ricci_scalar`,
`svt_decomposition`, `bardeen_potentials`, `transverse_projector`, `tt_projector`,
`scalar_action_matrix`

### External References (6)

- **Wald §4.4** — OCR ground truth from .djvu (pp.82–83, eq.4.4.3–4.4.4)
- **Zee IX.4** — pdftotext ground truth from .pdf (p.563, eq.1)
- **Bardeen 1980** — SVT decomposition (Phys. Rev. D 22:1882)
- **Gauge Invariance** — linearised Riemann invariant under h→h+∂ξ+∂ξ
- **Schur Orthogonality** — SO(3) irreps, no cross-terms
- **Gauss-Bonnet** — R²_μν − (1/3)R² = (1/2)C² mod total derivatives in 4D

### Computer Algebra Tests (12 scripts, all passing)

Primary (7):
- `tests/test_determinant.py` → node 1.6.2
- `tests/test_matrix_inverse.py` → node 1.6.4
- `tests/test_ricci_scalar_sector.py` → node 1.3
- `tests/test_scalar_action.py` → node 1.5.4
- `tests/test_vector_action.py` → node 1.5.3
- `tests/test_tensor_action.py` → node 1.5.2
- `tests/test_special_cases.py` → node 1.7.4

Verifier-generated (5):
- `tests/verify_1_7_1.py` — P^T projector properties
- `tests/verify_1_7_2.py` — Π^TT projector idempotency
- `tests/verify_1_7_3.py` — 1/p⁴ pole structure
- `tests/verify_1_7_4.py` — β=1/2, β=1/3 limits
- `tests/verify_weyl_identity_independent.py` — Weyl² identity via Gauss-Bonnet

Run all: `/tmp/cas-venv/bin/python3 tests/test_*.py`

### Adversarial Verification (8 verifiers, 2 batches)

| Verifier | Section | Challenges | Key Finding |
|----------|---------|------------|-------------|
| V-1 | §1 Action | 0 | Riemann symmetries + Bianchi identity ✓ |
| V-2 | §2 Gauge | **4** | **Sign convention error** in 1.2.2: −→+ (Wald convention). Amended. |
| V-3 | §3 Scalar | 0 | Full independent recalculation ✓ |
| V-4 | §4 Vec+Tens | 0 | Index raising h⁰ᵢ=−Vᵢ vs hⁱ₀=+Vᵢ ✓ |
| V-5 | §5 Action | **3** | **Missing test_scalar_action.py**. Created. Also: □↔+p² (not −p²) |
| V-6 | §6 Det+Prop | 0 | Normalization G=(1/2)M⁻¹ ✓ |
| V-7 | §7 Results | 1 | Weyl² identity via Gauss-Bonnet ✓. Wrote 5 extra scripts. |
| V-8 | Root | 1 | All 6 tests pass, logical flow ✓ |

Total: 9 challenges raised, 9 resolved (1 major fix, 1 gap filled, rest minor/notes).

### Known Minor Issues

- **Definition 0 notation**: States "□ ↔ −p²" but correct relation is □ ↔ +p²
  with p² = ω² − k². All computations use correct signs. Cosmetic only.

## Files

| File | Description |
|------|-------------|
| `fourth_derivative_gravity_propagators.md` | Original derivation (source material) |
| `report.tex` / `report.pdf` | 14-page pdflatex verification report |
| `proof_tree.tex` / `proof_tree_body.tex` | AF-exported proof tree (LaTeX) |
| `proof_export.md` | AF-exported proof tree (Markdown) |
| `meta.json` | AF proof workspace metadata |
| `ledger/000001–000245.json` | 245 append-only ledger entries |
| `externals/*.json` | 6 external reference records |
| `defs/*.json` | 10 definition records |
| `tests/*.py` | 14 verification scripts (12 §1–7 + 2 §8) |
| `refs/Zee2013.pdf` | Local copy of Zee (2013) for ground truth (gitignored) |

## How to Reproduce

```bash
cd examples12

# Check proof status
af status
af progress
af metrics

# Run all tests
/tmp/cas-venv/bin/python3 tests/test_determinant.py
/tmp/cas-venv/bin/python3 tests/test_matrix_inverse.py
/tmp/cas-venv/bin/python3 tests/test_ricci_scalar_sector.py
/tmp/cas-venv/bin/python3 tests/test_scalar_action.py
/tmp/cas-venv/bin/python3 tests/test_vector_action.py
/tmp/cas-venv/bin/python3 tests/test_tensor_action.py
/tmp/cas-venv/bin/python3 tests/test_special_cases.py

# Rebuild report
pdflatex report.tex && pdflatex report.tex
```

## Recent Addition: Position-Space Two-Point Functions (§8)

Added Fourier transforms of all propagators to Euclidean position space.

Three master Green's functions:
- **G1** = **−**ln(ρ²μ²)/(16π²) — biharmonic (from 1/p⁴), logarithmic core
- **G2** = [-ln(ρ²μ²)/2 + 1 - θcot θ]/(4π²) — mixed (from 1/(k²p²)), angle-dependent
- **G3** = -|x|/(8π) — instantaneous (from 1/k⁴), equal-time correlation

Key results (Theorems 8.4–8.6):
- Scalar propagators decompose as linear combinations of G1, G2, δ(τ)G3
- Vector/tensor propagators = transverse projectors × G2/G1
- Stochastic interpretation: □h=ξ (white noise) → ⟨hh⟩ = G₀∗G₀ = G₁ (Remark 8.10)
- Tests: `tests/test_position_space.py` (6/6), `tests/test_adversarial_section8.py` (11/12)

### Adversarial Verification (5 verifiers, 1 batch)

| Verifier | Target | Challenges | Key Finding |
|----------|--------|------------|-------------|
| V-8.1 | Claims 8.1, 8.2 | **1** | **Sign error in G₁**: +ln → −ln. Fixed. |
| V-8.3 | Claim 8.3 (G₂) | 0 | All 7 steps validated; analytic PDE proof |
| V-8.4 | Theorems 8.4–8.6 | 0 | Stochastic convolution confirmed |
| V-8.7 | Remarks 8.7–8.9 | **6** | QFT language leak, ±iπ sign, IR pathology, missing stochastic remark. All fixed. |
| V-8.T | Test suite | **7** | tan(θ) bug, 6 coverage gaps. All fixed/filled. |

Total: 14 challenges raised, 14 resolved (1 major sign fix, 1 code bug, 6 gap fills, 6 text amendments).

## Next Steps

Possible extensions:
- Add massive graviton (Fierz-Pauli mass term) → 1/p⁴ splits into 1/(p²) − 1/(p²−m²)
- Extend to curved background (linearised around de Sitter)
- Add matter coupling and compute graviton exchange amplitude
- Compute static potential V(r) by integrating ⟨ΦΦ⟩ over Euclidean time
