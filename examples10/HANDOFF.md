# HANDOFF — (Fib ⊠ Fib) ⋊ S₂ Verification

## Paper
**arXiv:2602.06117** — "On the (Fib ⊠ Fib) ⋊ S₂ fusion category"
by Ferragatta & van Rees. Unpacked in `./paper/`.

## Objective
Adversarial verification of ALL mathematical claims using the `af` framework,
with independent numerical cross-checks via `~/Projects/TensorCategories.jl`.

## Current State (37 nodes, 20 validated, 17 pending)

### Completed & Validated
- **Node 1.1 (Fib foundations)**: All 4 leaf nodes VALIDATED.
  - 1.1.1: Fusion rule τ×τ = 1+τ ✓
  - 1.1.2: Quantum dimensions d(τ) = ξ = (1+√5)/2 ✓
  - 1.1.3: F-symbols (eq 2.6) ✓
  - 1.1.4: Total dimension D_Fib ✓
- **Node 1.2 (Tube algebra)**: VALIDATED ✓
- **Node 1.3 (Lasso maps)**: All 5 children VALIDATED ✓
  - 1.3.1 (eq 2.19), 1.3.2 (eq 2.20), 1.3.3, 1.3.4 (spectral iso), 1.3.5 (reflection pos)
- **Node 1.4 (Modular matrices)**: VALIDATED ✓
- **Node 1.5 (Category structure)**: VALIDATED ✓
- **Nodes 1.6-1.11 (Twisted Hilbert spaces)**: All VALIDATED ✓
  - 1.6 (H_{c₁} irreps), 1.7 (c₂), 1.8 (c₃), 1.9 (c₄), 1.10 (c₇), 1.11 (c₈)
- **Node 1.12 (Further lassos)**: VALIDATED ✓
- **Node 1.13 (Drinfeld center)**: VALIDATED ✓
- **Node 1.14 (22×22 S matrix)**: VALIDATED ✓
- **Node 1.15 (T matrix)**: VALIDATED ✓

### TensorCategories.jl Cross-Check (Node 1.16) — COMPLETED
- **F-symbols computed**: 1800 nonzero entries for (Fib ⊠ Fib) ⋊ S₂
  - Rank 8, FPdim² ≈ 26.18, base ring QQ(ϕ)
  - Written to `fsymbols_fib2s2.txt`
  - Script: `compute_fsymbols.jl`
- **Verification status**: F-symbols match independent derivation via G-crossed formula
  `ass[(i,g),(j,h),(k,l),(m,ghl)] = base.ass[i, T_g(j), T_{gh}(k), m]`
  (0 differences across all 4096 blocks)
- **Known library bugs**:
  - `pentagon_axiom()` fails due to TensorCategories.jl bug in `associator()` for
    non-simple SixJObjects (summand ordering in block reassembly). F-symbols are correct.
  - Drinfeld center crashes with `DomainError: Can not invert non-square Matrix`
    in `induction_adjunction` (0×1 matrix inversion attempt)
- **Component checks PASS**: base Fib⊠Fib pentagon ✓, both monoidal functor axioms ✓

### Not yet refined
- **1.16**: TensorCategories.jl numerical cross-check — computation done, formal node pending

## Key Files
- `paper/fib2s2.tex` — The full paper source (3200+ lines)
- `verify_fib2s2.jl` — Julia script for numerical verification (needs TensorCategories.jl)
- `.af/` — Proof ledger (do NOT edit manually; use `af` commands)

## TensorCategories.jl Status
- Located at `~/Projects/TensorCategories.jl` — **WORKING** (Oscar + Julia 1.12.5)
- Run: `julia --project=../../TensorCategories.jl compute_fsymbols.jl`
- Key functions used:
  - `fibonacci_category()` → Fib (rank 2, 15 F-symbols)
  - `Fib ⊠ Fib` → Deligne product (rank 4, 225 F-symbols)
  - `gcrossed_product(FibFib, action)` → (Fib ⊠ Fib) ⋊ S₂ (rank 8, 1800 F-symbols)
  - `pentagon_axiom(simples)` — **BUGGY** for G-crossed products (see above)
  - `center(C)` — **CRASHES** on this category (matrix inversion bug)

## Paper Structure (key equation references)
- **Fib F-symbols**: eq 2.6 (line 128)
- **Tube algebra (general)**: eq 2.8 (line 172)
- **Tube algebra (Fib twisted)**: eqs 2.10-2.12 (lines 224-230)
- **Fib projectors**: eqs 2.7, 2.13 (lines 198, 245)
- **Lasso compositions**: eqs 2.19-2.20 (lines 284-288)
- **Fib S matrix**: eq 2.37 (line 655)
- **Semidirect product fusion**: eq 3.3 (line 1106)
- **Semidirect product F-symbols**: eq 3.22 (line 1860)
- **8 simple objects**: lines 1869-1872
- **Untwisted irreps + projectors**: eq 4.5 (line 2051)
- **c₂ projectors**: line 2150
- **c₃ projectors**: eq 4.11 (line 2316)
- **c₄ projectors**: line 2497
- **c₇ projectors**: eq 4.21 (line 2584), decomposition eq 4.22 (line 2590)
- **c₈ projectors**: eq 4.27 (line 2657)
- **Drinfeld center table**: line 2849
- **22 partition functions**: eq 5.1 (line 2879)
- **Spin values**: eq 5.2 (line 2884)
- **22×22 S matrix**: lines 2893-2967 (two halves, "cut and glue")

## Workflow Rules
1. **VERIFIERS must be fresh subagents** — one job each, strict mathematical rigor
2. **Max 1-2 subagents in parallel**
3. **Errors/gaps are HIGH VALUE** — finding problems is success
4. Use `af claim/refine/release` for prover, `af claim/accept or challenge/release` for verifier
5. All commands must run from `./examples10/` directory

## Next Steps (priority order)
1. **Formalize node 1.16** — attach TensorCategories.jl F-symbol output as numerical evidence
   to the proof tree via `af attach`
2. **Attach numerical evidence** to other validated nodes where applicable
3. **Address remaining unrefined leaf nodes** if any exist
4. **Report TensorCategories.jl bugs** upstream:
   - Pentagon axiom `associator()` ordering for non-simple SixJObjects
   - Drinfeld center `induction_adjunction` 0×N matrix inversion

## Dimension Counting (from paper analysis)
| Hilbert space | # networks | Irreps | Check |
|---|---|---|---|
| H_{c₁} | 8 | 4×1² + 1×2² = 8 | ✓ |
| H_{c₂} | 4 | 4×1² = 4 | ✓ |
| H_{c₃} | 7 | 7×1² = 7 | ✓ |
| H_{c₄} | 6 | 6×1² = 6 | ✓ |
| H_{c₅} | 7 | same as c₃ | ✓ |
| H_{c₆} | 6 | same as c₄ | ✓ |
| H_{c₇} | 18 | 6×1² + 3×2² = 18 | ✓ |
| H_{c₈} | 14 | 6×1² + 2×2² = 14 | ✓ |
| **Total** | | 52 irreps → 22 independent | ✓ |
