# HANDOFF — (Fib ⊠ Fib) ⋊ S₂ Verification

## Paper
**arXiv:2602.06117** — "On the (Fib ⊠ Fib) ⋊ S₂ fusion category"
by Ferragatta & van Rees. Unpacked in `./paper/`.

## Objective
Adversarial verification of ALL mathematical claims using the `af` framework,
with independent numerical cross-checks via `~/Projects/TensorCategories.jl`.

## Current State (37 nodes, 4 validated, 33 pending)

### Completed
- **Node 1.1 (Fib foundations)**: All 4 leaf nodes VALIDATED by independent verifier.
  - 1.1.1: Fusion rule τ×τ = 1+τ ✓
  - 1.1.2: Quantum dimensions d(τ) = ξ = (1+√5)/2 ✓
  - 1.1.3: F-symbols (eq 2.6) ✓
  - 1.1.4: Total dimension D_Fib ✓

### Refined (awaiting verification)
- **Node 1.2 (Tube algebra of Fib)**: 7 child nodes covering eqs 2.10-2.12
  derivation from general formula, eigenvalue verification, projectors (eqs 2.7, 2.13).
- **Node 1.3 (Lasso maps of Fib)**: 5 child nodes covering eqs 2.19-2.20
  composition, kernel/cokernel analysis, reflection positivity.
- **Node 1.4 (Fib modular matrices)**: 4 child nodes covering 4×4 S matrix (eq 2.37),
  T matrix, S²=C, (ST)³=C.

### Not yet refined (leaf-level sections 1.5-1.16)
- **1.5**: (Fib⊠Fib)⋊S₂ structure — 8 simple objects, fusion rules, F-symbols
- **1.6**: Untwisted Hilbert space H_{c₁} — 5 irreps, projectors (eq 4.5)
- **1.7**: Twisted c₂ — 4 irreps
- **1.8**: Twisted c₃ — 7 irreps (5 from Fib⊗Fib + 2 from S₂ mixing)
- **1.9**: Twisted c₄ — 6 irreps
- **1.10**: Twisted c₇ — 9 irreps (6 one-dim + 3 two-dim), 18 networks
- **1.11**: Twisted c₈ — 8 irreps (6 one-dim + 2 two-dim), 14 networks
- **1.12**: Further lassos (inter-Hilbert-space maps)
- **1.13**: Drinfeld center — 22 simple objects
- **1.14**: 22×22 modular S matrix (the headline result)
- **1.15**: T matrix (22 spin values)
- **1.16**: TensorCategories.jl numerical cross-check

## Key Files
- `paper/fib2s2.tex` — The full paper source (3200+ lines)
- `verify_fib2s2.jl` — Julia script for numerical verification (needs TensorCategories.jl)
- `.af/` — Proof ledger (do NOT edit manually; use `af` commands)

## TensorCategories.jl Status
- Located at `~/Projects/TensorCategories.jl`
- **NEEDS `Pkg.instantiate()`** — Oscar dependency not installed. The install
  timed out (Julia + Oscar is very slow to install). Run:
  ```
  cd ~/Projects/TensorCategories.jl
  julia --project=. -e 'using Pkg; Pkg.instantiate()'
  ```
  This may take 10-30 minutes. Once done, key functions:
  - `fibonacci_category()` — constructs Fib
  - `C ⊠ D` — Deligne product
  - `C ⋊ G` — semidirect product with group
  - `smatrix(C)`, `tmatrix(C)` — modular data
  - `center(C)` — Drinfeld center
  - `pentagon_axiom(C)` — verify pentagon

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
1. **Send verifiers** for nodes 1.2, 1.3, 1.4 (already refined, awaiting verification)
2. **Refine node 1.5** — category structure (straightforward from Fib foundations)
3. **Refine nodes 1.6-1.11** — these are the bulk computational work (tube algebra
   for each twisted Hilbert space). The paper's explicit eigenvalue tables and
   projector formulas need to be verified by substitution into the general tube
   algebra formula.
4. **Refine 1.12-1.13** — lasso maps and Drinfeld center
5. **Refine 1.14-1.15** — the 22×22 S and T matrices (headline result)
6. **Complete 1.16** — get TensorCategories.jl working and run independent computation
7. **Attach numerical evidence** via `af attach` to validated nodes

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
