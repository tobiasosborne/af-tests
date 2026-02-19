# HANDOFF — (Fib ⊠ Fib) ⋊ S₂ Verification

## Paper
**arXiv:2602.06117** — "On the (Fib ⊠ Fib) ⋊ S₂ fusion category"
by Ferragatta & van Rees. Unpacked in `./paper/`.

## Objective
Adversarial verification of ALL mathematical claims using the `af` framework,
with independent numerical cross-checks via `~/Projects/TensorCategories.jl`.

## Current State: 78% complete (29/37 validated, 8 pending, 44 open challenges)

### Validated Nodes (29)
- **1.1** (Fib foundations) + all 4 children ✓
- **1.2** (Tube algebra) + all 7 children ✓
- **1.3.1–1.3.5** (Lasso map children, all 5 validated) ✓
- **1.4** (Modular matrices) + all 4 children ✓
- **1.6** (H_{c₁} irreps), **1.7** (c₂), **1.10** (c₇), **1.11** (c₈) ✓
- **1.13** (Drinfeld center), **1.15** (T matrix) ✓

### Pending Nodes with BLOCKING Challenges (need PROVER action)

| Node | Blocking Challenge | Action Required |
|------|-------------------|-----------------|
| **1.8** (c₃ Hilbert) | 2× critical: statement says "10 networks, 3×1d+2×2d" but paper says **7 networks, 7×1d** | Prover must amend statement to match paper lines 2158, 2316 |
| **1.9** (c₄ Hilbert) | 2× critical: statement says "12 networks, 6×1d+1×2d" but paper says **6 networks, 6×1d** | Prover must amend statement to match paper lines 2342, 2496 |
| **1.5** (Category structure) | 2× major: "eq 3.3" doesn't exist; should cite label `junctionsemidirect` (line 1106) | Prover must fix equation reference |
| **1.3** (Lasso maps parent) | 1× major: "eqs 2.19-2.20" should be "eqs 2.29-2.30" (LaTeX labels `Lasso1tau`/`Lassotau1` at lines 284-286) | Prover must fix equation references in parent + children 1.3.1/1.3.2 |
| **1.12** (Further lassos) | 1× major: "Hilbert space isomorphisms" wrong for c₃↔c₇ (rank-deficient intertwiners, not isos) | Prover must refine statement; also missing c₃↔c₅, c₄↔c₆ |
| **1.14** (22×22 S matrix) | 1× major + 1× minor: S matrix entries correct, S²=I and (ST)³=I verified, but node doesn't acknowledge non-orthonormal basis for Z_{c₇}⁽⁹⁾ (2-dim irrep). Row 22 has factor-2 convention. | Prover should add basis convention note. Rescaling (row/2, col×2) gives symmetric+unitary matrix. |
| **1.16** (TC.jl cross-check) | 1× major: statement overclaims — only 3/7 items independently computed by TC.jl (Fib, Fib⊠Fib, F-symbols). Center crashes → no independent 22×22 S/T. | Prover must refine to distinguish TC.jl-computed vs algebraically-verified items |
| **1** (root) | No blocking challenges; just needs all children resolved | Accept when all children done |

### Priority Actions for Next Session

**HIGHEST PRIORITY — Fix fabricated statements (5 min each):**
1. `af claim 1.8 --owner prover-fix --role prover` → `af refine 1.8 -s "Twisted c_3 Hilbert space: 7 networks, 7 one-dim irreps (7×1²=7), projectors (eq 4.11)."` → resolve challenges
2. `af claim 1.9 --owner prover-fix --role prover` → `af refine 1.9 -s "Twisted c_4 Hilbert space: 6 networks, 6 one-dim irreps (6×1²=6), projectors."` → resolve challenges

**HIGH PRIORITY — Fix equation references (5 min each):**
3. Fix 1.3 equation refs: "eqs 2.19-2.20" → "eqs 2.29-2.30" (also fix children 1.3.1, 1.3.2)
4. Fix 1.5 equation ref: "eq 3.3" → cite `junctionsemidirect` label or correct eq number

**MEDIUM PRIORITY — Refine overclaims (10 min each):**
5. Refine 1.12: replace "isomorphisms" with "intertwiners" for c₃↔c₇, add missing connections
6. Refine 1.14: add note about partition function basis convention for 2-dim irrep Z_{c₇}⁽⁹⁾
7. Refine 1.16: distinguish TC.jl-independent computations from algebraic verifications

**THEN: Accept rollups:**
8. Once 1.3 challenges resolved → `af accept 1.3`
9. Once all children resolved → `af accept 1` (root)

## Key Verifier Findings (This Session)

### Critical: Fabricated Node Statements (1.8, 1.9)
Nodes 1.8 and 1.9 had completely wrong network counts and irrep decompositions.
The HANDOFF dimension table was correct all along — the node statements were wrong.

### S Matrix Asymmetry Explained
The 22×22 S matrix is NOT symmetric in the paper's partition function basis.
Root cause: Z_{c₇}⁽⁹⁾ is a 2-dimensional tube algebra irrep (Drinfeld center table
line 2872: `X = 2c₇`). This creates a factor-4 discrepancy between S[22,j] and S[j,22].
Rescaling row 22 by 1/2 and column 22 by 2 gives a perfectly symmetric, unitary matrix
with quantum dimension 2ξ² for the 22nd object. S²=I and (ST)³=I hold in both bases.

### TC.jl Bug Investigation — Deep Dive (this session)

See `TC_BUGS.md` for prior analysis. This session performed a deep code-level
investigation with 4 parallel subagents reading the full TensorCategories.jl source.

**Bug 1: Pentagon failure (156/4096 checks fail) — ROOT CAUSE PRECISELY IDENTIFIED**

Root cause confirmed by `diag_pentagon.jl` and `diag_pentagon2.jl`:

The `gcrossed_product()` function in `GCrossedFusion.jl` stores 6j symbols with
rows/columns ordered by **base-category intermediate index** (which maps to
monotonically increasing CxG indices). But the CxG `tensor_product()` for morphisms
in `FusionCategory.jl` visits intermediates in **(i,j) iteration order**, where `j`
runs over CxG simple indices. When the G-action permutes base simples (σ=[1,3,2,4]
for the swap), the intermediate CxG indices from the j-iteration are **non-monotonic**.

Concrete example at block 8 of `pentagon(S[2],S[7],S[7],S[7])`:
- `S[2]⊗S[j]` for j∈{1,3,5,7} gives intermediates p∈{2,6,4,8} (NOT monotonic)
- 6j symbol rows are in order p∈{2,4,6,8} (monotonic base ordering)
- Mismatch = P_{23} permutation (swap positions 2,3 ↔ CxG simples 4,6)
- The non-simple `associator(S[2], S[7]⊗S[7], S[7])` correctly produces P_{23}
  at block 8, but `α(S[8],S[7],S[7])` (simple, on RHS) doesn't compensate

**Attempted fixes that DON'T work** (all produce the same P_{23}):
- Rewriting `tensor_product()` for morphisms with direct matrix construction
- Using `inv(recomp_left)` instead of `vertical_direct_sum(projections)`
- Sum-of-terms: `Σ (inclusion ∘ simple_assoc ∘ projection)` per triple
- The P_{23} is intrinsic to the CxG tensor_product ordering, not a code artifact

**Correct fix (not yet implemented):**
Must be in `GCrossedFusion.jl:gcrossed_product()`. After computing the 6j matrix
`a[k]` for each `(i1,j1,i2,j2,i3,j3)` tuple, apply per-block row/column
permutations to convert from base-intermediate ordering to CxG j-iteration ordering.

The row permutation for output block k: collect the base intermediates
`r_j = base_i1 ⊗ T_{g1}(base_j)` for j=1,...,m. The 6j rows are in r-index order
(r=1,...,m). The CxG tensor_product visits them in j-index order, giving r-values
`r_1, r_2, ..., r_m` which may be non-monotonic. The permutation maps from r-order
to the order `(r_1, r_2, ..., r_m)`.

Challenge: each 6j block `a[k]` has dimensions determined by the SUBSET of
intermediates that contribute to output k (often 1×1 in this category), so the
permutation must be computed per-block on the relevant subset, not on all m
base simples.

**Bug 2: Center crash (5 thread-safety race conditions) — ALL 5 FIXED**
- Fix 1: `Centralizer.jl:770` — replaced `mors = [mors; B3]` race with pre-allocated
  `thread_results[idx] = B3` pattern
- Fix 2: `Center.jl:1631` — removed symmetric `S[i,j] = S[j,i]` write-write race;
  now computes `val` first, assigns with `i != j` guard
- Fix 3: `Centralizer.jl:883` — same smatrix fix as Center.jl
- Fix 4: `Center.jl:1136` — added `ReentrantLock` around `add_induction!` Dict mutation
- Fix 5: `Centralizer.jl:662` — same lock fix for Centralizer's `add_induction!`
- **Status**: Applied to local copy of TensorCategories.jl. NOT committed to
  upstream (we are not repo authors). Run `test_fixes.jl` to verify.

**F-symbols ARE correct** (1800 entries, 0 discrepancies with G-crossed formula)

## Julia Debug Scripts
| Script | Purpose | Result |
|--------|---------|--------|
| `debug_center.jl` | Reproduce center crash | Crash in `@threads` at `hom_by_adjunction` |
| `debug_center2.jl` | Unwrap thread error | Single-threaded works; race condition confirmed |
| `debug_pentagon.jl` | Trace pentagon failure | Block 8 rows/cols 2,3 swapped (P_{23} permutation) |
| `debug_ordering.jl` | Trace block ordering | Summand vs tensor-product ordering mismatch |
| `diag_pentagon.jl` | Deep trace of non-simple assoc | Confirms P_{23} from G-permuted intermediates |
| `diag_pentagon2.jl` | Trace each pentagon morphism | Isolates P_{23} to α(X,Y⊗Z,W); replacing with id fixes pentagon |
| `test_pentagon_quick.jl` | Quick pentagon regression test | Shows 156/4096 failures (known) |
| `test_fixes.jl` | Quick test for both fixes | Used for iterating on fix attempts |

## Julia Verification Scripts (from prior session)
| Script | Depends on TC.jl? | Nodes covered | Result |
|--------|-------------------|---------------|--------|
| `verify_fib_foundations.jl` | YES | 1.1.1–1.1.4 | ALL PASS |
| `verify_tube_algebra.jl` | NO (LinearAlgebra) | 1.2.2–1.2.7 | ALL PASS |
| `verify_modular_fib.jl` | NO (LinearAlgebra) | 1.4.1–1.4.4 | ALL PASS |
| `verify_modular_22x22.jl` | NO (LinearAlgebra) | 1.14, 1.15 | S²=I (8.7e-16), (ST)³=I (1.8e-15) |

## Key Files
- `paper/fib2s2.tex` — The full paper source (3200+ lines)
- `TC_BUGS.md` — Full technical analysis of TensorCategories.jl bugs
- `debug_*.jl` — 4 debug scripts for TC.jl bugs (prior session)
- `diag_pentagon.jl`, `diag_pentagon2.jl` — Deep pentagon diagnostics (this session)
- `test_pentagon_quick.jl` — Pentagon regression test (this session)
- `test_fixes.jl` — Quick test harness for fix attempts
- `verify_*.jl` — 4 Julia verification scripts (prior session)
- `compute_fsymbols.jl` — TC.jl F-symbol computation (prior session)
- `fsymbols_fib2s2.txt` — 1800 computed F-symbols
- `verify_fib2s2.jl` — Original verification script (partially uses TC.jl)

## Dimension Counting (from paper — verified correct)
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

## Workflow Rules
1. **VERIFIERS must be fresh subagents** — one job each, strict mathematical rigor
2. **Errors/gaps are HIGH VALUE** — finding problems is success
3. Use `af claim/refine/release` for prover, `af claim/accept or challenge/release` for verifier
4. All commands must run from `./examples10/` directory
5. **Read paper FIRST** before reasoning: `paper/fib2s2.tex`
