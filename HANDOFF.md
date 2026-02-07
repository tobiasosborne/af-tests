# Handoff: 2026-02-07 (Session 113)

## GOAL: Fill `fundamental_formula` sorry (the #1 priority)

**File**: `AfTests/Jordan/FundamentalFormula.lean:259`
**Statement**: `U (U a b) x = U a (U b (U a x))` for all `a b x : J` in any `JordanAlgebra J`
**Route**: Macdonald's theorem (H-O 2.4.13) lifts `special_fundamental_formula` to all Jordan algebras

## What EXISTS (all sorry-free unless noted)

### Macdonald infrastructure (`AfTests/Jordan/Macdonald/`)

| File | LOC | Sorries | What it does |
|------|-----|---------|-------------|
| FreeAlgebra.lean | 122 | 0 | FreeMagma, FreeNAAlg (ℝ-algebra on binary trees) |
| FreeJordan.lean | 177 | 0 | FreeJordanAlg = FreeNAAlg/JordanCong (2 generators x,y) |
| FreeSpecialJordan.lean | 207 | 0 | `evalAssoc : A → A → FreeJordanAlg → A` (eval into assoc algebras) |
| UBilinear.lean | 113 | 0 | `U_bilinear` linear map, simp lemmas |
| OperatorId.lean | 181 | 0 | Operator identities (2.47)-(2.49) |
| GeneratorLemma.lean | 102 | 0 | Lemma 2.4.23: U_{a,b} generation |
| Monomial.lean | 164 | 0 | M_word, M_eval, induction principles |
| MonoBlock.lean | 238 | 0 | FreeAssocMono type, weight, prependX/Y, **toFA** |
| FJOperators.lean | 105 | 0 | FreeJordanAlg.pow, T, U, U_bilinear on FJ |
| SpecialFF.lean | 100 | 0 | **`special_fundamental_formula`**: FF in all assoc algebras |
| MonomialFJ.lean | 131 | 0 | M_{p,q} as FreeJordanAlg elements |
| MOperator.lean | 213 | 0 | `M_op` recursive definition, termination fully proved |
| MOperatorProperties.lean | 122 | 0 | Properties (ii)-(iv): U factorization, bilinear symmetrization |
| TensorSetup.lean | 179 | 0 | FA, FA3, evalFA, gamma_elem, gamma_mac (correct gamma) |
| GammaInjectivity.lean | ~335 | **0** | full_gamma_tensor, encode_word, z-separator, **ALL PROVED** |
| **Macdonald.lean** | **~206** | **3** | Macdonald theorem + FF corollaries |

### Key theorems already proved

- **`special_fundamental_formula`** (SpecialFF.lean): FF holds in all associative algebras
- **`M_op_one_one`**: M(1,1)(v) = v (property ii)
- **`M_op_xCons_xCons`/`M_op_yCons_yCons`**: Same-letter U property (iii)
- **`M_op_U_bilinear_yCons`/`M_op_U_bilinear_xCons`**: U_bilinear symmetrization (iv)
- **`gamma_mac`**: gamma_mac(p,q) = ½(pzq*+qzp*) in FA3
- **`gamma_mac_comm`**: gamma_mac is symmetric
- **`FA_to_FA3_star`**: FA_to_FA3 commutes with star
- **`gamma_mac_eq_full_on_sym`**: gamma_mac = full_gamma on symmetric tensors
- **`full_gamma_tensor_injective`**: full_gamma_tensor is injective (z-separator argument)
- **`gamma_mac_injective_symTensor`**: gamma_mac injective on symTensor
- **`gamma_mac_injective`**: gamma_mac injectivity in the form used by Macdonald
- **`macdonald_injectivity`**: evalFA injective (sorry-free assuming `macdonald`)
- **`fundamental_formula_free`**: FF in FreeJordanAlg (sorry-free assuming `macdonald`)
- **`FreeAssocMono.toFA`**: conversion from block monomials to FA elements

## What NEEDS to be built (3 remaining sorries in Macdonald/)

### Sorry 1: `mult_alg_surjectivity` (Macdonald.lean:92)

**Goal**: Every T_v is a finite ℝ-linear combination of M_{p,q} operators.
**Statement** (corrected in Session 113):
```lean
theorem mult_alg_surjectivity (v : FreeJordanAlg) :
    ∃ (c : FreeAssocMono × FreeAssocMono →₀ ℝ),
    ∀ w, FreeJordanAlg.T v w = c.sum (fun pq r => r • M_op pq.1 pq.2 w)
```

**Approach**: Induction on v using:
- Properties (ii)-(iv) for closure
- GeneratorLemma for generation
- `FreeAssocMono.toFA` (now defined) for the monomial → FA conversion

**Estimate**: ~100-120 LOC

### Sorry 2: `macdonald` (Macdonald.lean:145)

**Goal**: `∀ v, evalFA v = 0 → v = 0`

**Approach**: Combine surjectivity + property (i) + gamma injectivity.
**Blockers**: Needs `mult_alg_surjectivity` filled + property (i) formalized.

### Sorry 3: `fundamental_formula_general` (Macdonald.lean:206)

**Goal**: FF holds in every JordanAlgebra.

**Three possible approaches**:
1. **Generalize FreeJordanAlg to n generators** (recommended). Then FJ(Fin 3) → J sends x→a, y→b, z→c.
2. **Prove `macdonald`** first, then apply as metatheorem.
3. **Direct algebraic proof** from Jordan axioms (~100 LOC, McCrimmon approach).

## Proof dependency chain

```
[DONE] full_gamma_tensor_injective ──→ gamma_mac_injective ──┐
                                                              ├──→ macdonald ──→ macdonald_injectivity
mult_alg_surjectivity ───────────────────────────────────────┘           │
M_op_eval_z (property (i)) ─────────────────────────────────┘           ↓
                                                              fundamental_formula_free
                                                                     │
                                                                     ↓
                                                          fundamental_formula_general
                                                                     │
                                                                     ↓
                                                    Fill fundamental_formula sorry
```

## CRITICAL TRAP TO AVOID

**DO NOT** try to prove `gamma_jordan_product` with `gamma_elem a = a⊗1+1⊗a`.
It is mathematically **FALSE**. The correct gamma for Macdonald is `gamma_mac` in TensorSetup.lean
which maps into FA3 (3-generator free algebra) using `½(pzq*+qzp*)`.

## Build & sorries

**Build**: `lake build AfTests 2>&1 | tail -40` — PASSES (1915 jobs)
**Sorries in Macdonald/**: 3 total (down from 5 at Session 110)
**Sorries elsewhere**: FundamentalFormula (1), Square (1), Classification (2)

## Recommended next session order

1. **`mult_alg_surjectivity`** — induction proof using properties (ii)-(iv)
2. **Property (i)** — M_{p,q}(z) = gamma_mac(toFA p, toFA q), needs 3-gen evaluation
3. **`macdonald`** — combines 1+2 + gamma injectivity (DONE)
4. **`fundamental_formula_general`** — needs n-gen FreeJordanAlg or direct proof

## Beads issues

- af-i706 (P2): Step 15 — Gamma injectivity (**DONE**, can close)
- af-g2kb (P1): Step 16 — Macdonald theorem (3 sorries)
- af-gzm1 (P1): Step 17 — Fill fundamental_formula
- af-uzj5 (P2, in_progress): Step 14 — Tensor setup (done, can close)
- af-ko7e (P2): FreeAssocMono.toFA (**DONE**, can close)

## Reference — READ BEFORE STARTING

**MANDATORY READING** (do NOT re-research these topics):
- **`memory/macdonald-proof-structure.md`** — Full mathematical proof structure
- **`memory/macdonald-steps14-17.md`** — Mathlib API reference
- **`memory/full-gamma-tensor-injective-code.md`** — (historical, now implemented)

Book: `examples3/Jordan Operator Algebras/joa-m/joa-m.md`
- Macdonald's theorem: 2.4.13 (line ~1063)
- M_{p,q} construction: 2.4.24 (line ~1215)
- Proof of Macdonald: 2.4.25 (line ~1379)

## File map

```
AfTests/Jordan/
├── Basic.lean              -- JordanAlgebra class
├── FundamentalFormula.lean -- fundamental_formula (sorry at line 259) ← FILL THIS
├── Quadratic.lean          -- U operator definition and properties
├── LinearizedJordan.lean   -- Linearized identities, power associativity
├── OperatorIdentities.lean -- Commutator identities
├── FormallyReal/Square.lean -- isPositiveSqrt_unique (sorry, unrelated)
├── Classification/         -- isSimple sorries (unrelated)
└── Macdonald/
    ├── UBilinear.lean      -- U_{a,b} linear map
    ├── OperatorId.lean     -- (2.47)-(2.49)
    ├── GeneratorLemma.lean -- Lemma 2.4.23
    ├── FreeAlgebra.lean    -- FreeMagma, FreeNAAlg
    ├── FreeJordan.lean     -- FreeJordanAlg (2 generators)
    ├── FreeSpecialJordan.lean -- evalAssoc
    ├── SpecialFF.lean      -- special_fundamental_formula (PROVED)
    ├── Monomial.lean       -- M_word, M_eval
    ├── MonoBlock.lean      -- FreeAssocMono, toFA (0 sorries!)
    ├── FJOperators.lean    -- T, U, U_bilinear on FreeJordanAlg
    ├── MonomialFJ.lean     -- M_{p,q} as FJ elements
    ├── MOperator.lean      -- M_op recursive definition (0 sorries!)
    ├── MOperatorProperties.lean -- Properties (ii)-(iv) (0 sorries!)
    ├── TensorSetup.lean    -- FA, FA3, evalFA, gamma_mac (0 sorries!)
    ├── GammaInjectivity.lean -- Step 15: gamma injectivity (0 sorries!)
    └── Macdonald.lean      -- Step 16+17: Macdonald theorem + FF (3 sorries)
```

---

## Previous Sessions

### Session 113: Fill gamma injectivity + toFA + fix surjectivity (3 parallel agents)
- **Agent 1 (full_gamma_tensor_injective)**: **FILLED** all 3 sorries in GammaInjectivity.lean.
  Added ~200 LOC: `encode_word`, `encode_word_injective` (z-separator argument via
  `list_split_at_unique_sep`), `basisFreeMonoid_mul/of/one`, `star_basisFreeMonoid`,
  `FA_to_FA3_basisFreeMonoid`, `full_gamma_tensor_on_basis`, `injective_of_basis_image_linIndep`,
  and the main `full_gamma_tensor_injective`. File is now **100% sorry-free**.
- **Agent 2 (FreeAssocMono.toFA)**: **DEFINED** `toFA : FreeAssocMono → FA` (23 LOC in
  MonoBlock.lean). Added simp lemmas + prepend interaction lemmas. Build passes.
- **Agent 3 (mult_alg_surjectivity)**: **FIXED** mathematically false statement. Now uses
  `Finsupp` for finite ℝ-linear combinations of M_{p,q}. Updated docstrings. Build passes.
- **Net result**: 1 sorry filled (full_gamma_tensor_injective), 1 definition added (toFA),
  1 statement corrected (mult_alg_surjectivity). Macdonald/ now has 3 sorries (down from 4).

### Session 112: Fill gamma_mac_injective + investigation (3 parallel agents)
- **Agent 1 (full_gamma_tensor_injective)**: Validated proof structure — main theorem
  compiles with sorry'd helpers (`encode_word_injective`, `full_gamma_tensor_on_basis`).
  Proved `basisFreeMonoid_mul` and `injective_of_basis_image_linIndep`. Did NOT modify
  GammaInjectivity.lean (worked in scratch). Remaining: fill 2 helpers (~40 LOC total).
- **Agent 2 (gamma_mac_injective)**: **FILLED** the sorry (17 LOC). Derives from
  `gamma_mac_injective_symTensor` by showing `a⊗b + b⊗a ∈ symTensor`, then
  `gamma_mac_tensor(t) = 0`, then injectivity. Build passes, zero warnings.
- **Agent 3 (mult_alg_surjectivity)**: **Found current statement is FALSE**. Proposed
  correct `Submodule.span`-based reformulation. Identified 6 sub-tasks totaling ~260-300 LOC.
  Created beads issues: af-ko7e, af-inuv, af-0cc6, af-efkr, af-opkm.
- **Net result**: 1 sorry filled (gamma_mac_injective), now 4 sorries remain (was 5).

### Session 111: Macdonald sorry investigation (3 parallel agents)
### Session 110: Steps 15+16+17 scaffolding
### Session 109: Step 14 corrections
### Session 108: Steps 11+12 (M_op definition)
### Session 106: Steps 7+10 (SpecialFF + MonomialFJ)
### Session 105: Steps 6+9 (FreeSpecialJordan + GeneratorLemma)
### Session 104: Steps 3+5 (OperatorId + FreeJordan)
### Session 102: Steps 1+4+8 (UBilinear + FreeAlgebra + Monomial)
