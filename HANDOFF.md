# Handoff: 2026-02-07 (Session 114)

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
- **`full_gamma_tensor_injective`**: full_gamma_tensor is injective (z-separator argument)
- **`gamma_mac_injective_symTensor`**: gamma_mac injective on symTensor
- **`gamma_mac_injective`**: gamma_mac injectivity in the form used by Macdonald
- **`macdonald_injectivity`**: evalFA injective (sorry-free assuming `macdonald`)
- **`fundamental_formula_free`**: FF in FreeJordanAlg (sorry-free assuming `macdonald`)
- **`FreeAssocMono.toFA`**: conversion from block monomials to FA elements

## What NEEDS to be built (3 remaining sorries in Macdonald/)

### Sorry 1: `mult_alg_surjectivity` (Macdonald.lean:92)

**Goal**: Every T_v is a finite ℝ-linear combination of M_{p,q} operators.

**STRATEGY (Session 114, corrected after reading H-O)**: Follow H-O exactly.
The book proves equation (2.58): `T_{x^k} M_{p,q} = ½(M_{x^k p, q} + M_{p, x^k q})`
by dedicated induction on weight. This is the KEY missing piece.
- Book ref: `joa-m.md` lines 1326-1377 (proof of 2.58)
- Book ref: `joa-m.md` lines 1379-1389 (proof of 2.4.25)
- (2.58) base cases use operator identities (2.47)/(2.49) from OperatorId.lean
- (2.58) inductive cases use M_op recurrence + properties (iii)/(iv)
- Then: E is left ideal of mult algebra containing Id → E = everything
- See `memory/mult-alg-surjectivity-analysis.md` for full strategy
- Estimated: ~150-170 LOC total (2.58 lemma + surjectivity proof)

### Sorry 2: `macdonald` (Macdonald.lean:145)

**Goal**: `∀ v, evalFA v = 0 → v = 0`
**Blockers**: Needs `mult_alg_surjectivity` + property (i) formalized.

### Sorry 3: `fundamental_formula_general` (Macdonald.lean:206)

**Goal**: FF holds in every JordanAlgebra.

**Three approaches** (analyzed Session 114):
1. **Generalize FreeJordanAlg to n generators** (cleanest, ~500 LOC refactoring)
2. **Prove `macdonald`** first, then apply as metatheorem (needs Sorry 1+2)
3. **Direct algebraic proof** from Jordan axioms (very heavy, ~200+ LOC)

**KEY FINDING (Session 114)**: The subalgebra argument ⟨a,b⟩ doesn't work because
FF needs to hold for ALL x ∈ J, not just x ∈ ⟨a,b⟩. The operator F(a,b) = U_{U_a(b)} - U_a U_b U_a
vanishes on ⟨a,b⟩ but we can't conclude it vanishes on all of J.
FF special cases (b=a, b=1) follow from U_jpow. General b needs Macdonald or 3-gen.

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
It is mathematically **FALSE**. The correct gamma for Macdonald is `gamma_mac` in TensorSetup.lean.

## Build & sorries

**Build**: `lake build AfTests 2>&1 | tail -40` — PASSES
**Sorries in Macdonald/**: 3 total (mult_alg_surjectivity, macdonald, fundamental_formula_general)
**Sorries elsewhere**: FundamentalFormula (1), Square (1), Classification (2)

## Recommended next session order (following H-O exactly)

1. **Prove equation (2.58)** as a Lean lemma: `T_{x^k} M_{p,q} = ½(M_{x^k p,q} + M_{p,x^k q})`
   By induction on weight(p,q). Uses (2.47)/(2.49) from OperatorId.lean.
   Book ref: joa-m.md lines 1326-1377. Estimated ~80-100 LOC.

2. **Fill `mult_alg_surjectivity`** using (2.58) + properties (iii)/(iv).
   E = span{M_{p,q}} is left ideal containing Id → E = full mult algebra.
   Book ref: joa-m.md lines 1379-1383. Estimated ~50-70 LOC.

3. **Fill `macdonald`** using surjectivity + property (i) + gamma injectivity.

4. **Fill `fundamental_formula_general`** — needs 3-gen FreeJordanAlg (parameterize)
   or use direct approach. The subalgebra ⟨a,b⟩ argument does NOT work
   (FF needs all x ∈ J, not just x ∈ ⟨a,b⟩).

## Beads issues

- af-g2kb (P1): Step 16 — Macdonald theorem (3 sorries)
- af-inuv (P1): Restate mult_alg_surjectivity using Submodule.span (DONE, can close)
- af-efkr (P1): FJ{x,y,z} infrastructure (3-gen FreeJordanAlg)
- af-gzm1 (P1): Step 17 — Fill fundamental_formula

## Reference — READ BEFORE STARTING

**MANDATORY READING** (do NOT re-research these topics):
- **`memory/macdonald-proof-structure.md`** — Full mathematical proof structure
- **`memory/macdonald-steps14-17.md`** — Mathlib API reference
- **`memory/mult-alg-surjectivity-analysis.md`** — Detailed analysis of surjectivity proof (Session 114)

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

### Session 114: Analysis of mult_alg_surjectivity + learnings
- **No code changes** — pure analysis session
- **Key finding**: mult_alg_surjectivity proof is harder than estimated.
  Product case T_{u∘v} needs M operator compositions to close.
  T_x = U_{x,1} not directly covered by properties (iii)/(iv).
- **Key finding**: fundamental_formula_general cannot use subalgebra argument
  (⟨a,b⟩ only gives FF for x ∈ ⟨a,b⟩, not all x ∈ J).
- **Computed**: T_{x∘y}=½M_{xy,1}+½M_{yx,1}, T_x∘T_y=½M_{xy,1}+½M_{x,y}
- **Closed beads**: af-i706, af-uzj5, af-ko7e (all completed in Session 113)
- **Wrote**: `memory/mult-alg-surjectivity-analysis.md` (detailed analysis)
- **Recommendation**: Parameterize FreeJordanAlg by generator type (fastest path to FF)

### Session 113: Fill gamma injectivity + toFA + fix surjectivity (3 parallel agents)
- **Agent 1 (full_gamma_tensor_injective)**: **FILLED** all 3 sorries in GammaInjectivity.lean.
- **Agent 2 (FreeAssocMono.toFA)**: **DEFINED** `toFA : FreeAssocMono → FA` (23 LOC).
- **Agent 3 (mult_alg_surjectivity)**: **FIXED** mathematically false statement.
- **Net result**: 1 sorry filled, 1 definition added, 1 statement corrected. 3 sorries remain.

### Session 112: Fill gamma_mac_injective + investigation (3 parallel agents)
### Session 111: Macdonald sorry investigation (3 parallel agents)
### Session 110: Steps 15+16+17 scaffolding
### Session 109: Step 14 corrections
### Session 108: Steps 11+12 (M_op definition)
### Session 106: Steps 7+10 (SpecialFF + MonomialFJ)
### Session 105: Steps 6+9 (FreeSpecialJordan + GeneratorLemma)
### Session 104: Steps 3+5 (OperatorId + FreeJordan)
### Session 102: Steps 1+4+8 (UBilinear + FreeAlgebra + Monomial)
