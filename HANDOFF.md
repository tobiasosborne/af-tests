# Handoff: 2026-02-07 (Session 112)

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
| MonoBlock.lean | 215 | 0 | FreeAssocMono type, weight, prependX/Y |
| FJOperators.lean | 105 | 0 | FreeJordanAlg.pow, T, U, U_bilinear on FJ |
| SpecialFF.lean | 100 | 0 | **`special_fundamental_formula`**: FF in all assoc algebras |
| MonomialFJ.lean | 131 | 0 | M_{p,q} as FreeJordanAlg elements |
| MOperator.lean | 213 | 0 | `M_op` recursive definition, termination fully proved |
| MOperatorProperties.lean | 122 | 0 | Properties (ii)-(iv): U factorization, bilinear symmetrization |
| TensorSetup.lean | 179 | 0 | FA, FA3, evalFA, gamma_elem, gamma_mac (correct gamma) |
| **GammaInjectivity.lean** | **143** | **1** | full_gamma_tensor, gamma_mac_tensor, injectivity on symTensor |
| **Macdonald.lean** | **183** | **3** | Macdonald theorem + FF corollaries (gamma_mac_injective filled) |

### Key theorems already proved

- **`special_fundamental_formula`** (SpecialFF.lean): FF holds in all associative algebras
- **`M_op_one_one`**: M(1,1)(v) = v (property ii)
- **`M_op_xCons_xCons`/`M_op_yCons_yCons`**: Same-letter U property (iii)
- **`M_op_U_bilinear_yCons`/`M_op_U_bilinear_xCons`**: U_bilinear symmetrization (iv)
- **`gamma_mac`**: gamma_mac(p,q) = ½(pzq*+qzp*) in FA3
- **`gamma_mac_comm`**: gamma_mac is symmetric
- **`FA_to_FA3_star`**: FA_to_FA3 commutes with star
- **`gamma_mac_eq_full_on_sym`**: gamma_mac = full_gamma on symmetric tensors
- **`gamma_mac_injective_symTensor`**: gamma_mac injective on symTensor (reduces to full_gamma_tensor_injective)
- **`macdonald_injectivity`**: evalFA injective (sorry-free assuming `macdonald`)
- **`fundamental_formula_free`**: FF in FreeJordanAlg (sorry-free assuming `macdonald`)

## What NEEDS to be built (4 remaining sorries)

### Sorry 1: `full_gamma_tensor_injective` (GammaInjectivity.lean:127)

**Goal**: Prove `Function.Injective full_gamma_tensor`

**Approach (validated Session 112)**: The main proof structure compiles with sorry'd helpers:
1. Define `encode_word : FreeMonoid (Fin 2) × FreeMonoid (Fin 2) → FreeMonoid (Fin 3)` as `map(castSucc)(m₁) ++ [2] ++ reverse(map(castSucc)(m₂))`
2. Prove `encode_word_injective` — z separates left/right parts
3. Prove `full_gamma_tensor_on_basis` — image of tensor basis = FA3 basis via encode_word
4. Use `Basis.linearIndependent.comp` to compose 2+3 into injectivity

**Helper lemmas proved by Agent 1**:
- `basisFreeMonoid_mul` — basis is multiplicative
- `injective_of_basis_image_linIndep` — generic lemma: basis maps to lin.indep → injective

**Remaining sub-tasks for this sorry**:
- `encode_word_injective` (~20 LOC): needs `List.map_injective` + z-separator on lists
- `full_gamma_tensor_on_basis` (~20 LOC): needs `basisFreeMonoid_of` (ι i = basis(of i)), `star_basisFreeMonoid` (star = reverse), `FA_to_FA3_basisFreeMonoid`

**Key API**: `FreeAlgebra.basisFreeMonoid`, `Basis.tensorProduct`, `FreeMonoid.map`, `FreeMonoid.reverse`

### Sorry 2: `mult_alg_surjectivity` (Macdonald.lean:86) — STATEMENT IS WRONG

**CRITICAL**: Current statement `∀ v, ∃ p q, ∀ w, M_op p q w = T v w` is **mathematically false**. A single M_{p,q} can't express every T_v.

**Correct statement**: T_v is in the ℝ-linear span of {M_{p,q}}. Proposed:
```lean
def MSpan : Submodule ℝ (FreeJordanAlg → FreeJordanAlg) :=
  Submodule.span ℝ (Set.range (fun pq : FreeAssocMono × FreeAssocMono => M_op pq.1 pq.2))
theorem mult_alg_surjectivity (v : FreeJordanAlg) : (FreeJordanAlg.T v) ∈ MSpan
```

**Prerequisites** (see beads af-ko7e, af-inuv, af-0cc6):
- `FreeAssocMono.toFA : FreeAssocMono → FA` (~15 LOC)
- Correct statement using Submodule.span (~10 LOC)
- Proof by induction using GeneratorLemma + properties ii-iv (~100-120 LOC)

**Total estimate**: ~260-300 LOC across 4-5 sub-tasks for full `macdonald` proof

### ~~Sorry 3: `gamma_mac_injective`~~ — **FILLED (Session 112)**

**Goal**: gamma_mac injectivity in the form used by the Macdonald proof.
**Approach**: Derive from `gamma_mac_injective_symTensor` in GammaInjectivity.lean.

### Sorry 4: `macdonald` (Macdonald.lean:121)

**Goal**: `∀ v, evalFA v = 0 → v = 0`

**Approach**: Combine property (i) + surjectivity + gamma injectivity. This is the
core theorem. Need to connect M_op to evalFA and gamma_mac.

**Missing piece**: Property (i): M_{p,q}(z) = gamma_mac(toFA(p), toFA(q)). Requires:
- `toFA : FreeAssocMono → FA` (convert monomials to free algebra elements)
- Evaluation of FreeJordanAlg into FA3 (3-generator free algebra)
- Induction on weight using properties (ii)-(iv)

### Sorry 5: `fundamental_formula_general` (Macdonald.lean:179)

**Goal**: FF holds in every JordanAlgebra.

**Blockers investigated (Session 111)**:
- `fundamental_formula_free` proves FF for ALL u,v,w in FJ{x,y}
- `evalAssoc : A → A → FreeJordanAlg → A` evaluates FJ elements into associative algebras
- No `evalJA : FreeJordanAlg → J` (Jordan algebra evaluation) exists yet
- Even with evalJA, the image only reaches ⟨a,b⟩ ⊆ J — does NOT cover arbitrary x ∈ J
- Both `U_{U_a(b)}` and `U_a U_b U_a` are linear in x, but they only agree on ⟨a,b⟩

**Three possible approaches**:
1. **Generalize FreeJordanAlg to n generators** (recommended). Refactor `FreeNAAlg`
   from 2 fixed generators to `Type*`-indexed generators. Then FJ(Fin 3) has 3
   generators, and evalJA sends x→a, y→b, z→c covering all of J.
2. **Prove `macdonald`** first (Sorries 1-4), then apply Macdonald's theorem as a
   metatheorem about operator identities in 2 variables linear in a 3rd.
3. **Direct algebraic proof** from Jordan axioms (~100 LOC, McCrimmon approach).

**For formalization**: Need either (a) FreeJordanAlg on 3+ generators and its universal
property, or (b) `macdonald` sorry filled first, or (c) direct proof from axioms.

## Proof dependency chain

```
full_gamma_tensor_injective ──→ gamma_mac_injective ──┐
                                                       ├──→ macdonald ──→ macdonald_injectivity
mult_alg_surjectivity ────────────────────────────────┘           │
M_op_eval_z (property (i)) ───────────────────────────┘           ↓
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

**Build**: `lake build AfTests 2>&1 | tail -40` — PASSES
**Sorries in Macdonald/**: 4 total (see above)
**Sorries elsewhere**: FundamentalFormula (1), Square (1), Classification (2)

## Recommended next session order

1. **`full_gamma_tensor_injective`** — purely linear algebra, self-contained
2. **`mult_alg_surjectivity`** — needs careful statement refinement
3. **Property (i)** — needs `toFA : FreeAssocMono → FA` and 3-gen evaluation
4. **`macdonald`** — combines 1+2+3
5. **`fundamental_formula_general`** — needs universal property of FreeJordanAlg

## Beads issues

- af-i706 (P2): Step 15 — Gamma injectivity (1 sorry left: full_gamma_tensor_injective)
- af-g2kb (P1): Step 16 — Macdonald theorem (4 sorries)
- af-gzm1 (P1): Step 17 — Fill fundamental_formula
- af-uzj5 (P2, in_progress): Step 14 — Tensor setup (done, can close)

## Reference — READ BEFORE STARTING

**MANDATORY READING** (do NOT re-research these topics):
- **`memory/macdonald-proof-structure.md`** — Full mathematical proof structure: exact theorem statement, property (i) induction, surjectivity argument, z-separator argument, how FF follows. Contains everything needed to write the proofs.
- **`memory/macdonald-steps14-17.md`** — Mathlib API reference: FreeAlgebra, TensorProduct, Basis, LinearIndependent, StarRing. Contains exact function names and signatures.

Book: `examples3/Jordan Operator Algebras/joa-m/joa-m.md`
- Macdonald's theorem: 2.4.13 (line ~1063)
- M_{p,q} construction: 2.4.24 (line ~1215)
- Proof of Macdonald: 2.4.25 (line ~1379)
- Star involution: 2.3.5 (line ~859)

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
    ├── MonoBlock.lean      -- FreeAssocMono (alternating block monomials)
    ├── FJOperators.lean    -- T, U, U_bilinear on FreeJordanAlg
    ├── MonomialFJ.lean     -- M_{p,q} as FJ elements
    ├── MOperator.lean      -- M_op recursive definition (0 sorries!)
    ├── MOperatorProperties.lean -- Properties (ii)-(iv) (0 sorries!)
    ├── TensorSetup.lean    -- FA, FA3, evalFA, gamma_mac (0 sorries!)
    ├── GammaInjectivity.lean -- Step 15: gamma injectivity (1 sorry)
    └── Macdonald.lean      -- Step 16+17: Macdonald theorem + FF (3 sorries)
```

---

## Previous Sessions

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
- **Agent 1 (full_gamma_tensor_injective)**: Developed key helper lemmas
  (`basisFreeMonoid_mul`, `star_basisFreeMonoid`, `FA_to_FA3_basisFreeMonoid`)
  for the z-separator argument. Sorry remains — needs to compose helpers into
  the full injectivity proof. The approach is correct: show image of tensor
  basis elements are distinct FreeMonoid words in FA3.
- **Agent 2 (mult_alg_surjectivity)**: Identified that current statement is
  too strong — a single M_{p,q} can't express every T_v. Correct reformulation
  uses `InMSpan` (ℝ-span of M operators). Found that `M_op (xCons k .one) .one`
  gives T_{x^{k+1}} by `rfl`-like reduction. Key missing piece: equation (2.58)
  `T_{x^k} ∘ M_{p,q} = ½(M_{x^k·p,q} + M_{p,x^k·q})` for closure under T composition.
- **Agent 3 (fundamental_formula_general)**: Confirmed sorry cannot be filled
  without: (a) generalizing FreeJordanAlg to 3+ generators, (b) filling `macdonald`
  first, or (c) direct algebraic proof. Updated docstring with precise diagnosis.
- **No new sorries filled**, but significant documentation and approach clarification.

### Session 110: Steps 15+16+17 scaffolding
- Created GammaInjectivity.lean (full_gamma, gamma_mac_tensor, injectivity)
- Created Macdonald.lean (theorem statement, FF corollaries)
- Fixed build issues in MOperator, MOperatorProperties, TensorSetup
- Research: detailed understanding of H-O 2.4.25 proof structure

### Session 109: Step 14 corrections
### Session 108: Steps 11+12 (M_op definition)
### Session 106: Steps 7+10 (SpecialFF + MonomialFJ)
### Session 105: Steps 6+9 (FreeSpecialJordan + GeneratorLemma)
### Session 104: Steps 3+5 (OperatorId + FreeJordan)
### Session 102: Steps 1+4+8 (UBilinear + FreeAlgebra + Monomial)
