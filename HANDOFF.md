# Handoff: 2026-02-07 (Session 110)

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
| **Macdonald.lean** | **164** | **4** | Macdonald theorem statement + proof skeleton + FF corollaries |

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

## What NEEDS to be built (5 remaining sorries)

### Sorry 1: `full_gamma_tensor_injective` (GammaInjectivity.lean:127)

**Goal**: Prove `Function.Injective full_gamma_tensor`

**Approach**: Monomial separation. The map sends basis element `m₁ ⊗ m₂` (from
`Basis.tensorProduct` of `FreeAlgebra.basisFreeMonoid`) to `m₁ · [2] · reverse(m₂)`
in FA3. Since `z = ι 2` appears exactly once, different `(m₁, m₂)` pairs give
different FA3-words. This gives linear independence of the image, hence injectivity.

**Key API**: `FreeAlgebra.basisFreeMonoid`, `Basis.tensorProduct`, `FreeMonoid` operations.

### Sorry 2: `mult_alg_surjectivity` (Macdonald.lean:85)

**Goal**: Every multiplication operator on FreeJordanAlg is M_t for some symmetric tensor.

**Statement**: `∀ v, ∃ p q, ∀ w, M_op p q w = T v w`

**Approach**: Show the range of M_op contains id (property ii) and is closed under
U_{x^k} (property iii) and U_{x^k,y^l} (property iv). By GeneratorLemma (2.4.23),
{U_{a,b} : a,b ∈ {1,x,y}} generate the multiplication algebra, so the range is everything.

**Note**: The exact statement may need refinement. The multiplication algebra is generated
by L operators, not just T operators. The surjectivity connects M_op (which takes
FreeAssocMono pairs) to the operator algebra (which takes FreeJordanAlg → FreeJordanAlg).

### Sorry 3: `gamma_mac_injective` (Macdonald.lean:101)

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

### Sorry 5: `fundamental_formula_general` (Macdonald.lean:160)

**Goal**: FF holds in every JordanAlgebra.

**Approach**: `fundamental_formula_free` gives FF in FreeJordanAlg. For a general
JA J and a,b,x ∈ J, the operator `U_{U_a(b)} - U_a U_b U_a` is a multiplication
operator in (a,b). By Macdonald it's zero on FreeJordanAlg. The operator identity
transfers to any JA because `U_{U_a(b)} = U_a U_b U_a` as endomorphisms (not just
on specific elements).

**Critical detail from book (H-O 2.4.13)**: Macdonald's theorem is about multiplication
operators in 2 variables acting on FJ{x,y,z} (3 generators). The FF involves 3
variables but the operator only depends on 2. The third variable z is the "input"
to the operator. So the theorem gives `U_{U_x(y)} = U_x U_y U_x` as endomorphisms
of FJ{x,y,z}, which transfers to any JA.

**For formalization**: Need either (a) FreeJordanAlg on 3 generators and its universal
property, or (b) argue at the operator level that the operator identity transfers.

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
**Sorries in Macdonald/**: 5 total (see above)
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

## Reference

Book: `examples3/Jordan Operator Algebras/joa-m/joa-m.md`
- Macdonald's theorem: 2.4.13 (line ~1063)
- M_{p,q} construction: 2.4.24 (line ~1215)
- Proof of Macdonald: 2.4.25 (line ~1379)
- Star involution: 2.3.5 (line ~859)
- Mathlib research: `memory/macdonald-steps14-17.md`

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
    └── Macdonald.lean      -- Step 16+17: Macdonald theorem + FF (4 sorries)
```

---

## Previous Sessions

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
