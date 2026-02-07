# Handoff: 2026-02-07 (Session 116)

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
| MonoBlock.lean | 238 | 0 | FreeAssocMono, weight, prependX/Y, toFA |
| FJOperators.lean | ~185 | 0 | T, U, U_bilinear, pow, **JordanAlgebra instance**, bridge lemmas |
| SpecialFF.lean | 100 | 0 | **`special_fundamental_formula`**: FF in all assoc algebras |
| MonomialFJ.lean | 131 | 0 | M_{p,q} as FreeJordanAlg elements |
| MOperator.lean | 213 | 0 | `M_op` recursive definition, termination fully proved |
| MOperatorProperties.lean | 122 | 0 | Properties (ii)-(iv): U factorization, bilinear symmetrization |
| TensorSetup.lean | 179 | 0 | FA, FA3, evalFA, gamma_elem, gamma_mac (correct gamma) |
| GammaInjectivity.lean | ~335 | **0** | full_gamma_tensor, encode_word, z-separator, **ALL PROVED** |
| Equation258.lean | 58 | 0 | Equation (2.58) base cases (p=1/q=1, p=1/q=y^j, p=y^j/q=1) |
| FJBridge.lean | ~50 | 0 | Bridge: JordanAlgebra.U/U_bilinear ↔ FreeJordanAlg.U/U_bilinear ← NEW |
| **Macdonald.lean** | **~206** | **3** | Macdonald theorem + FF corollaries |

### Key NEW results (Session 115)

- **JordanAlgebra instance for FreeJordanAlg** (FJOperators.lean): CRITICAL unblock!
  FreeJordanAlg now has a JordanAlgebra instance, meaning ALL operator identities
  from OperatorId.lean (2.47)-(2.49) can now be applied to FreeJordanAlg elements.
  Bridge lemmas: `FJ_jmul_eq_mul`, `FJ_jpow_eq_pow`, `FJ_L_apply`.

- **FreeJordanAlg.mul bilinearity** (FJOperators.lean): 9 lemmas
  mul_add_left, mul_add_right, smul_mul_left, smul_mul_right, mul_zero_left/right,
  T_add, T_smul, T_zero. All sorry-free.

- **Equation (2.58) base cases** (Equation258.lean): 3 theorems
  eq258_one_one, eq258_one_yCons, eq258_yCons_one. All sorry-free.

## What NEEDS to be built (3 remaining sorries in Macdonald/)

### Sorry 1: `mult_alg_surjectivity` (Macdonald.lean:92)

**Goal**: Every T_v is a finite ℝ-linear combination of M_{p,q} operators.

**NOW UNBLOCKED by JordanAlgebra instance.** Strategy:
1. Prove full equation (2.58) using operator_identity_249 applied to FreeJordanAlg.
   The base case (p=x^i, q=y^j) now works since we can apply (2.49) directly.
   Need bridge: relate JordanAlgebra.U_bilinear_linear to FreeJordanAlg.U_bilinear.
2. Then: E is closed under U_{a,b} for a,b ∈ {1,x,y} → left ideal → E = full mult alg.
3. Estimated: ~100-150 LOC remaining.

### Sorry 2: `macdonald` (Macdonald.lean:145)

**Goal**: `∀ v, evalFA v = 0 → v = 0`
**Blockers**: Needs `mult_alg_surjectivity` + property (i).

### Sorry 3: `fundamental_formula_general` (Macdonald.lean:206)

**Goal**: FF holds in every JordanAlgebra.
**Three approaches**: See Session 114 notes.

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

## Recommended next session order

1. **Write bridge lemmas** connecting JordanAlgebra.U_bilinear_linear to FreeJordanAlg.U_bilinear.
   ~20 LOC. This allows operator_identity_249 to be stated for M_op.

2. **Prove full equation (2.58)** for p = x^i, q = y^j using operator_identity_249.
   Add to Equation258.lean. ~50-80 LOC.

3. **Prove (2.58) for general weight** by induction. ~50-80 LOC.

4. **Fill `mult_alg_surjectivity`** using (2.58) + left ideal argument. ~50-70 LOC.

5. **Fill `macdonald`** using surjectivity + property (i) + gamma injectivity.

6. **Fill `fundamental_formula_general`** — needs 3-gen FreeJordanAlg or Macdonald metatheorem.

## Reference — READ BEFORE STARTING

**MANDATORY READING** (do NOT re-research these topics):
- **HANDOFF.md** (this file)
- **CLAUDE.md** — Build instructions, H-O ground truth, golden rules

Book: `examples3/Jordan Operator Algebras/joa-m/joa-m.md`
- Equation (2.58): lines 1326-1377
- Proof of Macdonald 2.4.25: lines 1379-1389

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
    ├── FJOperators.lean    -- T, U, U_bilinear, pow, **JordanAlgebra instance** ← NEW
    ├── MonomialFJ.lean     -- M_{p,q} as FJ elements
    ├── MOperator.lean      -- M_op recursive definition (0 sorries!)
    ├── MOperatorProperties.lean -- Properties (ii)-(iv) (0 sorries!)
    ├── TensorSetup.lean    -- FA, FA3, evalFA, gamma_mac (0 sorries!)
    ├── GammaInjectivity.lean -- Step 15: gamma injectivity (0 sorries!)
    ├── Equation258.lean    -- Eq (2.58) base cases ← NEW
    └── Macdonald.lean      -- Step 16+17: Macdonald theorem + FF (3 sorries)
```

---

## Previous Sessions

### Session 116: Bridge lemmas (FJBridge.lean)
- **New file FJBridge.lean** with 3 bridge lemmas (0 sorries):
  - `FJ_U_eq`: `JordanAlgebra.U a v = FreeJordanAlg.U a v`
  - `FJ_U_linear_apply`: `JordanAlgebra.U_linear a v = FreeJordanAlg.U a v`
  - `FJ_U_bilinear_eq`: `JordanAlgebra.U_bilinear_linear a b v = FreeJordanAlg.U_bilinear a b v`
- These bridge the JordanAlgebra-level operator identities (OperatorId.lean) to
  the FreeJordanAlg-level operators used in M_op. The key difference is nsmul 2
  vs (2:ℝ)• and argument ordering (triple vs U_bilinear).
- **Key lesson**: Importing UBilinear into FJOperators.lean breaks existing proofs
  (linarith failure in mul_zero_left). Solution: separate file (FJBridge.lean)
  that imports both FJOperators and OperatorId.

### Session 115: JordanAlgebra instance + bilinearity + equation (2.58) base cases
- **JordanAlgebra instance** for FreeJordanAlg (FJOperators.lean): CRITICAL UNBLOCK.
  All operator identities (2.47)-(2.49) from OperatorId.lean can now be applied to FreeJordanAlg.
- **9 bilinearity lemmas** for FreeJordanAlg.mul and T (FJOperators.lean).
- **3 equation (2.58) base cases** proved (Equation258.lean).
- **Bridge lemmas**: FJ_jmul_eq_mul, FJ_jpow_eq_pow, FJ_L_apply.
- **Key finding**: The hard (2.58) cases (p=x^i, q=y^j) need operator_identity_249
  applied to FreeJordanAlg. Now possible thanks to JordanAlgebra instance.
- **0 sorries added, 0 sorries filled** (infrastructure session).

### Session 114: Analysis of mult_alg_surjectivity + learnings
### Session 113: Fill gamma injectivity + toFA + fix surjectivity
### Session 112: Fill gamma_mac_injective + investigation
### Session 111: Macdonald sorry investigation
### Session 110: Steps 15+16+17 scaffolding
