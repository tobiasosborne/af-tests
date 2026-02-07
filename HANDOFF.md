# Handoff: 2026-02-07 (Session 117)

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
| FJBridge.lean | ~50 | 0 | Bridge: JordanAlgebra.U/U_bilinear ↔ FreeJordanAlg.U/U_bilinear |
| **Macdonald.lean** | **~206** | **3** | Macdonald theorem + FF corollaries |

## What NEEDS to be built (3 remaining sorries in Macdonald/)

### Sorry 1: `mult_alg_surjectivity` (Macdonald.lean:92)

**Goal**: Every T_v is a finite ℝ-linear combination of M_{p,q} operators.
**Blocked by**: Full equation (2.58) proof.

### Sorry 2: `macdonald` (Macdonald.lean:145)

**Goal**: `∀ v, evalFA v = 0 → v = 0`
**Blockers**: Needs `mult_alg_surjectivity` + property (i).

### Sorry 3: `fundamental_formula_general` (Macdonald.lean:206)

**Goal**: FF holds in every JordanAlgebra.
**Blockers**: Needs `macdonald` or direct proof. See Session 117 analysis.

## IMMEDIATE NEXT STEP — eq258_xCons_yCons_ge

**READY TO IMPLEMENT.** Complete proof skeleton in `memory/eq258-proof-strategy.md`.

Steps:
1. Add `import AfTests.Jordan.Macdonald.FJBridge` to Equation258.lean
2. Copy proof skeleton from memory file (~35 LOC)
3. Build and fix any type issues
4. This proves (2.58) for p=x^{i+1}, q=y^{j+1}, i≥k

**Why it matters**: For k=0, i≥0 always holds. So this covers T_x ∘ M_{x^i, y^j} ∈ E,
which is needed for mult_alg_surjectivity (the H-O 2.4.25 argument).

## Proof dependency chain

```
[DONE] full_gamma_tensor_injective ──→ gamma_mac_injective ──┐
                                                              ├──→ macdonald ──→ macdonald_injectivity
eq258_xCons_yCons_ge ──→ eq258_full ──→ mult_alg_surjectivity┘           │
M_op_eval_z (property (i)) ─────────────────────────────────┘           ↓
                                                              fundamental_formula_free
                                                                     │
                                                                     ↓
                                                          fundamental_formula_general
                                                                     │
                                                                     ↓
                                                    Fill fundamental_formula sorry
```

## Session 117 findings (analysis, no code)

### Key finding: fundamental_formula_general is HARDER than expected
- Direct transfer from FJ{x,y} to general JA **FAILS**: FF is U_{U_a(b)}(x) = U_a(U_b(U_a(x))),
  linear in x. Evaluation map evalJA : FJ{x,y} → J sends x→a, y→b, but im(evalJA) = ⟨a,b⟩ ⊂ J.
  So FF only transfers for x ∈ ⟨a,b⟩, not arbitrary x ∈ J.
- Generalizing FreeJordanAlg to 3 generators doesn't help: FJ(Fin 3) is NOT special
  (Shirshov only for 2 generators). Can't use special_fundamental_formula.
- **ONLY viable paths**: (a) Full Macdonald metatheorem, or (b) McCrimmon direct algebraic proof.
- Path (a) requires the full chain: eq258 → mult_alg_surjectivity → macdonald.
- Path (b) is ~100 LOC of degree-(4,2,1) polynomial identity verification. Very tedious.

### eq258_xCons_yCons_ge proof strategy (fully worked out)
- Uses `operator_identity_249` specialized to FreeJordanAlg
- Bridge: `DFunLike.congr_fun h249 v` + simp with `FJ_L_apply, FJ_jpow_eq_pow, FJ_U_bilinear_eq, FJ_U_linear_apply`
- Three M_op unfoldings: LHS base case, RHS1 base case, RHS2 via (2.53) with by_cases i=k
- Final calc: multiply by (1/2), rw h249v, add_comm via abel
- Complete proof skeleton: `memory/eq258-proof-strategy.md`

## CRITICAL TRAP TO AVOID

**DO NOT** try to prove `gamma_jordan_product` with `gamma_elem a = a⊗1+1⊗a`.
It is mathematically **FALSE**. The correct gamma for Macdonald is `gamma_mac` in TensorSetup.lean.

## Build & sorries

**Build**: `lake build AfTests 2>&1 | tail -40` — PASSES
**Sorries in Macdonald/**: 3 total (mult_alg_surjectivity, macdonald, fundamental_formula_general)
**Sorries elsewhere**: FundamentalFormula (1), Square (1), Classification (2)

## Recommended next session order

1. **Implement eq258_xCons_yCons_ge** — proof skeleton ready in memory file. ~35 LOC.
2. **Prove remaining (2.58) cases** — p=x^{i+1}/q=y^{j+1} with i<k (uses 2.47), inductive cases.
3. **Fill `mult_alg_surjectivity`** — uses (2.58) + left ideal argument. ~50-70 LOC.
4. **Fill `macdonald`** — uses surjectivity + property (i) + gamma injectivity.
5. **Fill `fundamental_formula_general`** — needs Macdonald metatheorem or direct proof.

## Reference — READ BEFORE STARTING

**MANDATORY READING** (do NOT re-research these topics):
- **HANDOFF.md** (this file)
- **CLAUDE.md** — Build instructions, H-O ground truth, golden rules
- **memory/eq258-proof-strategy.md** — COPY-PASTE proof skeleton

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
    ├── FJOperators.lean    -- T, U, U_bilinear, pow, **JordanAlgebra instance**
    ├── MonomialFJ.lean     -- M_{p,q} as FJ elements
    ├── MOperator.lean      -- M_op recursive definition (0 sorries!)
    ├── MOperatorProperties.lean -- Properties (ii)-(iv) (0 sorries!)
    ├── TensorSetup.lean    -- FA, FA3, evalFA, gamma_mac (0 sorries!)
    ├── GammaInjectivity.lean -- Step 15: gamma injectivity (0 sorries!)
    ├── Equation258.lean    -- Eq (2.58) base cases
    ├── FJBridge.lean       -- Bridge: JordanAlgebra ↔ FreeJordanAlg operators
    └── Macdonald.lean      -- Step 16+17: Macdonald theorem + FF (3 sorries)
```

---

## Previous Sessions

### Session 117: Analysis of eq258 + fundamental_formula_general (no code)
- **Worked out complete proof strategy** for eq258_xCons_yCons_ge (~35 LOC)
  Saved to `memory/eq258-proof-strategy.md`. Ready to implement.
- **Key finding**: fundamental_formula_general cannot use direct transfer from FJ{x,y}.
  im(evalJA) = ⟨a,b⟩ ⊂ J, so FF only proved for x ∈ ⟨a,b⟩. Generalizing to
  FJ(Fin 3) doesn't help (not special). Need full Macdonald or McCrimmon direct proof.
- **0 sorries added, 0 sorries filled** (pure analysis session).

### Session 116: Bridge lemmas (FJBridge.lean)
- **New file FJBridge.lean** with 3 bridge lemmas (0 sorries)

### Session 115: JordanAlgebra instance + bilinearity + equation (2.58) base cases
### Session 114: Analysis of mult_alg_surjectivity + learnings
### Session 113: Fill gamma injectivity + toFA + fix surjectivity
### Session 112: Fill gamma_mac_injective + investigation
### Session 111: Macdonald sorry investigation
### Session 110: Steps 15+16+17 scaffolding
