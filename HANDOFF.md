# Handoff: 2026-02-07 (Session 118)

## GOAL: Fill `fundamental_formula` sorry (the #1 priority)

**File**: `AfTests/Jordan/FundamentalFormula.lean:259`
**Statement**: `U (U a b) x = U a (U b (U a x))` for all `a b x : J` in any `JordanAlgebra J`
**Route**: Macdonald's theorem (H-O 2.4.13) lifts `special_fundamental_formula` to all Jordan algebras

## Session 118 summary

1. **Full H-O audit** — 4 parallel agents compared every Lean file against Hanche-Olsen ground truth
2. **Deleted 352 lines of dead/hallucinated code**:
   - `Monomial.lean` (MacGen, AssocWord, M_word, M_eval — superseded by MonoBlock/MOperator)
   - `MonomialFJ.lean` (M_eval_FJ — wrong type: elements not operators)
   - `gamma_elem`, `gamma` and all properties from TensorSetup.lean (wrong gamma map; advertised a FALSE theorem)
3. **Closed 3 stale/duplicate issues** (af-tggl, af-i8oo, af-efkr)
4. **Created 4 new fine-grained issues** with H-O line citations and dependency chain

## What EXISTS (all sorry-free unless noted)

### Macdonald infrastructure (`AfTests/Jordan/Macdonald/`)

| File | Sorries | What it does |
|------|---------|-------------|
| FreeAlgebra.lean | 0 | FreeMagma, FreeNAAlg (ℝ-algebra on binary trees) |
| FreeJordan.lean | 0 | FreeJordanAlg = FreeNAAlg/JordanCong (2 generators x,y) |
| FreeSpecialJordan.lean | 0 | `evalAssoc : A → A → FreeJordanAlg → A` (eval into assoc algebras) |
| UBilinear.lean | 0 | `U_bilinear` linear map, simp lemmas |
| OperatorId.lean | 0 | Operator identities (2.47)-(2.51) — all MATCH H-O |
| GeneratorLemma.lean | 0 | Lemma 2.4.23 ingredients (conclusion NOT yet stated) |
| MonoBlock.lean | 0 | FreeAssocMono, weight, prependX/Y, toFA |
| FJOperators.lean | 0 | T, U, U_bilinear, pow, **JordanAlgebra instance**, bridge lemmas |
| SpecialFF.lean | 0 | **`special_fundamental_formula`**: FF in all assoc algebras |
| MOperator.lean | 0 | `M_op` recursive definition (2.52)-(2.57), termination proved — MATCH H-O |
| MOperatorProperties.lean | 0 | Property (ii), partial (iii)/(iv) for equal-exponent + k,l≥1 cases |
| TensorSetup.lean | 0 | FA, FA2, FA3, symTensor, evalFA, gamma_mac (correct gamma) |
| GammaInjectivity.lean | 0 | full_gamma_tensor_injective, z-separator — MATCH H-O |
| Equation258.lean | 0 | Eq (2.58) base cases (p=1/q=1, p=1/q=y^j, p=y^j/q=1) |
| FJBridge.lean | 0 | Bridge: JordanAlgebra ↔ FreeJordanAlg operators |
| **Macdonald.lean** | **3** | Macdonald theorem + FF corollaries |

**Deleted in Session 118**: Monomial.lean, MonomialFJ.lean (dead code, no H-O basis)

## Critical path: 3 sorries → 0

```
af-2nr5: Property (iii) general     ─┬─→ af-07gj: Eq(2.58) weight>1 ─→ af-mlnv: GenLemma+Surj
af-ub66: Eq(2.58) weight≤1 ─────────┘                                        │
                                                                              ↓
                                                            af-0cc6: mult_alg_surjectivity
                                                                              │
af-opkm: Property (i) ───────────────────────────────────────────────────────┐│
                                                                              ↓
                                                            af-g2kb: Macdonald theorem
                                                                              │
                                                                              ↓
                                                            af-gzm1: fundamental_formula
```

### Ready NOW (no blockers):
- **af-2nr5**: Property (iii) general — H-O lines 1290-1302, ~30-40 LOC
- **af-ub66**: Eq(2.58) weight≤1 — H-O lines 1332-1344, ~50 LOC
- **af-opkm**: Property (i) — H-O line 1217, ~40-60 LOC

### What each issue requires (H-O citations):

**af-2nr5 — Property (iii) general** (MOperatorProperties.lean)
- H-O lines 1290-1302: Case p,q∈Y → (2.53a). Case p,q∈X → U_{x^k}U_{x^i}=U_{x^{k+i}}. Case mixed → (2.53a) directly.
- Currently only equal-exponent case proved (`M_op_xCons_xCons`). Need general case.

**af-ub66 — Eq(2.58) weight≤1** (Equation258.lean)
- H-O lines 1332-1335 (i≥k): Use `operator_identity_249` on `U_{x^i,y^j}`. Result = ½(U_{x^k}U_{x^{i-k},y^j} + U_{x^{i+k},y^j}). Then (2.52)+(2.53a) to rewrite as M_op terms.
- H-O lines 1336-1344 (i<k): Use `operator_identity_247`, `power_formula_245`, eq(2.56a), (iii).
- **FJBridge.lean** import needed for operator identity application to FreeJordanAlg.

**af-07gj — Eq(2.58) weight>1** (Equation258.lean, BLOCKED by af-2nr5+af-ub66)
- H-O lines 1346-1367 (i≥k): Start from (2.55a)/(2.56a), apply (2.49), induction.
- H-O lines 1369-1377 (i<k): Apply (2.47), (2.49), induction.

**af-mlnv — Generator lemma + surjectivity** (GeneratorLemma.lean + Macdonald.lean, BLOCKED)
- State 2.4.23 conclusion: {U_{a,b}} generates mult algebra. ~30 LOC.
- Prove mult_alg_surjectivity: E closed under T_x,T_y (by 2.58), U_x,U_y (by iii), U_{x,y} (by iv k,l≥1 already done). By 2.4.23, E=everything. ~20 LOC.

**af-opkm — Property (i)** (Macdonald.lean)
- M_{p,q}(z) = gamma_mac(toFA p, toFA q). Needs evalAssoc into FA3.

## Audit findings (Session 118)

### What MATCHES H-O (verified, solid)
- All operator identities (2.47)-(2.51) — OperatorId.lean
- M_op definition (2.52)-(2.57) — MOperator.lean
- Gamma injectivity (z-separator) — GammaInjectivity.lean
- Special FF — SpecialFF.lean
- Free algebra constructions — FreeAlgebra, FreeJordan, FreeSpecialJordan
- FreeAssocMono alternating blocks — MonoBlock.lean

### What was HALLUCINATED (now deleted)
- `gamma_elem` (a→a⊗1+1⊗a): wrong gamma, no H-O basis, advertised FALSE theorem
- `Monomial.lean` (MacGen, AssocWord, M_word): superseded dead code
- `MonomialFJ.lean` (M_eval_FJ): wrong type (elements not operators)

## Build & sorries

**Build**: `lake build AfTests 2>&1 | tail -40` — PASSES
**Total sorries**: 7 (3 in Macdonald.lean, 1 in FundamentalFormula.lean, 1 in Square.lean, 2 in Classification/)

## Reference — READ BEFORE STARTING

**MANDATORY**: Read the H-O book section FIRST, cite line numbers.
- Book: `examples3/Jordan Operator Algebras/joa-m/joa-m.md`
- Property (iii) proof: lines 1290-1302
- Equation (2.58) proof: lines 1326-1377
- Macdonald 2.4.25 proof: lines 1379-1389
- `bd ready` for available work

## Previous Sessions

### Session 118: H-O audit, dead code deletion, issue restructuring
- Full audit: 4 agents compared all Lean files against H-O ground truth
- Deleted 352 LOC of dead/hallucinated code (Monomial.lean, MonomialFJ.lean, gamma_elem)
- Closed 3 stale issues, created 4 new fine-grained issues with dependency chain
- Key insight: mult_alg_surjectivity does NOT need full property (iv); only (iii), (iv) k,l≥1 (done), and (2.58)

### Session 117: Analysis of eq258 + fundamental_formula_general (no code)
### Session 116: Bridge lemmas (FJBridge.lean)
### Session 115: JordanAlgebra instance + bilinearity + equation (2.58) base cases
### Session 114: Analysis of mult_alg_surjectivity + learnings
### Session 113: Fill gamma injectivity + toFA + fix surjectivity
### Session 112: Fill gamma_mac_injective + investigation
### Session 111: Macdonald sorry investigation
### Session 110: Steps 15+16+17 scaffolding
