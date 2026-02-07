# Handoff: 2026-02-07 (Session 121)

## GOAL: Fill `fundamental_formula` sorry (the #1 priority)

**File**: `AfTests/Jordan/FundamentalFormula.lean:259`
**Statement**: `U (U a b) x = U a (U b (U a x))` for all `a b x : J` in any `JordanAlgebra J`
**Route**: Macdonald's theorem (H-O 2.4.13) lifts `special_fundamental_formula` to all Jordan algebras

## Session 121 summary

1. **eq258_xCons_yCons_lt** — Eq(2.58) weight<=1, i<k case: `T_{x^{k+1}} M_{x^{i+1},y^{j+1}} = 1/2(M_{x^{i+k+2},y^{j+1}} + M_{x^{i+1},x^k·y^{j+1}})`. Sorry-free, ~50 LOC. Uses operator_identity_247, eq258_xCons_yCons_ge, power_formula_245. H-O lines 1336-1344.

This completes the weight<=1 case of eq(2.58): both i>=k and i<k are now sorry-free.

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
| MOperatorProperties.lean | 0 | Property (ii), (iii) x+y general+equal-exp, (iv) k,l>=1. FJ_U_pow_comp, M_op_U_prependX, M_op_U_prependY. |
| TensorSetup.lean | 0 | FA, FA2, FA3, symTensor, evalFA, gamma_mac (correct gamma) |
| GammaInjectivity.lean | 0 | full_gamma_tensor_injective, z-separator — MATCH H-O |
| Equation258.lean | 0 | Eq (2.58) base cases + weight<=1 both cases (eq258_xCons_yCons_ge + eq258_xCons_yCons_lt) |
| FJBridge.lean | 0 | Bridge: JordanAlgebra ↔ FreeJordanAlg operators |
| **Macdonald.lean** | **3** | Macdonald theorem + FF corollaries |

## Critical path: 3 sorries → 0

```
af-2nr5: Property (iii) x+y ✓ DONE ─┬─→ af-07gj: Eq(2.58) weight>1 ─→ af-mlnv: GenLemma+Surj
                                     │                                        │
af-ub66: Eq(2.58) weight≤1 ✓ DONE ──┘                                        ↓
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
- **af-07gj**: Eq(2.58) weight>1 — H-O lines 1346-1377. Now unblocked (af-ub66 complete).
- **af-opkm**: Property (i) — H-O line 1217, ~40-60 LOC

### What each remaining issue requires (H-O citations):

**af-ub66 — Eq(2.58) weight<=1** (Equation258.lean) — **COMPLETE**
- H-O lines 1332-1335 (i>=k): **DONE** (`eq258_xCons_yCons_ge`). Uses operator_identity_249 + bridge lemmas.
- H-O lines 1336-1344 (i<k): **DONE** (`eq258_xCons_yCons_lt`). Uses operator_identity_247, eq258_xCons_yCons_ge, power_formula_245.

**af-07gj — Eq(2.58) weight>1** (Equation258.lean, BLOCKED by af-2nr5+af-ub66)
- H-O lines 1346-1367 (i≥k): Start from (2.55a)/(2.56a), apply (2.49), induction.
- H-O lines 1369-1377 (i<k): Apply (2.47), (2.49), induction.

**af-mlnv — Generator lemma + surjectivity** (GeneratorLemma.lean + Macdonald.lean, BLOCKED)
- State 2.4.23 conclusion: {U_{a,b}} generates mult algebra. ~30 LOC.
- Prove mult_alg_surjectivity: E closed under T_x,T_y (by 2.58), U_x,U_y (by iii), U_{x,y} (by iv k,l≥1 already done). By 2.4.23, E=everything. ~20 LOC.

**af-opkm — Property (i)** (Macdonald.lean)
- M_{p,q}(z) = gamma_mac(toFA p, toFA q). Needs evalAssoc into FA3.

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

### Session 121: eq258_xCons_yCons_lt — Eq(2.58) weight<=1 i<k case
- eq258_xCons_yCons_lt: ~50 LOC sorry-free proof using (2.47) + ge case + (2.45)
- Weight<=1 case of eq(2.58) is now COMPLETE (both i>=k and i<k)
- af-ub66 closed; af-07gj (weight>1) now unblocked

### Session 120: eq258_xCons_yCons_ge + M_op_U_prependY fill + build fixes
- eq258_xCons_yCons_ge: Eq(2.58) i>=k case via operator_identity_249 — sorry-free
- M_op_U_prependY: FILLED (was sorry) — 65-line symmetric proof
- Fixed 5 files for mathlib/toolchain compatibility (FJOperators, FJBridge, MonoBlock, MOperatorProperties)
- Closed af-2nr5 (Property iii y-version)

### Session 119: Property (iii) general x-version + U-power composition
- FJ_U_pow_comp: U(a^m)(U(a^n)(w)) = U(a^{m+n})(w) — sorry-free
- M_op_U_prependX: U_{x^{k+1}} M_{p,q} = M_{x^{k+1}·p, x^{k+1}·q} — sorry-free (9 cases)
- M_op_U_prependY: y-version — sorry'd (filled in Session 120)

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
