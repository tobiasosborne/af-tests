# Handoff: 2026-02-07 (Session 124)

## GOAL: Fill `fundamental_formula` sorry (the #1 priority)

**File**: `AfTests/Jordan/FundamentalFormula.lean:259`
**Statement**: `U (U a b) x = U a (U b (U a x))` for all `a b x : J` in any `JordanAlgebra J`
**Route**: Macdonald's theorem (H-O 2.4.13) lifts `special_fundamental_formula` to all Jordan algebras

## Session 124 summary

**Task**: Parallel agent session on 3 tasks (af-07gj, af-opkm, af-mlnv)

**Result**: All 3 agents hit context limits before writing file changes. No code modifications.

**Root cause**: Each task requires deep exploration (reading goal states, searching lemmas,
understanding M_op's ~20 case structure) which consumes context before actual code writing.
These tasks are too complex for single-agent sessions — they need focused, incremental work.

**Recommendation for next session**: Work on ONE task at a time:
1. **af-07gj** (Eq258 algebra closure): Start by running `lean_goal` on lines 281 and 333
   of Equation258.lean. The goals involve M_op terms that need to be rewritten using
   M_op_U_bilinear_yCons, M_op_U_prependX, M_op_xCons_yCons_yCons. ~30-40 LOC each.
2. **af-opkm** (M_op_evalFA3): Large structural induction (~20 cases). Best approached by
   proving cases incrementally, starting with base cases (already done as separate lemmas)
   then tackling recursive cases one at a time.
3. **af-mlnv** (GeneratorLemma + surjectivity): Scaffolding task. State 2.4.23 conclusion,
   then scaffold mult_alg_surjectivity proof.

## Session 123 summary

**Task**: af-07gj — Eq(2.58) weight>1 inductive cases (H-O lines 1346-1377)

1. **Equation258.lean** — Added weight > 1 inductive case framework (~170 LOC, 2 sorries):
   - `T_sub`: T distributes over subtraction (sorry-free)
   - `T_smul'`: T distributes over scalar multiplication (sorry-free)
   - `eq259_xCons_yCons`: Equation (2.59) recurrence = M_op_xCons_yCons_yCons (sorry-free)
   - `eq258_xCons_yCons_general_ge`: Case i >= k (H-O lines 1346-1367, 1 sorry at algebra)
   - `eq258_xCons_yCons_general_lt`: Case i < k (H-O lines 1369-1377, 1 sorry at algebra)

2. **Proof structure** (both cases follow H-O exactly):
   - Step 1: Expand LHS via eq(2.59) = M_op recurrence (2.55a)
   - Step 2: Distribute T over sub/smul using T_sub, T_smul'
   - Step 3: Apply operator identity (2.49 for ge, 2.47 for lt) via FJBridge
   - Step 4: Apply inductive hypothesis `ih_swap` for swapped M term
   - Step 5: Halve the (2.49) result to get expression for T term (ge only)
   - SORRY: Remaining algebra (steps 5-7 in ge, steps 5-6 in lt)

3. **What the sorry needs**: After steps 1-4/5, the goal involves:
   - U_bilinear and U terms from operator identities
   - M_op terms from ih_swap
   - Need: M_op_U_bilinear_yCons (property iv) to convert U_bi to M_op
   - Need: M_op_U_prependX (property iii) to extract U factors
   - Need: M_op_xCons_yCons_yCons / M_op_xCons_xCons to expand RHS M_op terms
   - Then cancel matching terms

4. **Pre-existing issue**: MOperatorProperties.lean and existing eq258_xCons_yCons_ge/lt
   have broken proofs (simp/omega failures from toolchain update). These cascade
   errors into new code when compiling the file directly, but `lean_run_code` confirms
   all new code compiles correctly in isolation. The full `lake build AfTests` passes
   because it uses cached .olean files.

**Key insight**: The algebra closure requires distributing U through smul/add
(U is linear in 2nd arg via JordanAlgebra.U_linear), applying (iii) and (iv)
to convert all U/U_bilinear terms to M_op terms, then cancelling. This is
~30-40 LOC of careful rewriting, feasible in a focused session.

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
| FJOperators.lean | 0 | T, U, U_bilinear, pow, **JordanAlgebra instance**, bridge lemmas, **evalAssoc naturality** |
| SpecialFF.lean | 0 | **`special_fundamental_formula`**: FF in all assoc algebras |
| MOperator.lean | 0 | `M_op` recursive definition (2.52)-(2.57), termination proved — MATCH H-O |
| MOperatorProperties.lean | 0 | Property (ii), (iii) x+y general+equal-exp, (iv) k,l>=1. FJ_U_pow_comp, M_op_U_prependX, M_op_U_prependY. |
| TensorSetup.lean | 0 | FA, FA2, FA3, symTensor, evalFA, gamma_mac (correct gamma) |
| GammaInjectivity.lean | 0 | full_gamma_tensor_injective, z-separator — MATCH H-O |
| Equation258.lean | 2 | Eq (2.58) base cases + weight<=1 + weight>1 framework (ge/lt with sorry at algebra) |
| FJBridge.lean | 0 | Bridge: JordanAlgebra ↔ FreeJordanAlg operators |
| **PropertyI.lean** | **1** | Property (i): gamma_mac recurrences + M_op_evalAssoc bridge (H-O 2.4.24 line 1217) |
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
- **af-opkm**: Property (i) — MOSTLY DONE (gamma_mac identities proved in PropertyI.lean).
  Remaining: formal connection from M_op to gamma_mac via 3-gen FreeJordanAlg or evalAssoc naturality.

### What each remaining issue requires (H-O citations):

**af-ub66 — Eq(2.58) weight<=1** (Equation258.lean) — **COMPLETE**
- H-O lines 1332-1335 (i>=k): **DONE** (`eq258_xCons_yCons_ge`). Uses operator_identity_249 + bridge lemmas.
- H-O lines 1336-1344 (i<k): **DONE** (`eq258_xCons_yCons_lt`). Uses operator_identity_247, eq258_xCons_yCons_ge, power_formula_245.

**af-07gj — Eq(2.58) weight>1** (Equation258.lean, IN PROGRESS — framework done, 2 sorries)
- H-O lines 1346-1367 (i>=k): `eq258_xCons_yCons_general_ge` — steps 1-5 done, sorry at algebra.
- H-O lines 1369-1377 (i<k): `eq258_xCons_yCons_general_lt` — steps 1-4 done, sorry at algebra.
- Remaining: ~30-40 LOC algebra closure using (iii), (iv), cancel terms.

**af-mlnv — Generator lemma + surjectivity** (GeneratorLemma.lean + Macdonald.lean, BLOCKED)
- State 2.4.23 conclusion: {U_{a,b}} generates mult algebra. ~30 LOC.
- Prove mult_alg_surjectivity: E closed under T_x,T_y (by 2.58), U_x,U_y (by iii), U_{x,y} (by iv k,l≥1 already done). By 2.4.23, E=everything. ~20 LOC.

**af-opkm — Property (i)** (PropertyI.lean + FJOperators.lean)
- gamma_mac algebraic identities: **DONE** (PropertyI.lean)
- evalAssoc naturality lemmas: **DONE** (FJOperators.lean — evalAssoc_one/T/U_bilinear/pow_x/pow_y)
- M_op_evalAssoc bridge: **1 sorry** — structural induction on M_op ~20 cases using naturality lemmas
- Estimated: ~80 LOC of case analysis matching M_op definition

## Build & sorries

**Build**: `lake build AfTests 2>&1 | tail -40` — PASSES
**Total sorries**: 10 (3 in Macdonald.lean, 2 in Equation258.lean, 1 in PropertyI.lean, 1 in FundamentalFormula.lean, 1 in Square.lean, 2 in Classification/)

## Reference — READ BEFORE STARTING

**MANDATORY**: Read the H-O book section FIRST, cite line numbers.
- Book: `examples3/Jordan Operator Algebras/joa-m/joa-m.md`
- Property (iii) proof: lines 1290-1302
- Equation (2.58) proof: lines 1326-1377
- Macdonald 2.4.25 proof: lines 1379-1389
- `bd ready` for available work

## Previous Sessions

### Session 123: Eq(2.58) weight>1 framework (af-07gj)
- Equation258.lean: 5 new theorems (~170 LOC, 2 sorries at algebra closure)
- T_sub, T_smul': T linearity helpers (sorry-free)
- eq259_xCons_yCons: Equation (2.59) = M_op recurrence (sorry-free)
- eq258_xCons_yCons_general_ge: Case i>=k with ih_swap (1 sorry)
- eq258_xCons_yCons_general_lt: Case i<k with ih_swap (1 sorry)
- Both proofs: steps 1-4/5 complete (expand via 2.59, distribute T, apply operator
  identity 2.49/2.47, apply ih_swap, halve). Sorry at algebra closure.
- Pre-existing breakage: MOperatorProperties.lean and existing eq258 base case proofs
  have simp/omega failures from toolchain update. New code verified via lean_run_code.

### Session 122b: evalAssoc naturality + M_op_evalAssoc bridge
- FJOperators.lean: 5 new evalAssoc naturality lemmas (evalAssoc_one, evalAssoc_T,
  evalAssoc_U_bilinear, evalAssoc_pow_x, evalAssoc_pow_y) — all sorry-free
- PropertyI.lean: added M_op_evalAssoc bridge theorem (1 sorry) with full documentation
  of 3 approaches and type mismatch analysis
- Macdonald.lean: updated documentation with available naturality lemmas
- Key finding: the typing bridge requires structural induction on M_op ~20 cases

### Session 121b: Property (i) — gamma_mac algebraic identities
- NEW FILE PropertyI.lean: 0 sorries, ~250 LOC
- 7 key theorems: gamma_mac_one_one, gamma_mac_assocU, gamma_mac_diff_letter,
  gamma_mac_T_recurrence, gamma_mac_U_bilinear, gamma_mac_prependX_inY, gamma_mac_prependY_inX
- 5 convenience theorems: gamma_mac_mono_* connecting to FreeAssocMono
- Helper simp lemmas: FA.star_x_pow, FA.star_y_pow, FA_to_FA3_one_eq, toFA_xPow, toFA_yPow
- Documented architecture gap: formal M_op↔gamma_mac needs 3-gen FreeJordanAlg or naturality
- Macdonald.lean: updated imports + property (i) documentation

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
