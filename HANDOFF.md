# Handoff: 2026-01-30 (Session 52)

## Completed This Session

### 1. Deep Analysis of Fundamental Formula Blockers
Investigated the structural challenges in proving `linearized_jordan_aux` and `fundamental_formula`:

**Key Finding**: The `linearized_jordan_aux` theorem requires proving:
```lean
(a∘(bc))∘a² + (b∘(ac))∘a² + (c∘(ab))∘a² = a∘((bc)∘a²) + b∘((ac)∘a²) + c∘((ab)∘a²)
```

- **First term**: `(a∘(bc))∘a² = a∘((bc)∘a²)` by Jordan identity ✓
- **Second term**: `(b∘(ac))∘a²` vs `b∘((ac)∘a²)` - NOT Jordan (outer=b, square=a²)
- **Third term**: Same issue with c

The "deviation from Jordan" terms must cancel in the SUM, but direct proof is non-trivial.

### 2. Research Agent Findings (aa3a583)
Direct algebraic expansion of fundamental formula is **NOT feasible**:
- ~12-16 terms on each side after full expansion
- Term structures fundamentally different between LHS and RHS
- Estimated **70-95 LOC** of intermediate lemmas needed

**Required intermediate lemmas**:
1. Linearized Jordan identity (have in OperatorIdentities.lean)
2. Operator commutator: `[L_{a²}, L_b] = 2 L_a ∘ [L_a, L_b]`
3. Cross-Jordan identity for mixed terms

### 3. Updated Research Issue
Updated **af-bk8q** with detailed structural analysis findings.

---

## Current State

### Jordan Algebra Project
- **28 files, ~3600 LOC total**
- **21 sorries remaining** (across 9 files)

### Sorry Counts by File
| File | Sorries | Notes |
|------|---------|-------|
| FundamentalFormula.lean | 2 | linearized_jordan_aux, fundamental_formula |
| Peirce.lean | 7 | Peirce multiplication rules |
| FormallyReal/Def.lean | 3 | Abstract case (of_sq_eq_zero) |
| Primitive.lean | 3 | Primitive idempotents |
| OperatorIdentities.lean | 2 | L_e_L_a_L_e, opComm_double_idempotent |
| FormallyReal/Spectrum.lean | 1 | spectral_sq_eigenvalues_nonneg |
| Quadratic.lean | 1 | U_idempotent_comp |
| SpinFactor/FormallyReal.lean | 1 | |
| Quaternion/FormallyReal.lean | 1 | |

### Key Blocker: Fundamental Formula
```
fundamental_formula (sorry)
    ↓
linearized_jordan_aux (sorry - hard)
    ↓
U_jsq → U_idempotent_comp' → Peirce identities
```

---

## Next Steps: Operator Calculus Approach

Three issues created with dependency chain (~70-95 LOC total):

### Step 1: af-gmzr (Ready to work)
**Prove operator commutator identity**
```lean
[L_{a²}, L_b] = 2 L_a ∘ [L_a, L_b]
```
- Use `linearized_jordan_jmul` + Mathlib's `two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add`
- File: `OperatorIdentities.lean`
- Est: 15-20 LOC

### Step 2: af-dmot (Blocked by af-gmzr)
**Prove linearized_jordan_aux via deviation cancellation**
```lean
(a∘(bc))∘a² + (b∘(ac))∘a² + (c∘(ab))∘a² = a∘((bc)∘a²) + b∘((ac)∘a²) + c∘((ab)∘a²)
```
- First term: Jordan identity ✓
- Remaining: Show D(b,ac) + D(c,ab) = 0 using operator commutator
- File: `FundamentalFormula.lean`
- Est: 20-30 LOC

### Step 3: af-secn (Blocked by af-dmot)
**Prove fundamental_formula using operator calculus**
```lean
∀ x, U (U a b) x = U a (U b (U a x))
```
- Express via `U_a = 2L_a² - L_{a²}`
- Manipulate commutators using Steps 1-2
- File: `FundamentalFormula.lean`
- Est: 20-30 LOC
- **Unblocks ~10 sorries**

---

## Research Issue

**af-bk8q** - Deep research: Fundamental Formula proof strategies (P1)

Contains:
- Literature analysis (MacDonald's theorem, McCrimmon)
- Mathlib lemma inventory
- Direct expansion complexity analysis (~70-95 LOC estimate)
- Structural analysis showing why linearized_jordan_aux is hard

---

## Files Examined This Session

- `AfTests/Jordan/FundamentalFormula.lean` - Analyzed goal structure
- `AfTests/Jordan/Quadratic.lean` - U operator definition
- `AfTests/Jordan/OperatorIdentities.lean` - Existing linearized lemmas
- `AfTests/Jordan/Peirce.lean` - Peirce multiplication sorries

---

## Technical Reference

### The Structural Mismatch
```
linearized_rearranged: x ∘ (Y ∘ a²) ↔ Y ∘ (x ∘ a²)   [order swap]
linearized_jordan_aux: (x ∘ Y) ∘ a² ↔ x ∘ (Y ∘ a²)   [reassociation]
```

These are DIFFERENT operations. The first term of `linearized_jordan_aux`
follows from Jordan identity, but remaining terms need sum-level cancellation.

### Mathlib Lemmas Available
- `IsJordan.lmul_comm_rmul_rmul` - Jordan identity
- `commute_lmul_lmul_sq` - L_a commutes with L_{a²}
- `two_nsmul_lie_lmul_lmul_add_add_eq_zero` - Cyclic linearization
- `two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add` - Two-variable form

---

## Previous Sessions

### Session 51 (2026-01-30)
- Linearized Jordan identity lemmas added to OperatorIdentities.lean
- Created research issue af-bk8q

### Session 50 (2026-01-30)
- FormallyRealJordan direct proofs for SpinFactor, Quaternion

### Session 49 (2026-01-30)
- IsCommJordan bridge + OperatorIdentities build fix
