# Handoff: 2026-01-30 (Session 51)

## Completed This Session

### 1. Linearized Jordan Identity Lemmas
Added three new proven theorems to `OperatorIdentities.lean`:

| Theorem | Purpose |
|---------|---------|
| `linearized_on_jsq` | Linearized Jordan identity evaluated at a² |
| `linearized_core` | Same without factor of 2 |
| `linearized_rearranged` | Rearranged sum form |

### 2. Deep Research Issue Created
Created **af-bk8q** (P1) with parallel subagent research on fundamental formula.

**Key Finding:** In quadratic Jordan algebra formulations, the fundamental
formula `U_{U_x(y)} = U_x U_y U_x` is taken as an **AXIOM**, not derived!

This explains why `linearized_jordan_aux` is difficult - we're trying to
derive what quadratic algebras axiomatize.

### 3. Structural Analysis
Found that `linearized_jordan_aux` has different structure than what
`linearized_rearranged` provides:
- `linearized_rearranged`: relates `x ∘ (Y ∘ a²)` to `Y ∘ (x ∘ a²)` (swap)
- `linearized_jordan_aux`: relates `(x ∘ Y) ∘ a²` to `x ∘ (Y ∘ a²)` (reassoc)

---

## Current State

### Jordan Algebra Project
- **28 files, ~3600 LOC total**
- **18 sorries remaining**

### Key Blocker: Fundamental Formula
```
fundamental_formula (sorry)
    ↓
U_jsq → U_idempotent_comp'
    ↓
peirce_polynomial_identity
    ↓
7 Peirce multiplication sorries
```

### Recommended Next Steps (from research)

1. **Axiomatize Route** (Fastest)
   - Add fundamental formula as axiom to `FormallyRealJordan`
   - Verify it holds for concrete instances (matrices, spin factors)
   - Unblocks ~10 sorries immediately

2. **Operator Calculus Route** (Medium)
   - Use mathlib's `commute_lmul_lmul_sq` and related lemmas
   - Build up operator identities systematically

3. **MacDonald Theorem Route** (Complete but long)
   - Polynomial identity theory for special Jordan algebras
   - Structure theory extension

---

## Open Research Issue

**af-bk8q** - Deep research: Fundamental Formula proof strategies (P1)

Contains detailed findings from parallel subagent research including:
- Literature analysis
- Mathlib lemma inventory
- Direct expansion complexity analysis
- Recommended approaches

---

## Files Modified This Session

- `AfTests/Jordan/OperatorIdentities.lean` - Added 3 new lemmas (+47 lines)
- `docs/Jordan/LEARNINGS.md` - Documented linearized identity findings
- `HANDOFF.md` - This file

---

## Technical Reference

### Using Mathlib's Linearized Jordan Identity
```lean
have h := linearized_jordan_jmul a b c
-- Type: 2 • (⁅mulLeft a, mulLeft (b*c)⁆ + ...) = 0
have happ := congrFun (congrArg DFunLike.coe h) (jsq a)
-- Unfolds to element-level identity
```

### Available Mathlib Commutation Lemmas
- `commute_lmul_lmul_sq` - L_a and L_{a²} commute
- `commute_lmul_rmul_sq` - L_a and R_{a²} commute
- `two_nsmul_lie_lmul_lmul_add_add_eq_zero` - Cyclic linearization

---

## Previous Sessions

### Session 50 (2026-01-30)
- FormallyRealJordan direct proofs for SpinFactor, Quaternion

### Session 49 (2026-01-30)
- IsCommJordan bridge + OperatorIdentities build fix
