# Handoff: 2026-01-30 (Session 51)

## Completed This Session

### Linearized Jordan Identity Lemmas

Added three new proven theorems to `OperatorIdentities.lean`:

| Theorem | Purpose |
|---------|---------|
| `linearized_on_jsq` | Linearized Jordan identity evaluated at a² |
| `linearized_core` | Same without factor of 2 |
| `linearized_rearranged` | Rearranged sum form |

These prove identities relating `x ∘ (Y ∘ a²)` to `Y ∘ (x ∘ a²)` using the
mathlib theorem `two_nsmul_lie_lmul_lmul_add_add_eq_zero`.

### Key Finding: `linearized_jordan_aux` Structure Mismatch

Investigated the `linearized_jordan_aux` theorem in FundamentalFormula.lean.
Found that it has a different structure than what `linearized_rearranged` provides:

- **`linearized_rearranged`**: relates `x ∘ (Y ∘ a²)` to `Y ∘ (x ∘ a²)` (swap order)
- **`linearized_jordan_aux`**: relates `(x ∘ Y) ∘ a²` to `x ∘ (Y ∘ a²)` (reassociate)

The first term of `linearized_jordan_aux` follows from Jordan identity directly.
The remaining terms need a different proof approach.

---

## Current State

### Jordan Algebra Project
- **28 files, ~3600 LOC total**
- **18 sorries remaining**

### Sorries by File
| File | Sorries | Notes |
|------|---------|-------|
| Peirce.lean | 7 | Multiplication rules |
| FormallyReal/Def.lean | 2 | Abstract case (needs spectral) |
| OperatorIdentities.lean | 2 | L_e_L_a_L_e, opComm_double_idempotent |
| FundamentalFormula.lean | 2 | linearized_jordan_aux, fundamental_formula |
| Spectrum.lean | 1 | Eigenvalue properties |
| Quadratic.lean | 1 | Depends on fundamental_formula |
| Primitive.lean | 3 | Primitive idempotents |

### Dependency Chain (Key Blocker)
```
fundamental_formula (sorry)
    ↓
U_jsq (proven, uses fundamental_formula)
    ↓
U_idempotent_comp' (proven)
    ↓
peirce_polynomial_identity (sorry)
    ↓
Peirce multiplication rules (7 sorries)
```

---

## Next Steps

### Option 1: Alternative Fundamental Formula Proof
The current approach through `linearized_jordan_aux` has structural issues.
Consider:
- Direct algebraic expansion (lengthy but straightforward)
- Different linearization substitutions
- Check literature for alternative proof strategies

### Option 2: Work on Non-Blocking Issues
- Ready tasks from `bd ready` (new files, less critical)
- Primitive.lean sorries (may be independent)

### Option 3: Accept Abstract Gaps
- Mark fundamental_formula dependency chain as "needs spectral theory"
- Focus on concrete type completeness (already good)

---

## Files Modified This Session

- `AfTests/Jordan/OperatorIdentities.lean` - Added 3 new lemmas
- `docs/Jordan/LEARNINGS.md` - Documented linearized identity findings
- `HANDOFF.md` - This file

---

## Technical Notes

### Using Mathlib's Linearized Jordan Identity

```lean
-- Access via IsCommJordan bridge
have h := linearized_jordan_jmul a b c
-- Type: 2 • (⁅mulLeft a, mulLeft (b*c)⁆ + ...) = 0

-- Apply to specific element (e.g., jsq a)
have happ := congrFun (congrArg DFunLike.coe h) (jsq a)

-- Unfold Lie bracket at AddMonoid.End level
-- Each ⁅f, g⁆ x = f(g(x)) - g(f(x)) by rfl
```

### Why linarith Doesn't Work on Module Elements

Module operations like `jmul` are not in ℝ, so `linarith` fails.
Use `sub_eq_zero.mp` instead:
```lean
have h' : X - Y = 0 := by convert h using 1; abel
exact sub_eq_zero.mp h'
```

---

## Previous Sessions

### Session 50 (2026-01-30)
- FormallyRealJordan direct proofs for SpinFactor, Quaternion

### Session 49 (2026-01-30)
- IsCommJordan bridge + OperatorIdentities build fix
