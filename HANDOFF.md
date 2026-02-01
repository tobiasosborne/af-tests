# Handoff: 2026-02-01 (Session 117)

## Session Summary

**PROGRESS:** Added detailed 12-step proof sketch for `orthogonal_primitive_peirce_sq`.

**Key insight:** The proof requires showing that for orthogonal primitives e, f and a ∈ P₁₂(e) ∩ P₁₂(f):
1. jsq a ∈ P₁(e+f) (since jmul (e+f) a = a)
2. jsq a = r₁•e + r₂•f (no P₀(e)∩P₀(f) component)
3. r₁ = r₂ (via fundamental formula: U_a(U_a(e)) = r₁r₂•e = r₁²•e)
4. r₁ ≥ 0 (by formal reality, H-O 2.9.4(vi))

**Result:** Build passes. 4 sorries remain but proof strategy is complete.

---

## Current State

| Metric | Value |
|--------|-------|
| Total Sorries | **4** (Primitive.lean) |
| Build Status | **PASSING** |
| Key Progress | Complete proof sketch for line 1119 |

---

## Remaining Sorries in Primitive.lean

| Line | Name | Goal | Status |
|------|------|------|--------|
| 1131 | `orthogonal_primitive_peirce_sq` | `∃ μ, 0 ≤ μ ∧ jsq a = μ • (e + f)` | **Proof sketch complete** |
| 1147 | `orthogonal_primitive_structure` | Dichotomy: trivial 1/2-space or strongly connected | Needs line 1131 |
| 1221 | `exists_primitive_decomp` | Induction case for primitive decomposition | Design decision |
| 1228 | `csoi_refine_primitive` | Refine CSOI to primitives | Needs line 1221 |

---

## Proof Sketch for `orthogonal_primitive_peirce_sq` (Line 1131)

The 12-step proof is documented in the code. Key steps:

### Part A: Structure (Steps 4-10)
- f ∈ P₀(e), e ∈ P₀(f) (orthogonality)
- jmul f (jsq a) = jmul f c₀e = r₂ • f
- jmul e (jsq a) = jmul e c₀f = r₁ • e
- e + f is idempotent (orthogonal sum)
- a ∈ P₁(e+f) since jmul (e+f) a = a
- jsq a ∈ P₁(e+f) by peirce_mult_P1_P1
- P₀(e) ∩ P₀(f) ⊆ P₀(e+f), so jsq a = r₁•e + r₂•f

### Part B: Equality r₁ = r₂ (Step 11)
- U_a(e) = {a,e,a} = 2 jmul a (jmul e a) - jmul (jsq a) e = jsq a - r₁•e = r₂•f
- U_a(f) = r₁•e (by symmetry)
- Fundamental formula: U_a(U_a(e)) = U_{jsq a}(e)
- LHS: U_a(r₂•f) = r₂ U_a(f) = r₁r₂•e
- RHS: U_{r₁e+r₂f}(e) = r₁²•e (after computation)
- Therefore r₁r₂ = r₁², and similarly r₁r₂ = r₂²
- Hence r₁ = r₂ (both ≥ 0)

### Part C: Non-negativity (Step 12)
- jsq a is a square, so by H-O 2.9.4(vi), coefficients ≥ 0
- Alternatively: if r₁ < 0, then jsq a + |r₁|•(e+f) = 0 contradicts formal reality

### Missing Lemmas Needed
1. `orthogonal_sum_isIdempotent` - sum of orthogonal idempotents is idempotent
2. `IsIdempotent.jmul_self` or equivalent accessor
3. Peirce space membership simplifications (`0 • x = 0`, `1 • x = x`)
4. Fundamental formula (has sorry in FundamentalFormula.lean:56)

---

## For Next Agent

**Recommended approach:**
1. First prove helper lemma `orthogonal_sum_isIdempotent`
2. Fix the Peirce space membership issues (eigenvalues use `λ • x` form)
3. Implement the proof step by step, testing each step

**Alternative:** The fundamental formula has a sorry - could use a direct symmetry argument instead.

---

## File Locations

| Item | Location |
|------|----------|
| `orthogonal_primitive_peirce_sq` | Primitive.lean:1097 |
| `fundamental_formula` (sorry) | FundamentalFormula.lean:56 |
| Peirce multiplication rules | Peirce.lean |

---

## Session Close Checklist

- [x] BUILD PASSES
- [x] HANDOFF.MD UPDATED
- [ ] bd close → bd sync
- [ ] git commit → git push
