# Handoff: 2026-02-01 (Session 116)

## Session Summary

**PROGRESS:** Fixed the instance diamond in `h_finrank_one` (Primitive.lean:~1007).

**Solution:** Used `Real.nonempty_algEquiv_or` directly with explicit instance management:
- `letI hAlg := P1PowerSubmodule_algebra` brings in algebra structure
- `haveI hFD := P1PowerSubmodule_finiteDimensional` provides finite-dimensionality
- Case split on whether P1PowerSubmodule ≃ₐ[ℝ] ℝ or ≃ₐ[ℝ] ℂ
- ℂ case excluded by `P1PowerSubmodule_formallyReal`
- ℝ case gives finrank = 1 via `eqv.toLinearEquiv.finrank_eq`

**Result:** Build passes. 4 sorries remain in Primitive.lean (down from 5).

---

## Current State

| Metric | Value |
|--------|-------|
| Total Sorries | **4** (Primitive.lean) |
| Build Status | **PASSING** |
| Key Fix | Instance diamond resolved via explicit instances |

---

## Remaining Sorries in Primitive.lean

| Line | Name | Goal | Blocker |
|------|------|------|---------|
| 1119 | `orthogonal_primitive_peirce_sq` | `∃ μ, 0 ≤ μ ∧ jsq a = μ • (e + f)` | Algebraic computation |
| 1131 | `orthogonal_primitive_structure` | Dichotomy: trivial 1/2-space or strongly connected | Needs line 1119 |
| 1205 | `exists_primitive_decomp` | Induction case for primitive decomposition | Design decision |
| 1212 | `csoi_refine_primitive` | Refine CSOI to primitives | Needs line 1205 |

---

## Key Fix Details (Session 116)

### The Problem
When calling `formallyReal_field_is_real`, Lean couldn't unify:
- `FiniteDimensional` proved with `(P1PowerSubmodule e x).module`
- `FiniteDimensional` required by theorem with `Algebra.toModule`

### The Solution
Instead of using the existing `formallyReal_field_is_real`, we replicate its logic inline:

```lean
letI hAlg : Algebra ℝ ↥(P1PowerSubmodule e x) := P1PowerSubmodule_algebra e x he.isIdempotent hx
haveI hFD : FiniteDimensional ℝ ↥(P1PowerSubmodule e x) :=
  P1PowerSubmodule_finiteDimensional e x he.isIdempotent hx
cases Real.nonempty_algEquiv_or ↥(P1PowerSubmodule e x) with
| inl hR => -- Use eqv.toLinearEquiv.finrank_eq to get finrank = 1
| inr hC => -- Contradiction via P1PowerSubmodule_formallyReal
```

Key insight: `Algebra.ofModule` (used by `P1PowerSubmodule_algebra`) reuses the existing module structure, so `FiniteDimensional` transfers correctly.

---

## For Next Agent

### Easiest Target: Line 1119 (`orthogonal_primitive_peirce_sq`)
Given:
- `c₁e = r₁ • e` (from `primitive_peirce_one_scalar`)
- `c₁f = r₂ • f` (from `primitive_peirce_one_scalar`)
- `c₀e + c₁e = jmul a a` and `c₀f + c₁f = jmul a a`
- `e, f` orthogonal primitives

Need to show: `∃ μ, 0 ≤ μ ∧ jsq a = μ • (e + f)`

**Proof sketch (Session 116 analysis):**
1. `e + f` is idempotent (need lemma: `orthogonal_sum_isIdempotent`)
2. `a ∈ P₁(e+f)` since `jmul (e+f) a = (1/2)a + (1/2)a = a`
3. `jsq a ∈ P₁(e+f)` by Peirce rule P₁×P₁⊆P₁
4. P₀(e)∩P₀(f) ⊆ P₀(e+f), disjoint from P₁(e+f)
5. Therefore `jsq a = r₁ • e + r₂ • f` (no P₀∩P₀ component)
6. **Key:** By symmetry of hypotheses in e↔f, also `jsq a = r₂ • e + r₁ • f`
7. Comparing: `(r₁-r₂)(e-f) = 0`, and e,f linearly independent ⟹ `r₁ = r₂`
8. **Non-negativity:** If `μ < 0`, form sum `jsq a + |μ|•e + |μ|•f = 0`, contradicting formal reality

**Missing lemmas needed:**
- `orthogonal_sum_isIdempotent : AreOrthogonal e f → IsIdempotent e → IsIdempotent f → IsIdempotent (e+f)`
- `jmul_add_left : jmul (a + b) c = jmul a c + jmul b c` (or use L_add)

### Medium: Line 1205 (`exists_primitive_decomp`)
Strong induction on dimension. The base case and non-primitive case are set up;
just need to apply inductive hypothesis to `f` and `e - f`.

---

## File Locations

| Item | Location |
|------|----------|
| `primitive_peirce_one_dim_one` | Primitive.lean:864 |
| `h_finrank_one` (FILLED) | Primitive.lean:~1007 |
| `orthogonal_primitive_peirce_sq` | Primitive.lean:1097 |
| `exists_primitive_decomp` | Primitive.lean:1173 |

---

## Session Close Checklist

- [x] BUILD PASSES
- [x] HANDOFF.MD UPDATED
- [ ] bd close → bd sync
- [ ] git commit → git push
