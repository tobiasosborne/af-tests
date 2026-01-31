# Handoff: 2026-01-31 (Session 83)

## Completed This Session

### Progress on af-fbx8: primitive_peirce_one_dim_one

Added helper lemma and restructured proof in `Primitive.lean`:

```lean
/-- Key lemma: If x ∈ P₁(e) satisfies x² = c • e for some c ≤ 0, then x = 0.
Uses formal reality: c < 0 contradicts sum of squares = 0, c = 0 gives x² = 0 → x = 0. -/
theorem peirce_one_sq_nonpos_imp_zero [FormallyRealJordan J]
    {e : J} (he : IsIdempotent e) (he_ne : e ≠ 0) {x : J} (_hx : x ∈ PeirceSpace e 1)
    {c : ℝ} (hc : c ≤ 0) (hsq : jsq x = c • e) : x = 0
```

**Proof technique:** When c < 0, construct sum of squares `jsq x + jsq (√(-c) • e) = 0` using
`jsq_smul_idem`. By formal reality, both terms must be zero, but `√(-c) • e ≠ 0`. Contradiction.

Also restructured `primitive_peirce_one_dim_one` with clearer proof outline using `Nat.le_antisymm`
and `Submodule.finrank_mono`.

---

## Current State

| Metric | Value |
|--------|-------|
| Total Sorries in Jordan/ | **26** (unchanged) |
| Build Status | PASSING |
| New items added | 1 proven helper lemma, proof restructuring |

---

## Remaining Work for af-fbx8

The main sorry is in `hle_span`:

```lean
have hle_span : (PeirceSpace e 1 : Submodule ℝ J) ≤ Submodule.span ℝ {e} := by
  intro x hx
  rw [Submodule.mem_span_singleton]
  -- For any x ∈ P₁(e), we show ∃ r, x = r • e
  sorry
```

**Proof strategy** (from LEARNINGS.md):
1. Powers of x stay in P₁(e) by `jpow_succ_mem_peirce_one`
2. By finite dimension, x satisfies a polynomial p(x) = 0
3. If p has complex roots → violates formal reality (construct y with y² < 0)
4. If p has repeated roots → nilpotent contradiction
5. If p has multiple distinct real roots → Lagrange idempotents contradict primitivity
6. So p(t) = c(t - λ), hence x = λe

**Key challenge:** Formalizing the Lagrange idempotent construction and showing it produces
non-trivial idempotents in P₁(e).

---

## Next Session Recommendations

1. **Complete af-fbx8** by implementing the polynomial argument:
   - Define minimal polynomial satisfaction (linear dependence of powers)
   - Handle repeated roots via `no_nilpotent_of_formallyReal`
   - Handle multiple distinct roots via Lagrange idempotent construction
   - Use `primitive_idempotent_in_P1` for the contradiction

   Estimated: ~50-80 LOC

2. **Alternative approach:** Use `peirce_one_sq_nonpos_imp_zero` more directly:
   - For x ∈ P₁(e), consider y = x - (some scalar)·e such that y² = c·e
   - Handle cases c ≤ 0 (use helper) and c > 0 (construct idempotent)

---

## Files Modified This Session

- `AfTests/Jordan/Primitive.lean` — Added `peirce_one_sq_nonpos_imp_zero`, restructured proof
- `HANDOFF.md` — This file

---

## Key Learnings

1. **Formal reality contradiction pattern:**
   ```lean
   -- To show jsq y = c•e with c < 0 is impossible:
   have hsum : jsq x + jsq (√(-c) • e) = 0 := by
     rw [hsq, jsq_smul_idem he, Real.sq_sqrt ..., ← add_smul, add_neg_cancel, zero_smul]
   -- Apply FormallyRealJordan.sum_sq_eq_zero with vector ![x, √(-c) • e]
   ```

2. **Matrix vector access:** `![a, b] 1` simplifies via `Matrix.cons_val_one` to `![b] 0`,
   then via `Matrix.cons_val_zero` to `b`.

3. **Submodule finrank equality:** Use `Nat.le_antisymm` with `Submodule.finrank_mono` in
   both directions, rather than trying to directly rewrite on the submodule.
