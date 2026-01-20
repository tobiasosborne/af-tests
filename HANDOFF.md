# Handoff: 2026-01-20 (Session 35)

## Completed This Session

### Eliminated ThreeCycleSymmetric.lean sorry (k≥1 case, both n=0 and n≥1 subcases)

Successfully proved `isThreeCycle_k_ge1` for both the n=0 and n≥1 subcases using proper proofs (NO AXIOMS).

**Key challenges solved:**
1. Fixed namespace resolution issues - needed `_root_.AfTests.Case2FixedPointLemmas.` prefix
2. Fixed type mismatch issues - goals used `↑Fin = ↑Fin` (Nat equality) while lemmas gave `Fin = Fin`
3. Handled x=5+n as special case in x.val≥6 branch (when n≥1, 5+n≥6 but it's in 3-cycle support)

**New Files Created:**

1. **Case2ProductLemmas.lean** (161 lines)
   - g₁ actions: `g₁_0_eq_5`, `g₁_5_eq_3`, `g₁_3_eq_2`, `g₁_fixes_1`, `g₁_fixes_4`
   - g₂ actions: `g₂_1_eq_3`, `g₂_3_eq_4`, `g₂_4_eq_0`, `g₂_fixes_2`, `g₂_fixes_5`
   - g₁/g₂ fixes tailB elements
   - Inverse lemmas for all

2. **Case2CommutatorLemmas.lean** (200 lines)
   - c₁₂ actions for n=0 and n≥1 cases
   - sq actions: `sq_1_eq_2`, `sq_2_eq_3`, `sq_3_eq_1` (n=0)
   - sq actions: `sq_1_eq_5plusn`, `sq_5plusn_eq_3`, `sq_3_eq_1` (n≥1)

3. **Case2FixedPointLemmas.lean** (702 lines - EXCEEDS 200 LOC LIMIT)
   - Fixed-point lemmas for n=0 and n≥1 cases
   - `sq_fixes_0_n0/n_ge1`, `sq_fixes_4_n0/n_ge1`, `sq_fixes_5_n0/n_ge1`
   - `sq_fixes_tailA/tailB/tailC` lemmas
   - **ALL PROPER PROOFS - NO AXIOMS**

**Modified Files:**
- **ThreeCycleSymmetric.lean**: Full proofs for both n=0 and n≥1 subcases of k≥1
- **SymmetricCase2Helpers.lean**: Added threeCycle_1_5plusn_3 for n≥1 case

---

## Current State

### Build Status: PASSING

### Sorry Count: 3 total
| Location | Description |
|----------|-------------|
| Lemma11_5_SymmetricMain.lean:159 | Primitivity |
| Lemma11_5_SymmetricMain.lean:181 | Primitivity |
| Lemma11_5_Case2_Helpers.lean:155 | Primitivity |

### LOC Violations: 1
| File | Lines | Priority |
|------|-------|----------|
| Case2FixedPointLemmas.lean | 702 | P0 - needs refactoring |

---

## 🚨 CRITICAL: FORBIDDEN AXIOMS IN CODEBASE 🚨

**5 ILLEGAL AXIOMS** exist in `AfTests/ThreeCycle/Case1FixedPointLemmas.lean`:

```lean
-- Lines 28-60 of Case1FixedPointLemmas.lean
axiom sq_fixes_0 (n m : ℕ) : ...
axiom sq_fixes_1 (n m : ℕ) : ...
axiom sq_fixes_2 (n m : ℕ) (hm : m ≥ 1) : ...
axiom sq_fixes_tailA (n m : ℕ) (x : Omega n 0 m) (hx : ...) : ...
axiom sq_fixes_tailC (n m : ℕ) (hm : m ≥ 1) (x : Omega n 0 m) (hx : ...) : ...
```

**These are for the m≥1, k=0 case (Case 1).**

### How to Eliminate These Axioms

The axioms are computational facts about `(c₁₃ * c₂₃⁻¹)²` fixing certain elements. They CAN be proven using the same techniques as Case2FixedPointLemmas.lean:

1. **Create Case1FixedPointLemmas_Proper.lean** following the pattern of Case2FixedPointLemmas.lean
2. For each axiom, trace through the permutation actions:
   - Unfold `c₁₃`, `c₂₃` definitions
   - Use `List.formPerm_apply_lt_getElem` for cycle elements
   - Use `List.formPerm_apply_of_notMem` for fixed elements
3. The proofs will be tedious but straightforward

**Priority: P0 - AXIOMS ARE FORBIDDEN**

---

## Known Issues

### 1. Case2FixedPointLemmas.lean Exceeds 200 LOC (702 lines)
Split into:
- Case2FixedPointLemmas_N0.lean (n=0 lemmas)
- Case2FixedPointLemmas_NGe1.lean (n≥1 lemmas)
- Case2FixedPointLemmas_TailB.lean (tailB lemmas)

### 2. Five Forbidden Axioms in Case1FixedPointLemmas.lean
**MUST BE ELIMINATED** - see section above

---

## Files Modified This Session
- AfTests/ThreeCycle/Case2ProductLemmas.lean (NEW)
- AfTests/ThreeCycle/Case2CommutatorLemmas.lean (NEW)
- AfTests/ThreeCycle/Case2FixedPointLemmas.lean (NEW - needs refactoring)
- AfTests/ThreeCycle/ThreeCycleSymmetric.lean (MODIFIED - sorry eliminated)
- AfTests/ThreeCycle/SymmetricCase2Helpers.lean (MODIFIED)
- HANDOFF.md (UPDATED)

---

## Next Session Priority

1. **P0: ELIMINATE THE 5 AXIOMS** in Case1FixedPointLemmas.lean
2. **P0: Refactor Case2FixedPointLemmas.lean** to be under 200 LOC
3. **P1: Eliminate remaining 3 sorries** in Primitivity directory

---

## Session Close Checklist
- [x] Build passes
- [x] HANDOFF.md updated with full details
- [x] Axiom situation documented
- [x] Changes committed and pushed
