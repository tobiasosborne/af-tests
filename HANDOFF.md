# Handoff: 2026-01-22

## Build Status: PASSING

## Sorry Count: 3

---

## NEXT SMALLEST STEP

**Create helper lemma `g₃_pow2_c₁_eq_c₃`** in `Lemma11_5_OrbitHelpers_Core.lean`

This is a computational lemma needed for the m >= 2 case:
```lean
/-- g₃²(c₁) = c₃ for m ≥ 3 -/
theorem g₃_pow2_c₁_eq_c₃ (hm : m ≥ 3) :
    (g₃ n k m ^ (2 : ℕ)) (⟨6 + n + k, by omega⟩ : Omega n k m) =
    ⟨6 + n + k + 2, by omega⟩
```

**Why this is needed**: The m >= 2 case requires handling the special case B' = {1, 4}. To derive a contradiction, we need to show g₃²(c₁) = c₃ ∈ g₃²(B) ∩ B, violating the block disjointness condition.

**Implementation approach**: This is pure computation on the g₃ cycle. Can use `List.formPerm` reasoning similar to other element mapping lemmas.

---

## Implementation Plan

See **`AfTests/Primitivity/PLAN_M2_CASE.md`** for the full 4-step implementation plan for the m >= 2 case.

### Quick Summary of Steps:
1. **Find j** such that g₃^j(c₁) = 4 — all lemmas exist ✓
2. **Define B'** and establish properties — all lemmas exist ✓
3. **Show g₂(B') ≠ B'** — all lemmas exist ✓
4. **Find g₂-fixed element OR handle B' = {1, 4}** — needs helper lemmas

### Helper Lemmas Needed (for Step 4):
- `g₃_pow2_c₁_eq_c₃` — **NEXT STEP**
- `g₃_pow2_c₃` — after above

---

## Remaining Sorries (3)

| File | Line | Case | Difficulty | Blocker |
|------|------|------|------------|---------|
| `Lemma11_5_Case2.lean` | 322 | B' = {0,3} | HARDER | Needs g₁²(0)=3 |
| `Lemma11_5_SymmetricCases.lean` | 368 | k >= 2, B' = {0,3} | HARDER | Same as above |
| `Lemma11_5_SymmetricCases.lean` | 502 | m >= 2 | HARDER | See plan |

---

## Key Discovery This Session

**supp(g₂) ∩ supp(g₃) = {1, 4}** (not just {4})

This means element 1 is in BOTH supports, so the simple "find g₂-fixed point" argument fails when B' = {1, 4}. The plan handles this via block condition violation.

---

## Files Modified This Session

- `AfTests/Primitivity/Lemma11_5_SymmetricCases.lean` — Added import, documented approach
- `AfTests/Primitivity/PLAN_M2_CASE.md` — NEW: Detailed implementation plan
- `HANDOFF.md` — This file

---

## Verification Commands

```bash
# Build
lake build AfTests

# Check sorries
grep -rn "sorry" AfTests/Primitivity/ --include="*.lean"

# Check LOC
wc -l AfTests/Primitivity/Lemma11_5_*.lean | sort -n
```
