# Handoff: 2026-01-22

## Build Status: PASSING

## Sorry Count: 3

---

## Progress This Session

**Created helper lemmas in `Lemma11_5_OrbitHelpers_Core.lean`:**
- `g₃_c₁_eq_c₂` (m ≥ 2): g₃(c₁) = c₂
- `g₃_c₂_eq_c₃` (m ≥ 3): g₃(c₂) = c₃
- `g₃_pow2_c₁_eq_c₃` (m ≥ 3): g₃²(c₁) = c₃

These are computational lemmas needed for the m >= 2 case (line 502 sorry).

---

## NEXT SMALLEST STEP

**Handle the m = 2 case separately OR proceed to implement Steps 1-4 of the plan**

The helper lemma `g₃_pow2_c₁_eq_c₃` requires m ≥ 3 (not m ≥ 2 as originally thought) because:
- c₃ needs to exist as a valid element (6+n+k+2 < 6+n+k+m requires m > 2)
- For m = 2, g₃²(c₁) = 2 (wraps around), not c₃

**Options:**
1. Create a separate lemma for m = 2 case: `g₃_pow2_c₁_eq_elem2`
2. Proceed with Steps 1-4 of the plan using case split on m = 2 vs m ≥ 3

---

## Implementation Plan

See **`AfTests/Primitivity/PLAN_M2_CASE.md`** for the full 4-step implementation plan for the m >= 2 case.

### Quick Summary of Steps:
1. **Find j** such that g₃^j(c₁) = 4 — all lemmas exist ✓
2. **Define B'** and establish properties — all lemmas exist ✓
3. **Show g₂(B') ≠ B'** — all lemmas exist ✓
4. **Find g₂-fixed element OR handle B' = {1, 4}** — needs helper lemmas

### Helper Lemmas Status:
- `g₃_c₁_eq_c₂` (m ≥ 2) — **DONE** ✓
- `g₃_c₂_eq_c₃` (m ≥ 3) — **DONE** ✓
- `g₃_pow2_c₁_eq_c₃` (m ≥ 3) — **DONE** ✓
- `g₃_pow2_c₁_eq_elem2` (m = 2) — not yet created

---

## Remaining Sorries (3)

| File | Line | Case | Difficulty | Blocker |
|------|------|------|------------|---------|
| `Lemma11_5_Case2.lean` | 322 | B' = {0,3} | HARDER | Needs g₁²(0)=3 |
| `Lemma11_5_SymmetricCases.lean` | 368 | k >= 2, B' = {0,3} | HARDER | Same as above |
| `Lemma11_5_SymmetricCases.lean` | 502 | m >= 2 | HARDER | See plan |

---

## Key Discovery This Session

**For m = 2 vs m ≥ 3:**
- m = 2: tailC = {c₁, c₂}, g₃²(c₁) = 2 (wraps to core)
- m ≥ 3: tailC has c₁, c₂, c₃, ..., g₃²(c₁) = c₃

This affects the B' = {1, 4} special case handling.

**supp(g₂) ∩ supp(g₃) = {1, 4}** (not just {4})

---

## Files Modified This Session

- `AfTests/Primitivity/Lemma11_5_OrbitHelpers_Core.lean` — Added 3 new helper lemmas
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
