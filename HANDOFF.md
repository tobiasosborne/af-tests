# Handoff: 2026-01-21 (Session 42)

## Completed This Session

### Filled j≤-3 x=4 Sorry in Case2_Correct.lean
- Fixed the sorry at line 343 (now at different line after edits)
- Used block overlap argument at element 0
- Key fix: `Equiv.image_symm_image` for `e '' (e.symm '' s) = s`
- Required `conv_lhs` tactic to rewrite only left side

### Eliminated Sorries (Reduced from 6 to 3)
- Removed `orbit_ge2_has_core` (unused)
- Removed `orbit_le_neg3_impossible` (unused)
- Filled j≤-3 x=4 case proof

### Created Plan for SymmetricMain Sorries
- **Location**: `AfTests/Primitivity/PLAN_SYMMETRIC_MAIN.md`
- **Critical finding**: Theorem missing explicit block hypothesis
- **Proof strategy**: Use g₂ʲ orbit analysis with block dichotomy

---

## Current State

### Build Status: PASSING ✓

### Axiom Count: 0 (all eliminated!)

### Sorry Count: 3 total (including 1 known false)
| Location | Description | Status |
|----------|-------------|--------|
| Lemma11_5_Case2_Helpers.lean:155 | FALSE FOR n≥3 | Do not use |
| Lemma11_5_SymmetricMain.lean:159 | Primitivity (k≥2 case) | **See PLAN_SYMMETRIC_MAIN.md** |
| Lemma11_5_SymmetricMain.lean:181 | Primitivity (m≥2 case) | **See PLAN_SYMMETRIC_MAIN.md** |

---

## Key Technical Insight (CRITICAL)

### The SymmetricMain Theorems Need Block Property

The theorems `case2_impossible_B` and `case2_impossible_C` do NOT explicitly include a "B is a block" hypothesis, but the proof REQUIRES this property.

**Problem**: For k=3, the set B = {6+n, 6+n+2} satisfies all stated hypotheses:
- g₂(B) ∩ B = ∅ ✓
- b₁ ∈ B ✓
- g₁(B) = B ✓
- g₃(B) = B ✓
- |B| > 1 ✓

**But**: B is NOT a valid block because g₂²(B) ∩ B ≠ ∅ and g₂²(B) ≠ B.

**Solution**: The calling context in Lemma11_5.lean provides B from a block system. The proof must:
1. Either add an explicit block hypothesis
2. Or derive the g₂ʲ dichotomy from the H-invariance

See `PLAN_SYMMETRIC_MAIN.md` for full analysis and implementation options.

---

## Files Modified This Session
- `AfTests/Primitivity/Lemma11_5_Case2_Correct.lean` (MODIFIED - filled j≤-3 x=4)
- `AfTests/Primitivity/PLAN_SYMMETRIC_MAIN.md` (NEW - detailed plan)
- `HANDOFF.md` (UPDATED)

---

## Next Session Priority

### Task 1: Implement SymmetricMain.lean Fixes (P1)

Follow the plan in `PLAN_SYMMETRIC_MAIN.md`:

1. **Choose implementation option** (recommend Option A: add block hypothesis)
2. **Update theorem signature** in SymmetricMain.lean
3. **Update call site** in Lemma11_5.lean
4. **Implement k≥2 proof** using orbit analysis:
   - Show 6+n+1 ∉ B
   - Find j ≥ 2 with 6+n+j ∈ B
   - Use block property: g₂ʲ(B) = B
   - Derive contradiction via tailB exit
5. **Port to m≥2 case** (symmetric)

### Task 2: Refactor Case2_Correct.lean (P2)

File currently ~400+ lines, exceeds 200 LOC limit.

Suggested split:
- `Case2_Correct_Core.lean`: Main theorem structure
- `Case2_Correct_Orbit.lean`: Orbit analysis lemmas
- `Case2_Correct_JCases.lean`: j≥2 and j≤-3 case proofs

### Task 3: Clean Up Known-False Theorem (P3)

Consider adding clear documentation or removing the false theorem in Case2_Helpers.lean:155 to prevent accidental use.

---

## Dependency Graph

```
Task 1 (SymmetricMain) ──> Task 2 (Refactor Case2_Correct)
                     │
                     └──> Task 3 (Clean up false theorem)
```

---

## Session Close Checklist
- [x] Build passes
- [x] HANDOFF.md updated with full details
- [x] PLAN_SYMMETRIC_MAIN.md created with granular steps
- [ ] Changes committed and pushed
