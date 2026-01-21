# Handoff: 2026-01-21 (Session 37)

## Completed This Session

### Fixed j=-2 Case in Case2_Correct.lean
- Fixed the proof that handles j = -2 orbit position (lines 239-256)
- Key technique: Used `congrFun (congrArg (⇑) h_eq)` to convert permutation equality to element application
- Proof shows g₁⁻²(3) = 0 using composition of g₁_inv_elem3_eq_elem5 and g₁_inv_elem5_eq_elem0

### Added Helper Lemmas in OrbitContinuation.lean
- `g₁_pow2_inv_elem3_eq_elem0`: (g₁^2)⁻¹(3) = 0
- `g₁_zpow2_inv_elem3_eq_elem0`: Same for zpow form

---

## Current State

### Build Status: PASSING

### Sorry Count: 8 total (excluding known false theorem)
| Location | Description | Status |
|----------|-------------|--------|
| Lemma11_5_SymmetricMain.lean:159 | Primitivity (k≥2 case) | Original |
| Lemma11_5_SymmetricMain.lean:181 | Primitivity (m≥2 case) | Original |
| Lemma11_5_Case2_Helpers.lean:155 | FALSE FOR n≥3 (known bug) | Do not use |
| Lemma11_5_Case2_Correct.lean:193 | h4_in_B₁ | Needs proof |
| Lemma11_5_Case2_Correct.lean:197 | h0_or_tailB_in_g₂B₁ | Needs proof |
| Lemma11_5_Case2_Correct.lean:218 | g₂(y)≠6 | Needs proof |
| Lemma11_5_Case2_Correct.lean:223 | k≥1 tailB case | Needs proof |
| Lemma11_5_Case2_Correct.lean:263 | j≤-3 orbit case | Needs proof |

### Axiom Count: 5 (FORBIDDEN)
All in `AfTests/ThreeCycle/Case1FixedPointLemmas.lean`:
- `sq_fixes_0`, `sq_fixes_1`, `sq_fixes_2`
- `sq_fixes_tailA`, `sq_fixes_tailC`

---

## Case2_Correct.lean Proof Structure

The correct Case 2 proof uses block B₁ containing element 1:

1. **Find B₁**: The block containing element 1
2. **g₁ fixes B₁**: Since g₁(1) = 1, by block_fixed_of_fixed_point
3. **Case split on supp(g₁) vs B₁**:
   - **supp(g₁) ⊆ B₁**: Then a₁ ∈ B₁ ≠ B (since 1 ∈ B₁ but 1 ∉ B), contradiction
   - **supp(g₁) ∩ B₁ = ∅**: Then g₂(B₁) contains 3 ∈ supp(g₁)
     - If g₁ preserves g₂(B₁): supp(g₁) ⊆ g₂(B₁), so a₁ ∈ g₂(B₁) ≠ B
     - If g₁ doesn't preserve g₂(B₁): Orbit continuation argument

4. **Orbit continuation**: The orbit of g₂(B₁) under g₁ covers supp(g₁). Since a₁ ∈ supp(g₁), a₁ must be in some orbit block C. Either C = B or C ≠ B:
   - **C ≠ B**: a₁ ∈ C ∩ B contradicts partition disjointness
   - **C = B**: Then B is at some orbit position j
     - **j = 0**: B = g₂(B₁) contains 3 (core), contradicting B ⊆ tailA ✓
     - **j = 1**: B = g₁(g₂(B₁)) contains 2 (core), contradicting B ⊆ tailA ✓
     - **j ≥ 2**: SORRY - Need partition overlap argument
     - **j = -1**: B contains 5 (core via g₁⁻¹(3) = 5), contradiction ✓
     - **j = -2**: B contains 0 (core via g₁⁻²(3) = 0), contradiction ✓
     - **j ≤ -3**: SORRY - Partition overlap argument needed

### Remaining Work for j≥2 and j≤-3

**For j ≥ 2** (lines 178-223):
1. Need to prove 4 ∈ B₁ given B₁ ∩ supp(g₁) = ∅
2. Then g₂(4) = 0 (when k=0) or tailB element (when k≥1)
3. Show partition overlap between orbit positions

**For j ≤ -3** (line 263):
- Use partition overlap: positions j and j+2 share element g₁^j(3)
- Since g₁² doesn't preserve g₂(B₁), these are different blocks
- Shared element contradicts partition disjointness

---

## Known Issues

### 1. Case2_Helpers.lean:155 is FALSE
The old `case2_B_ncard_le_one` theorem is false for n ≥ 3. This is marked as a BUG and should NOT be used. Use `Case2_Correct.lean` instead.

### 2. Five Forbidden Axioms in Case1FixedPointLemmas.lean
**MUST BE ELIMINATED** - These are computational lemmas that should be provable with `native_decide` or explicit cycle computations.

### 3. Case2FixedPointLemmas.lean Exceeds 200 LOC (702 lines)
Needs refactoring into smaller files.

---

## Files Modified This Session
- AfTests/Primitivity/Lemma11_5_OrbitContinuation.lean (MODIFIED - added g₁_pow2_inv helper)
- AfTests/Primitivity/Lemma11_5_Case2_Correct.lean (MODIFIED - fixed j=-2 case)
- HANDOFF.md (UPDATED)

---

## Next Session Priority

1. **P1: Complete j≥2 proofs** in Case2_Correct.lean (h4_in_B₁, h0_or_tailB, g₂(y)≠6, k≥1 case)
2. **P1: Complete j≤-3 proof** in Case2_Correct.lean
3. **P1: Wire case2_correct** into main Lemma11_5.lean
4. **P0: ELIMINATE THE 5 AXIOMS** in Case1FixedPointLemmas.lean
5. **P2: Eliminate sorries in SymmetricMain.lean** (k≥2, m≥2 cases)

---

## Session Close Checklist
- [x] Build passes
- [x] HANDOFF.md updated with full details
- [ ] Changes committed and pushed
