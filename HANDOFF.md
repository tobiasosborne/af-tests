# Handoff: 2026-01-21 (Session 36)

## Completed This Session

### Fixed Build Errors in Case2_Correct.lean

Fixed `simp` errors in the orbit continuation proof for j=0 and j=1 cases:
- j=0: Used `rw [Int.ofNat_zero, zpow_zero, ...]` instead of `simp`
- j=1: Used explicit `have h1 : Int.ofNat (0 + 1) = (1 : ℤ) := rfl; rw [...]`

### Added Helper Lemmas in Lemma11_5_OrbitContinuation.lean

New lemmas for g₁ action analysis:
- `g₁_elem5_eq_elem3`: g₁(5) = 3
- `g₁_elem0_eq_elem5`: g₁(0) = 5
- `g₁_inv_elem3_eq_elem5`: g₁⁻¹(3) = 5
- `g₁_inv_sq_elem3_eq_elem0`: g₁⁻²(3) = 0
- `elem0_not_tailA`, `elem5_not_tailA`: 0, 5 are core elements (not in tailA)

---

## Current State

### Build Status: PASSING

### Sorry Count: 6 total
| Location | Description | Status |
|----------|-------------|--------|
| Lemma11_5_SymmetricMain.lean:159 | Primitivity (k≥2 case) | Original |
| Lemma11_5_SymmetricMain.lean:181 | Primitivity (m≥2 case) | Original |
| Lemma11_5_Case2_Helpers.lean:155 | FALSE FOR n≥3 (see bug) | Known bug |
| Lemma11_5_Case2_Correct.lean:179 | j≥2 orbit case | NEW |
| Lemma11_5_Case2_Correct.lean:186 | Negative j orbit case | NEW |

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
     - **j ≥ 2**: SORRY - Need cardinality/overlap argument
     - **j < 0**: SORRY - g₁⁻¹(3) = 5 (core), g₁⁻²(3) = 0 (core)

### Remaining Work for j≥2 and j<0

The key insight: For B₁ = {1, 4} (forced by constraints), g₂(B₁) = {3, 0}. The orbit of {3, 0} under g₁ cycles through all of supp(g₁).

For B ⊆ tailA:
- g₁ʲ(3) and g₁ʲ(0) must both be in tailA
- This restricts j to specific values depending on n
- For n ≤ 2: No such j ≥ 2 exists (all hit core elements)
- For n ≥ 3: Some j values exist but partition overlap argument applies

For negative j:
- j = -1: g₁⁻¹(3) = 5 (core) → contradiction
- j = -2: g₁⁻²(3) = 0 (core) → contradiction
- j ≤ -3: Similar pattern continues

---

## Known Issues

### 1. Case2_Helpers.lean:155 is FALSE
The old `case2_B_ncard_le_one` theorem is false for n ≥ 3. This is marked as a BUG and should NOT be used. Use `Case2_Correct.lean` instead.

### 2. Five Forbidden Axioms in Case1FixedPointLemmas.lean
**MUST BE ELIMINATED** - See previous session notes for proof strategy.

### 3. Case2FixedPointLemmas.lean Exceeds 200 LOC (702 lines)
Needs refactoring into smaller files.

---

## Files Modified This Session
- AfTests/Primitivity/Lemma11_5_OrbitContinuation.lean (MODIFIED - added helper lemmas)
- AfTests/Primitivity/Lemma11_5_Case2_Correct.lean (MODIFIED - fixed simp errors)
- HANDOFF.md (UPDATED)

---

## Next Session Priority

1. **P1: Complete j≥2 and j<0 proofs** in Case2_Correct.lean
2. **P1: Wire case2_correct** into main Lemma11_5.lean
3. **P0: ELIMINATE THE 5 AXIOMS** in Case1FixedPointLemmas.lean
4. **P0: Refactor Case2FixedPointLemmas.lean** to be under 200 LOC

---

## Session Close Checklist
- [x] Build passes
- [x] HANDOFF.md updated with full details
- [ ] Changes committed and pushed
