# Handoff: 2026-01-21 (Session 49)

## Build Status: ✅ PASSING

## Sorry Count: 3

All sorries are now at the "≥ 3" boundary (symmetric structure):
1. `case2_impossible` in `Lemma11_5_Case2.lean:242` (n ≥ 3 only - **n=1,2 now proven!**)
2. `case2_impossible_B` in `Lemma11_5_SymmetricCases.lean:531` (k ≥ 3 only - k=1,2 proven)
3. `case2_impossible_C` in `Lemma11_5_SymmetricCases.lean:690` (m ≥ 3 only - m=1,2 proven)

---

## Progress This Session

### Key Accomplishments

1. **Proved n = 1 case for `case2_impossible`**:
   - B ⊆ tailA (via support disjointness)
   - |tailA| = 1, so |B| ≤ 1, contradicting |B| > 1

2. **Proved n = 2 case for `case2_impossible`**:
   - B ⊆ tailA = {a₁, a₂}
   - Since a₁ ∈ B and |B| > 1, must have a₂ ∈ B
   - g₁(a₁) = a₂ ∈ g₁(B), and a₂ ∈ B
   - So g₁(B) ∩ B ≠ ∅, contradicting g₁(B) disjoint from B

3. **Added hBlock hypothesis to `case2_impossible`**:
   - Signature now matches case2_impossible_B and case2_impossible_C
   - `hBlock : ∀ j : ℕ, (g₁ n k m ^ j) '' B = B ∨ Disjoint ((g₁ n k m ^ j) '' B) B`
   - Updated call site in Lemma11_5.lean to provide this hypothesis

### Mathematical Analysis (n ≥ 3 / k ≥ 3 / m ≥ 3)

For the ≥ 3 cases, the orbit analysis is more complex:

1. For small orbits (e.g., n=3, n=4): The orbit of a₁ under g₁^(i-1) hits a core element, contradicting B ⊆ tailA.

2. For special cases where orbit stays in tailA (e.g., n=6, B={a₁,a₆}):
   - g₁ powers satisfy the block condition for this B
   - But h = g₁⁻¹ * g₂ * g₁ gives h(B) = {a₁, element 1}
   - h(B) ∩ B = {a₁} ≠ ∅ and h(B) ≠ B
   - So B is NOT an H-block (requires full block condition for all h ∈ H)

**Note**: The current theorem signatures use hBlock for generator powers only. The full proof for ≥ 3 cases may need the complete H-block condition or a different approach.

---

## Current Sorry Status (All Symmetric at ≥ 3 Boundary)

### case2_impossible (Lemma11_5_Case2.lean:242)
- **n = 1**: ✅ Proven (cardinality argument)
- **n = 2**: ✅ Proven (direct disjointness)
- **n ≥ 3**: ⏳ Sorry (needs orbit analysis or full H-block)

### case2_impossible_B (Lemma11_5_SymmetricCases.lean:531)
- **k = 1**: ✅ Proven (cardinality argument)
- **k = 2**: ✅ Proven (j-1 = 1 forces g₂(B) = B, contradiction)
- **k ≥ 3**: ⏳ Sorry (symmetric to n ≥ 3)

### case2_impossible_C (Lemma11_5_SymmetricCases.lean:690)
- **m = 1**: ✅ Proven (cardinality argument)
- **m = 2**: ✅ Proven (j-1 = 1 forces g₃(B) = B, contradiction)
- **m ≥ 3**: ⏳ Sorry (symmetric to n ≥ 3)

---

## File Changes

### Modified Files
- `AfTests/Primitivity/Lemma11_5_Case2.lean` - Added n=1,2 proofs, hBlock hypothesis (~80 new lines)
- `AfTests/Primitivity/Lemma11_5.lean` - Updated call site to provide hBlock

### File Status
- **Lemma11_5_Case2.lean**: ~243 lines (⚠️ exceeds 200 LOC limit - needs refactoring)
- **Lemma11_5_SymmetricCases.lean**: ~690 lines (⚠️ exceeds 200 LOC limit)
- **Lemma11_5_Case2_Helpers.lean**: ~233 lines (⚠️ exceeds 200 LOC limit)

---

## Next Steps

1. **Complete ≥ 3 cases** (Priority: HIGH):
   - Option A: Formalize orbit analysis showing contradiction for most n/k/m values
   - Option B: Add full H-block hypothesis and use mixed products
   - Option C: Restructure proof to use block system structure directly

2. **Refactor large files** (Priority: MEDIUM):
   - Split Lemma11_5_Case2.lean (~243 lines)
   - Split SymmetricCases.lean (~690 lines)
   - Split Case2_Helpers.lean (~233 lines)

---

## Critical Notes

**All three variants now have the same symmetric structure:**
- Small cases (n/k/m ≤ 2): Proved via cardinality or direct computation
- Large cases (n/k/m ≥ 3): Require orbit analysis or full H-block condition

**DO NOT assume hBlock for generator powers is enough for ≥ 3 cases!**
The handoff example for k=6 shows that mixed products can violate the block condition even when generator powers satisfy it.

**Possible approaches for ≥ 3:**
1. Add more hypotheses capturing full H-invariance
2. Prove case-by-case that orbits hit core elements
3. Use the block SYSTEM structure (multiple blocks, partitions)
