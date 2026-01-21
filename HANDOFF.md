# Handoff: 2026-01-21 (Session 40)

## Completed This Session

### Created OrbitHelpers.lean
- New file: `AfTests/Primitivity/Lemma11_5_OrbitHelpers.lean` (85 lines)
- Contains helper lemmas for orbit analysis:
  - `g₁_sq_elem0_eq_elem3`: g₁²(0) = 3
  - `g₂_elem4_eq_elem0'`: g₂(4) = 0 (for all k, not just k=0)
  - `g₁_pow_fixes_elem1`: g₁^j(1) = 1 for all j
  - `g₁_pow_fixes_tailB`: g₁^j(b) = b for tailB elements
  - Supporting lemmas for the orbit contradiction proofs

### Developed Detailed Proof Strategy for j ≥ 2 Case
Key insight: For the j ≥ 2 case in `case2_correct`, the proof uses:

1. **|B₁| > 1** (from |B| > 1 since g₁, g₂ are bijections)
2. **B₁ ⊆ {1, 4} ∪ tailB** (from B₁ ∩ supp(g₁) = ∅)
3. **Either 4 ∈ B₁ or tailB ∩ B₁ ≠ ∅** (since |B₁| > 1 and 1 ∈ B₁)

**Case 4 ∈ B₁:**
- g₂(4) = 0 ∈ g₂(B₁)
- g₁²(0) = 3 ∈ g₁²(g₂(B₁))
- 3 ∈ g₂(B₁) (from g₂(1) = 3)
- So 3 ∈ g₂(B₁) ∩ g₁²(g₂(B₁))
- If g₂(B₁) ≠ g₁²(g₂(B₁)): partition disjointness contradiction
- If g₂(B₁) = g₁²(g₂(B₁)): derive 6 = a₁ ∈ g₂(B₁), but 6 ∉ range(g₂|_{B₁})

**Case tailB ∩ B₁ ≠ ∅:**
- g₂ maps tailB cyclically: b₁→b₂→...→bₖ→1
- g₁ fixes tailB elements and 1
- So g₂(b) stays in C for all j ≥ 0
- But tailB ∩ tailA = ∅ and 1 ∉ tailA → contradiction

---

## Current State

### Build Status: PASSING

### Axiom Count: 0 (all eliminated!)

### Sorry Count: 7 total (including 1 known false)
| Location | Description | Status |
|----------|-------------|--------|
| Lemma11_5_SymmetricMain.lean:159 | Primitivity (k≥2 case) | Needs orbit analysis |
| Lemma11_5_SymmetricMain.lean:181 | Primitivity (m≥2 case) | Needs orbit analysis |
| Lemma11_5_Case2_Helpers.lean:155 | FALSE FOR n≥3 | Do not use |
| Lemma11_5_Case2_Correct.lean:103 | orbit_ge2_has_core | Strategy developed |
| Lemma11_5_Case2_Correct.lean:130 | orbit_le_neg3_impossible | Needs similar analysis |
| Lemma11_5_Case2_Correct.lean:221 | j≥2 orbit case | Strategy developed above |
| Lemma11_5_Case2_Correct.lean:237 | j≤-3 orbit case | Symmetric to j≥2 |

---

## Key Technical Insights

### g₂ Cycle Structure (IMPORTANT FIX)
- g₂CoreList = [1, 3, 4, 0] (NOT [1, 3, 0, 4]!)
- g₂ cycle: 1 → 3 → 4 → 0 → b₁ → b₂ → ... → bₖ → 1
- So g₂(4) = 0 for ALL k (not just k=0)
- The existing `g₂_elem4_eq_elem0` has hypothesis `hk : k = 0` which is unnecessary

### Orbit Structure of Element 3 under g₁
- g₁⁰(3) = 3 (core)
- g₁¹(3) = 2 (core)
- g₁²(3) = 6 = a₁ (tailA if n ≥ 1)
- g₁^(n+2)(3) = 0 (core)
- Period is 4+n

### Orbit Structure of Element 0 under g₁
- g₁⁰(0) = 0 (core)
- g₁¹(0) = 5 (core)
- g₁²(0) = 3 (core)
- g₁³(0) = 2 (core)
- g₁⁴(0) = 6 = a₁ (tailA if n ≥ 1)
- Period is 4+n

### Block B₁ Properties
- 1 ∈ B₁ (by definition)
- g₁(1) = 1, so g₁(B₁) = B₁
- Either supp(g₁) ⊆ B₁ (→ a₁ ∈ B₁ ≠ B) or B₁ ∩ supp(g₁) = ∅
- When B₁ ∩ supp(g₁) = ∅: B₁ ⊆ {1, 4} ∪ tailB

---

## Files Modified This Session
- `AfTests/Primitivity/Lemma11_5_OrbitHelpers.lean` (NEW - 85 lines)
- `HANDOFF.md` (UPDATED)

---

## Next Session Priority

1. **P1: Fill j≥2 sorry in Case2_Correct.lean (line 221)**
   - Use the detailed proof strategy above
   - Key helper lemmas already in OrbitHelpers.lean
   - Need to handle: size argument, overlap argument, tailB case

2. **P1: Fill j≤-3 sorry (line 237)**
   - Symmetric to j≥2, use same techniques
   - For negative powers, trace backwards through orbit

3. **P1: Fill orbit_ge2_has_core (line 103) and orbit_le_neg3_impossible (line 130)**
   - These may be redundant after filling inline sorries
   - Consider if they're still needed or can be removed

4. **P1: Fill SymmetricMain.lean sorries (lines 159, 181)**
   - Similar orbit structure arguments for k≥2 and m≥2 cases

---

## Implementation Notes for Next Session

### For j≥2 Case
```lean
-- Key structure:
by_cases h4_in_B₁ : (⟨4, by omega⟩ : Omega n k m) ∈ B₁
· -- 4 ∈ B₁: use orbit overlap at element 3
  have h0_in : 0 ∈ g₂(B₁) := ⟨4, h4_in_B₁, g₂_elem4_eq_elem0'⟩
  have h3_in_g₁²g₂B₁ : 3 ∈ g₁²(g₂(B₁)) := ⟨0, h0_in, g₁_sq_elem0_eq_elem3⟩
  -- 3 is also in g₂(B₁), derive partition contradiction
· -- 4 ∉ B₁: tailB ∩ B₁ ≠ ∅, use fixed elements
  -- g₂ maps tailB to tailB ∪ {1}, g₁ fixes both
  -- Element in C that's not in tailA
```

### Helper Lemmas Needed
- `g₂_tailB_to_tailB_or_1`: g₂ maps tailB element to tailB or 1
- May need explicit index computation for g₂ cycle on tailB

---

## Session Close Checklist
- [x] Build passes
- [x] HANDOFF.md updated with full details
- [ ] Changes committed and pushed
