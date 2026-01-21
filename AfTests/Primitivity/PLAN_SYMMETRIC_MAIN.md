# Plan: Filling SymmetricMain.lean Sorries

## Overview

There are 2 sorries in `Lemma11_5_SymmetricMain.lean`:
- **Line 159**: `case2_impossible_B` for k ≥ 2
- **Line 181**: `case2_impossible_C` for m ≥ 2

Both use the same proof strategy, so solving one gives the template for the other.

---

## Critical Finding: Missing Block Hypothesis

### Problem Statement

The theorem `case2_impossible_B` has these hypotheses:
```lean
theorem case2_impossible_B (hk : k ≥ 1) (B : Set (Omega n k m))
    (hg₂_disj : Disjoint (g₂ n k m '' B) B) (hb₁_in_B : b₁ n k m hk ∈ B)
    (hg₁_pres : PreservesSet (g₁ n k m) B) (hg₃_pres : PreservesSet (g₃ n k m) B)
    (hSize : 1 < B.ncard) : False
```

**Issue**: The theorem does NOT explicitly state that B is a block in an H-invariant system.

### Counterexample Analysis (k = 3)

Consider B = {6+n, 6+n+2} for k = 3:
- hg₂_disj: g₂(B) = {6+n+1, 1}, disjoint from B ✓
- hb₁_in_B: 6+n ∈ B ✓
- hg₁_pres: g₁ fixes tailB, so g₁(B) = B ✓
- hg₃_pres: g₃ fixes tailB, so g₃(B) = B ✓
- hSize: |B| = 2 > 1 ✓

All hypotheses satisfied, but the conclusion is False!

**Resolution**: The calling context (`Lemma11_5.lean:156`) passes B from a block system, so B IS a block. The proof must use the block property that for ALL h ∈ H, either h(B) = B or h(B) ∩ B = ∅.

For the counterexample B = {6+n, 6+n+2}:
- g₂²(B) = {6+n+2, 3}
- g₂²(B) ∩ B = {6+n+2} ≠ ∅
- But g₂²(B) ≠ B (since 3 ∉ B and 6+n ∉ g₂²(B))
- So B is NOT a valid block!

---

## Proof Strategy

### Core Argument for k ≥ 2

Given:
- B ⊆ tailB (from `case2B_B_subset_tailB`)
- g₂(B) ∩ B = ∅
- b₁ = 6+n ∈ B
- B is a block (from calling context)
- |B| > 1

**Step 1**: Show 6+n+1 ∉ B
- g₂(6+n) = 6+n+1
- Since 6+n ∈ B and g₂(B) ∩ B = ∅, we have 6+n+1 ∉ B

**Step 2**: Identify the second element
- Since |B| ≥ 2 and B ⊆ tailB and 6+n+1 ∉ B
- There exists j ∈ {2, ..., k-1} with 6+n+j ∈ B

**Step 3**: Use block property for g₂ʲ
- g₂ʲ(6+n) = 6+n+j ∈ B
- So g₂ʲ(B) ∩ B ⊇ {6+n+j} ≠ ∅
- Block property: g₂ʲ(B) = B

**Step 4**: Derive contradiction
- g₂ʲ(6+n+j) = g₂²ʲ(6+n)
- If 2j ≥ k: g₂²ʲ(6+n) exits tailB (equals 1 or later core element)
- Since B ⊆ tailB: g₂ʲ(6+n+j) ∉ B
- But g₂ʲ(B) = B requires g₂ʲ(6+n+j) ∈ B
- Contradiction!

**Step 5**: Handle 2j < k case by induction
- If 2j < k: 6+n+2j ∈ tailB, and 6+n+2j ∈ B (from g₂ʲ(B) = B)
- Apply same argument with 4j, 8j, ... until 2ʳj ≥ k
- Eventually exits tailB, giving contradiction

---

## Implementation Options

### Option A: Add Block Hypothesis (Recommended)

Modify the theorem signature to include explicit block property:

```lean
theorem case2_impossible_B (hk : k ≥ 1) (B : Set (Omega n k m))
    (hg₂_disj : Disjoint (g₂ n k m '' B) B) (hb₁_in_B : b₁ n k m hk ∈ B)
    (hg₁_pres : PreservesSet (g₁ n k m) B) (hg₃_pres : PreservesSet (g₃ n k m) B)
    (hBlock : ∀ j : ℤ, (g₂ n k m ^ j) '' B = B ∨ Disjoint ((g₂ n k m ^ j) '' B) B)
    (hSize : 1 < B.ncard) : False
```

Pros:
- Explicit, self-contained theorem
- Clearer proof obligation

Cons:
- Requires updating call site in Lemma11_5.lean:156
- Additional hypothesis to verify

### Option B: Use Block System Parameter

Pass the block system directly:

```lean
theorem case2_impossible_B (hk : k ≥ 1) (BS : BlockSystemOn n k m)
    (B : Set (Omega n k m)) (hB_mem : B ∈ BS.blocks)
    (hg₂_disj : Disjoint (g₂ n k m '' B) B) (hb₁_in_B : b₁ n k m hk ∈ B)
    (hg₁_pres : PreservesSet (g₁ n k m) B) (hg₃_pres : PreservesSet (g₃ n k m) B)
    (hInv : IsHInvariant BS)
    (hSize : 1 < B.ncard) : False
```

Pros:
- More natural interface
- Can derive all needed properties from BS

Cons:
- Larger signature change
- More dependencies

### Option C: Inline Block Dichotomy (Current Approach Variant)

Add the g₂² dichotomy as a derived hypothesis within the proof:

```lean
-- At line 159, before sorry:
have hg₂²_dich : (g₂ n k m ^ 2) '' B = B ∨ Disjoint ((g₂ n k m ^ 2) '' B) B := by
  -- Derive from block system membership
  sorry -- Need to thread through from calling context
```

Pros:
- Minimal signature change

Cons:
- Requires careful threading of block membership
- Less clean

---

## Recommended Execution Steps

### Step 1: Verify Block Property Availability

Check that the calling context in Lemma11_5.lean can provide the block dichotomy:
```bash
grep -n "hDich" AfTests/Primitivity/Lemma11_5.lean
```

Expected: Find `hDich₂` which gives g₂ dichotomy for B.

### Step 2: Analyze Dichotomy for Powers

For the proof, we need dichotomy for g₂ʲ. Check if:
- `perm_image_preserves_or_disjoint` can be applied to powers
- Or if we need to derive it from the group structure

### Step 3: Choose Implementation Option

Based on Step 1-2 findings:
- If dichotomy easily derivable: Option A or C
- If complex: Option B for cleaner interface

### Step 4: Implement k = 1 and k = 2 Cases

These are simpler and already partially done (k = 1 has `case2B_B_ncard_le_one_k1`).

For k = 2:
- tailB = {6+n, 6+n+1}
- 6+n ∈ B, 6+n+1 ∉ B (from Step 1 of strategy)
- So B = {6+n}, |B| = 1 ✓

### Step 5: Implement General k ≥ 2 Case

Use induction on the power j:
1. Find minimal j ≥ 2 with 6+n+j ∈ B
2. Show g₂ʲ(B) = B
3. Show 2^r·j ≥ k for some r (always true)
4. Derive contradiction at that step

### Step 6: Port to m ≥ 2 Case

Same argument with:
- g₃ instead of g₂
- tailC instead of tailB
- c₁ instead of b₁

---

## Helper Lemmas Needed

### 1. g₂_shift_tailB_elem

```lean
/-- g₂ shifts tailB elements forward by 1 (or to 1 if at end) -/
theorem g₂_tailB_shift (i : Fin k) (hi : i.val < k - 1) :
    g₂ n k m ⟨6 + n + i.val, _⟩ = ⟨6 + n + i.val + 1, _⟩ := by
  -- Use formPerm index computation
  sorry
```

### 2. g₂_pow_tailB_exit

```lean
/-- g₂^k maps first tailB element to core -/
theorem g₂_pow_k_b₁ (hk : k ≥ 1) :
    (g₂ n k m ^ k) (b₁ n k m hk) = ⟨1, by omega⟩ := by
  -- Trace through k applications
  sorry
```

### 3. block_zpow_dichotomy

```lean
/-- For a block in H-invariant system, zpow preserves block dichotomy -/
theorem block_zpow_dichotomy {BS : BlockSystemOn n k m}
    (hInv : IsHInvariant BS) (B : Set (Omega n k m)) (hB : B ∈ BS.blocks)
    (g : Perm (Omega n k m)) (hg : g ∈ ({g₁ n k m, g₂ n k m, g₃ n k m} : Set _))
    (j : ℤ) : (g ^ j) '' B = B ∨ Disjoint ((g ^ j) '' B) B := by
  -- Use H-invariance and group closure
  sorry
```

---

## File Structure Considerations

Current line count for SymmetricMain.lean: ~183 lines (under 200)

Adding the full proof may push it over 200 lines. Options:
1. Create `Lemma11_5_Case2B_Orbit.lean` for orbit analysis lemmas
2. Create `Lemma11_5_Case2C_Orbit.lean` for symmetric proofs
3. Add helpers to existing `SymmetricCase2B.lean` and `SymmetricCase2C.lean`

Recommendation: Add helpers to existing Case2B/Case2C files first, only split if needed.

---

## Testing Strategy

Before full implementation:
1. Verify counterexample B = {6+n, 6+n+2} is NOT a valid block by computing g₂²(B)
2. Test g₂_shift_tailB_elem on concrete examples (n=k=m=1)
3. Verify the orbit length formula for small k values

---

## Summary

| Task | File | Complexity |
|------|------|------------|
| Add block hypothesis | SymmetricMain.lean | Low |
| Update call site | Lemma11_5.lean | Low |
| Implement k≥2 proof | SymmetricMain.lean | Medium |
| Add helper lemmas | SymmetricCase2B.lean | Medium |
| Port to m≥2 | SymmetricMain.lean | Low (copy) |
| Port helpers | SymmetricCase2C.lean | Low (copy) |

**Estimated total**: Medium complexity, requires careful orbit analysis.
