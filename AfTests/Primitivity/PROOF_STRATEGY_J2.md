# Proof Strategy: j≥2 and j≤-3 Cases in case2_correct

## Goal
Prove `False` given:
- `B₁` is a block containing element 1
- `hDisj₁ : Disjoint (supp(g₁)) B₁` (B₁ ∩ supp(g₁) = ∅)
- `C = g₁^j(g₂(B₁))` for j ≥ 2 (or j ≤ -3)
- `hB_subset_tailA : ∀ x ∈ C, isTailA x`
- `hSize : 1 < C.ncard`

## Proof Decomposition

### Step 1: Get second element in B₁
Since |C| > 1 and all blocks have equal size, |B₁| > 1.
Since 1 ∈ B₁ and |B₁| > 1, there exists x ∈ B₁ with x ≠ 1.

**Existing lemma**: None needed, this is basic set theory.

### Step 2: Classify x
Since B₁ ∩ supp(g₁) = ∅, we have x ∉ supp(g₁).
By `elem_not_in_support_g₁_cases`: x.val = 1 ∨ x.val = 4 ∨ isTailB x ∨ isTailC x

Since x ≠ 1: **x.val = 4 ∨ isTailB x ∨ isTailC x**

**Existing lemma**: `elem_not_in_support_g₁_cases` ✓

### Step 3: Case x.val = 4

#### Sub-step 3a: Block overlap at element 3
- g₂(4) = 0 → 0 ∈ g₂(B₁)
- g₁²(0) = 3 → 3 ∈ g₁²(g₂(B₁))
- g₂(1) = 3 → 3 ∈ g₂(B₁)
- So 3 ∈ g₂(B₁) ∩ g₁²(g₂(B₁))

**Existing lemmas**:
- `g₂_elem4_eq_elem0'` ✓
- `g₁_pow2_elem0_eq_elem3` ✓
- `g₂_elem1_eq_elem3'` ✓

#### Sub-step 3b: Either equal or disjoint
By block partition property:
- If g₂(B₁) ≠ g₁²(g₂(B₁)): They're disjoint, contradicting 3 in both
- If g₂(B₁) = g₁²(g₂(B₁)): Continue to 3c

**Existing lemma**: Block partition disjointness (in hypotheses)

#### Sub-step 3c: If equal, derive 6 ∈ g₂(B₁)
If g₂(B₁) = g₁²(g₂(B₁)), then:
- 3 ∈ g₂(B₁)
- g₁²(3) = 6
- So 6 ∈ g₁²(g₂(B₁)) = g₂(B₁)

**Existing lemma**: `g₁_elem3_eq_elem2`, `g₁_elem2_eq_elem6` ✓

#### Sub-step 3d: But 6 ∉ range(g₂|_{B₁})
Since B₁ ⊆ {1, 4} ∪ tailB ∪ tailC (from B₁ ∩ supp(g₁) = ∅):
- g₂(1) = 3 ≠ 6
- g₂(4) = 0 ≠ 6
- g₂(tailB) ⊆ tailB ∪ {1} (all values < 6 or in [6+n, 6+n+k))
- g₂(tailC) = tailC (values in [6+n+k, 6+n+k+m), and 6 < 6+n+k when n≥1 or k≥1... WAIT)

**PROBLEM**: Need to verify 6 ∉ g₂(tailB) and 6 ∉ tailC

For 6 ∈ tailA, we need 6 ≤ x.val < 6+n, so x.val could be 6 if n ≥ 1.
tailB has x.val ∈ [6+n, 6+n+k), so min is 6+n ≥ 7 when n ≥ 1. So 6 ∉ tailB. ✓
tailC has x.val ∈ [6+n+k, 6+n+k+m), so min is 6+n+k ≥ 7. So 6 ∉ tailC. ✓
g₂(tailB) ⊆ tailB ∪ {1, 3, 4, 0}, none of which equal 6. ✓

**NEEDED LEMMA**: `g₂_B₁_not_elem6` - If B₁ ⊆ {1,4} ∪ tailB ∪ tailC, then 6 ∉ g₂(B₁)

### Step 4: Case isTailB x

- g₂(x) ∈ tailB ∪ {1} (need lemma)
- g₁^j fixes tailB elements (by `g₁_pow_fixes_tailB`)
- g₁^j fixes element 1 (by `g₁_pow_fixes_elem1`)
- So g₁^j(g₂(x)) = g₂(x)
- x ∈ B₁ → g₂(x) ∈ g₂(B₁) → g₁^j(g₂(x)) ∈ g₁^j(g₂(B₁)) = C
- But g₂(x) ∈ tailB ∪ {1}, neither in tailA
- Contradicts hB_subset_tailA

**NEEDED LEMMA**: `g₂_tailB_to_tailB_or_1` - g₂(tailB) ⊆ tailB ∪ {1}

**Existing lemmas**:
- `g₁_pow_fixes_tailB` ✓
- `g₁_pow_fixes_elem1` ✓
- `tailB_not_tailA` ✓
- `elem1_not_tailA` ✓

### Step 5: Case isTailC x

- g₂(x) = x (by `g₂_fixes_tailC`)
- g₁(x) = x (by `g₁_fixes_tailC`)
- So g₁^j(x) = x
- g₂(x) = x ∈ g₂(B₁)
- g₁^j(g₂(x)) = g₁^j(x) = x ∈ C
- But x ∈ tailC, so x ∉ tailA (by `tailC_disjoint_tailA`)
- Contradicts hB_subset_tailA

**Existing lemmas**:
- `g₂_fixes_tailC` ✓
- `g₁_fixes_tailC` ✓
- `tailC_disjoint_tailA` ✓

---

## Required New Helper Lemmas

### Lemma 1: `g₂_tailB_to_tailB_or_1`
```lean
theorem g₂_tailB_to_tailB_or_1 (x : Omega n k m) (hx : isTailB x) :
    isTailB (g₂ n k m x) ∨ g₂ n k m x = ⟨1, by omega⟩
```
**Proof sketch**:
- tailB elements are at indices 4, 5, ..., 3+k in g₂'s cycle list
- g₂ maps index i to (i+1) % (4+k)
- If i < 3+k: next element is also tailB
- If i = 3+k: wraps to index 0 = element 1

### Lemma 2: `g₂_tailB_not_tailA`
```lean
theorem g₂_tailB_not_tailA (x : Omega n k m) (hx : isTailB x) :
    ¬isTailA (g₂ n k m x)
```
**Proof**: Follows from Lemma 1 + `tailB_not_tailA` + `elem1_not_tailA`

### Lemma 3: `g₂_image_of_complement_supp_g₁_not_6` (for the x=4 subcase)
```lean
theorem g₂_image_of_complement_supp_g₁_not_6 (y : Omega n k m)
    (hy : y.val = 1 ∨ y.val = 4 ∨ isTailB y ∨ isTailC y) :
    (g₂ n k m y).val ≠ 6
```
**Proof sketch**:
- y = 1: g₂(1) = 3 ≠ 6
- y = 4: g₂(4) = 0 ≠ 6
- y ∈ tailB: g₂(y) ∈ tailB ∪ {1}, values are 1 or ≥ 6+n ≥ 7, none equal 6
- y ∈ tailC: g₂(y) = y ∈ tailC, values ≥ 6+n+k ≥ 7, not 6

---

## Implementation Order

1. **First**: Add `g₂_tailB_to_tailB_or_1` to OrbitHelpers.lean
2. **Second**: Add `g₂_tailB_not_tailA` (trivial from 1)
3. **Third**: Add `g₂_image_of_complement_supp_g₁_not_6`
4. **Fourth**: Write the j≥2 proof using these lemmas
5. **Fifth**: The j≤-3 proof is symmetric (uses zpow instead of pow)

---

## File Locations

- Helper lemmas: `AfTests/Primitivity/Lemma11_5_OrbitHelpers.lean`
- Main proof: `AfTests/Primitivity/Lemma11_5_Case2_Correct.lean`

## Dependencies

```
OrbitHelpers.lean
  ├── g₂_tailB_to_tailB_or_1 (NEW)
  ├── g₂_tailB_not_tailA (NEW, uses above)
  └── g₂_image_of_complement_supp_g₁_not_6 (NEW)

Case2_Correct.lean
  └── case2_correct theorem
      └── j≥2 case (uses all above)
```
