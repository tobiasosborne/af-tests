# Implementation Plan: m >= 2 Case in case2_impossible_C

**File**: `Lemma11_5_SymmetricCases.lean`
**Line**: 502
**Theorem**: `case2_impossible_C`

---

## Context

We have:
- `hm : m ≥ 1`, `hm1 : m ≠ 1` (so m ≥ 2)
- `B ⊆ tailC` (all elements of B are tailC elements)
- `c₁ ∈ B` and `|B| ≥ 2`
- `hBlock : ∀ j : ℕ, g₃^j '' B = B ∨ Disjoint (g₃^j '' B) B`
- Block system BS is H-invariant

**Key Insight**: `supp(g₂) ∩ supp(g₃) = {1, 4}` (not just {4}!)

---

## Step-by-Step Implementation

### Step 1: Find j such that g₃^j(c₁) = 4

**What we need**:
- `c₁_mem_support_g₃` ✓ EXISTS
- `elem4_in_support_g₃` ✓ EXISTS
- `g₃_isCycle` ✓ EXISTS
- `IsCycle.exists_zpow_eq` from Mathlib

**Code**:
```lean
have hc₁_in_supp : c₁ n k m hm ∈ (g₃ n k m).support := c₁_mem_support_g₃ hm
have h4_in_supp : (⟨4, by omega⟩ : Omega n k m) ∈ (g₃ n k m).support := elem4_in_support_g₃
have hCyc : (g₃ n k m).IsCycle := g₃_isCycle n k m
rw [mem_support] at hc₁_in_supp h4_in_supp
obtain ⟨j, hj⟩ := hCyc.exists_zpow_eq hc₁_in_supp h4_in_supp
```

**Helper lemmas needed**: NONE (all exist)

---

### Step 2: Define B' and establish basic properties

**What we need**:
- Define `B' := (g₃ n k m ^ j) '' B`
- Show `4 ∈ B'` (from c₁ ∈ B and hj)
- Show `|B'| = |B| ≥ 2`
- Show `B' ⊆ supp(g₃)` (zpow preserves support membership)
- Show `B' ∈ BS.blocks` using `g₃_zpow_preserves_blocks` ✓ EXISTS

**Code**:
```lean
let B' := (g₃ n k m ^ j) '' B
have h4_in_B' : (⟨4, by omega⟩ : Omega n k m) ∈ B' := ⟨c₁ n k m hm, hc₁_in_B, hj⟩
have hB'_card : B'.ncard = B.ncard := Set.ncard_image_of_injective _ (g₃ n k m ^ j).injective
have hB'_card_gt_1 : 1 < B'.ncard := by rw [hB'_card]; exact hNT_lower
have hB'_subset_supp : B' ⊆ (g₃ n k m).support := by
  intro x hx; obtain ⟨y, hyB, hyx⟩ := hx
  have hy_in_supp : y ∈ (g₃ n k m).support := hB_subset_supp_g₃ hyB
  simp only [Finset.mem_coe] at hy_in_supp ⊢
  rw [← hyx]; exact Equiv.Perm.zpow_apply_mem_support.mpr hy_in_supp
have hB'_in_BS : B' ∈ BS.blocks := g₃_zpow_preserves_blocks BS hInv B hB_in_BS j
```

**Helper lemmas needed**: NONE (all exist)

---

### Step 3: Show g₂(B') ≠ B'

**What we need**:
- `g₂_elem4_eq_elem0'` ✓ EXISTS (in OrbitHelpers_Core, already imported)
- `elem0_not_in_support_g₃` ✓ EXISTS

**Code**:
```lean
have hg₂_4_not_in_B' : g₂ n k m ⟨4, by omega⟩ ∉ B' := by
  rw [OrbitCore.g₂_elem4_eq_elem0']; intro h_contra
  exact elem0_not_in_support_g₃ (hB'_subset_supp h_contra)
have hg₂_B'_ne : g₂ n k m '' B' ≠ B' := by
  intro h_eq
  have : g₂ n k m ⟨4, by omega⟩ ∈ g₂ n k m '' B' := Set.mem_image_of_mem _ h4_in_B'
  rw [h_eq] at this; exact hg₂_4_not_in_B' this
```

**Helper lemmas needed**: NONE (all exist)

---

### Step 4: Find g₂-fixed element OR handle special case

This is the complex step. We need to either:
- (a) Find z ∈ B' with z ∈ {2, 5} ∪ tailC (so g₂(z) = z), OR
- (b) Handle the special case B' = {1, 4}

**Subcase 4a**: If ∃ z ∈ B' with z ∉ {1, 4}

Then z ∈ supp(g₃) \ {1, 4} = {2, 5} ∪ tailC, all of which are g₂-fixed.

**Existing lemmas needed**:
- `g₂_fixes_elem2` ✓ EXISTS
- `g₂_fixes_elem5` ✓ EXISTS
- `g₂_fixes_tailC` ✓ EXISTS

**Subcase 4b**: If B' ⊆ {1, 4} (i.e., B' = {1, 4} since |B'| ≥ 2)

Must derive contradiction from `hBlock`.

**NEW HELPER LEMMA NEEDED**:

```lean
/-- g₃²(c₁) = c₃ (element at index 6+n+k+2) for m ≥ 3 -/
theorem g₃_pow2_c₁_eq_c₃ (hm : m ≥ 3) :
    (g₃ n k m ^ (2 : ℕ)) (c₁ n k m (by omega)) = ⟨6 + n + k + 2, by omega⟩ := by
  -- Computational: g₃(c₁) = c₂, g₃(c₂) = c₃
  sorry
```

**Logic for 4b**:
1. B' = {1, 4} and |B| = 2, so B = {c₁, x} for some x ≠ c₁
2. g₃^j(x) = 1 (the other element of B')
3. x must be c₃ (by computing which tailC element maps to 1)
4. So B = {c₁, c₃}
5. By `hBlock 2`: either g₃²(B) = B or Disjoint g₃²(B) B
6. g₃²(c₁) = c₃ ∈ B (using helper lemma)
7. If g₃²(B) = B: then g₃²(c₃) ∈ B, but g₃²(c₃) = c₅ (for m ≥ 5) or wraps → contradiction
8. If Disjoint g₃²(B) B: then c₃ ∈ g₃²(B) ∩ B → contradiction

**NEW HELPER LEMMA NEEDED**:

```lean
/-- For m ≥ 2, the preimage of {1, 4} under g₃^(m+1) intersected with tailC
    gives exactly {c₁, c₃} (when m ≥ 3) -/
theorem g₃_zpow_preimage_1_4 (hm : m ≥ 3) :
    let j : ℤ := m + 1
    (g₃ n k m ^ j) (c₁ n k m (by omega)) = ⟨4, by omega⟩ ∧
    (g₃ n k m ^ j) (⟨6 + n + k + 2, by omega⟩ : Omega n k m) = ⟨1, by omega⟩ := by
  sorry
```

**Code structure for Step 4**:
```lean
by_cases hB'_small : ∃ z ∈ B', z ≠ (⟨1, by omega⟩ : Omega n k m) ∧ z ≠ (⟨4, by omega⟩ : Omega n k m)
case inl =>
  -- Easy case: use z for fixed-point argument
  obtain ⟨z, hz_in_B', hz_ne_1, hz_ne_4⟩ := hB'_small
  -- z ∈ {2, 5} ∪ tailC, so g₂(z) = z
  -- Apply block dichotomy contradiction
case inr =>
  -- Hard case: B' ⊆ {1, 4}, so B' = {1, 4}
  -- Derive contradiction via hBlock
```

---

## Summary of Needed Helper Lemmas

### Already Exist (no action needed):
1. `c₁_mem_support_g₃`
2. `elem4_in_support_g₃`
3. `g₃_isCycle`
4. `g₃_zpow_preserves_blocks`
5. `OrbitCore.g₂_elem4_eq_elem0'`
6. `elem0_not_in_support_g₃`
7. `g₂_fixes_elem2`
8. `g₂_fixes_elem5`
9. `g₂_fixes_tailC`

### Need to Create:
1. **`g₃_pow2_c₁_eq_c₃`**: Computational lemma showing g₃²(c₁) = c₃
2. **`g₃_pow2_c₃`**: Computational lemma for g₃²(c₃) (depends on m)

### Optional (may simplify proof):
3. **`elem_in_g₃_support_cases`**: Case split for elements in supp(g₃)

---

## Next Smallest Step

**Create `g₃_pow2_c₁_eq_c₃` lemma** in `Lemma11_5_OrbitHelpers_Core.lean`:

```lean
/-- g₃²(c₁) = c₃ for m ≥ 3. The g₃ cycle is (2 4 5 1 c₁ c₂ ... cₘ),
    so g₃(c₁) = c₂ and g₃(c₂) = c₃. -/
theorem g₃_pow2_c₁_eq_c₃ (hm : m ≥ 3) :
    (g₃ n k m ^ (2 : ℕ)) (⟨6 + n + k, by omega⟩ : Omega n k m) =
    ⟨6 + n + k + 2, by omega⟩ := by
  simp only [pow_two, Equiv.Perm.coe_mul, Function.comp_apply]
  -- g₃(c₁) = c₂
  have h1 : g₃ n k m ⟨6 + n + k, by omega⟩ = ⟨6 + n + k + 1, by omega⟩ := by
    sorry  -- List.formPerm computation
  -- g₃(c₂) = c₃
  have h2 : g₃ n k m ⟨6 + n + k + 1, by omega⟩ = ⟨6 + n + k + 2, by omega⟩ := by
    sorry  -- List.formPerm computation
  rw [h1, h2]
```

This lemma is purely computational and can use `native_decide` or explicit `List.formPerm` reasoning.

---

## Estimated Complexity

| Step | Difficulty | LOC | Notes |
|------|------------|-----|-------|
| Step 1 | Easy | 5 | All lemmas exist |
| Step 2 | Easy | 10 | All lemmas exist |
| Step 3 | Easy | 8 | All lemmas exist |
| Step 4a | Medium | 15 | Case analysis on z |
| Step 4b | Hard | 30+ | Requires new helper lemmas |

**Total**: ~70 lines for the full proof, plus ~20 lines for helper lemmas.
