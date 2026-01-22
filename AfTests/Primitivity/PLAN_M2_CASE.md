# Implementation Plan: m >= 2 Case in case2_impossible_C

**File**: `Lemma11_5_SymmetricCases.lean`
**Theorem**: `case2_impossible_C`

---

## Status Summary

| Step | Status | Description |
|------|--------|-------------|
| Step 1 | ✅ DONE | Find j such that g₃^j(c₁) = 4 |
| Step 2 | ✅ DONE | Define B' and establish basic properties |
| Step 3 | ✅ DONE | Show g₂(B') ≠ B' |
| Step 4a | ✅ DONE | Easy case: find g₂-fixed element z ∉ {1,4} |
| Step 4b.1 | ✅ DONE | Establish B' = {1, 4} |
| Step 4b.2 (m=2) | ✅ DONE | Contradiction via g₃²(c₁) = 2 ∉ tailC |
| Step 4b.2 (m≥3) | ❌ TODO | **CURRENT SORRY** - Line 686 |

**Current sorry**: Line 686, inside `· -- Case m ≥ 3`

---

## What Has Been Achieved

### Steps 1-4a (Previously completed)
Standard setup: found `j` with `g₃^j(c₁) = 4`, defined `B' = g₃^j '' B`, showed `g₂(B') ≠ B'`, handled easy case where `∃ z ∈ B', z ∉ {1, 4}`.

### Step 4b.1: Establish B' = {1, 4} (Lines 614-634)
- Used `push_neg` to transform `hB'_small` from negated existential to implication form
- Proved `h1_in_B'` via cardinality argument (|B'| > 1 and B' ⊆ {1,4} implies 1 ∈ B')
- Established `hB'_eq_14 : B' = {⟨1, _⟩, ⟨4, _⟩}`

**Key insight**: After `push_neg`, `hB'_small` becomes `∀ z ∈ B', z ≠ 1 → z = 4` (implication form, not disjunction). Must use `by_cases` instead of `rcases`.

### Step 4b.2 m=2 Case (Lines 637-684) - COMPLETE
Split into two sub-cases via `rcases hBlock 2`:

**Equality case** (`g₃²(B) = B`): Lines 647-652
- Used `OrbitCore.g₃_pow2_c₁_eq_elem2` to get `g₃²(c₁) = 2`
- Showed `2 ∉ tailC` via `simp only [isTailC]; omega`
- Since `c₁ ∈ B` and `g₃²(B) = B`, we have `2 ∈ B`
- But `B ⊆ tailC` contradicts `2 ∉ tailC`

**Disjoint case** (`Disjoint (g₃² '' B) B`): Lines 653-684
- Since `m = 2`, `tailC = {c₁, c₂}` has exactly 2 elements
- Since `|B| = 2` and `B ⊆ tailC`, we have `B = {c₁, c₂}`
- Used `@OrbitCore.g₃_c₁_eq_c₂ n k m` to get `g₃(c₁) = c₂`
- So `c₂ ∈ g₃(B)` and `c₂ ∈ B`
- This contradicts `hg₃Disj : Disjoint (g₃ '' B) B`

---

## Session 2026-01-22: Work Done and Remaining Errors

### What Was Implemented

1. **m ≥ 3 case structure** (lines 686-797):
   - Added `hm3 : m ≥ 3` from `hm_eq_2 : ¬m = 2` and `hm2 : m ≥ 2`
   - Established `hg₃_c₁ : g₃(c₁) = c₂` using `OrbitCore.g₃_c₁_eq_c₂`
   - Case split on `c₂ ∈ B` (line 692)

2. **c₂ ∈ B case** (lines 693-696): COMPLETE
   - Shows `c₂ ∈ (g₃ '' B) ∩ B`, contradicts `hg₃Disj`

3. **c₂ ∉ B case** (lines 697-797): PARTIALLY IMPLEMENTED
   - Used `hBlock 2` to case split on `g₃²(B) = B` vs `Disjoint`
   - **Equality case** (g₃²(B) = B): Lines 705-794
     - Shows c₃ ∈ B (from g₃²(c₁) = c₃ ∈ g₃²(B) = B)
     - Shows B = {c₁, c₃}
     - Uses cycle length argument: g₃²(c₃) ∉ {c₁, c₃} because:
       - `IsCycle.orderOf` gives `orderOf g₃ = support.card = 4+m`
       - `IsCycle.pow_eq_one_iff` converts `g₃^n(x) = x` to `g₃^n = 1`
       - `orderOf_dvd_of_pow_eq_one` gives `(4+m) ∣ n`
       - `Nat.le_of_dvd` converts to `4+m ≤ n`, contradiction for n=2,4
   - **Disjoint case** (line 797): SORRY remains

### Current Build Errors (Lines 727-736)

The `hB_sub` proof has errors:

```
Line 727: Type mismatch - hx_not.2
Line 729: Invalid field `symm` on hx_not.2
Line 731: ncard_le_ncard argument mismatch
Line 736: omega can't prove goal
```

**Root cause**: After `simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx_not`, the structure of `hx_not` may not be `∧` but something else. Need to check actual type with `lean_goal`.

**Fix approach** (for next session):
1. Use `lean_goal` at line 723 to see actual type of `hx_not`
2. Adjust destructuring accordingly
3. May need `And.intro` or different approach for the `ncard_le_ncard` call

### Key Learnings

1. **Correct API for cycle power lemmas**:
   - `IsCycle.pow_eq_one_iff` : `f^n = 1 ↔ ∃ x, f x ≠ x ∧ f^n x = x`
   - `IsCycle.orderOf` : `orderOf f = f.support.card`
   - `orderOf_dvd_of_pow_eq_one` : `f^n = 1 → orderOf f ∣ n`
   - `Nat.le_of_dvd` : `0 < b → a ∣ b → a ≤ b` (needed for omega)

2. **g₃_support_card location**: `AfTests.SignAnalysis.g₃_support_card`

3. **pow_add for permutations**: Need explicit calc chain:
   ```lean
   calc (g₃ ^ 4) x = (g₃ ^ (2+2)) x := by rw [show (4:ℕ) = 2+2 from rfl]
       _ = (g₃^2 * g₃^2) x := by rw [pow_add]
       _ = (g₃^2) ((g₃^2) x) := by simp [Equiv.Perm.coe_mul]
   ```

## Current State at the Sorry (Line 686)

```lean
-- Hypotheses available:
hm : m ≥ 1
hm1 : ¬m = 1                    -- so m ≥ 2
hm2 : m ≥ 2
hm_eq_2 : ¬m = 2               -- so m ≥ 3
B : Set (Omega n k m)
BS : BlockSystemOn n k m
hInv : IsHInvariant BS
hB_in_BS : B ∈ BS.blocks
hg₃Disj : Disjoint (g₃ '' B) B
hc₁_in_B : c₁ n k m hm ∈ B
hBlock : ∀ j : ℕ, (g₃^j) '' B = B ∨ Disjoint ((g₃^j) '' B) B
hNT_lower : 1 < B.ncard
hB_subset_supp_g₃ : B ⊆ supp(g₃)
hB_subset_tailC : ∀ x ∈ B, isTailC x

-- From Steps 1-4b.1:
j : ℤ
hj : (g₃^j)(c₁) = 4
B' : Set (Omega n k m) := (g₃^j) '' B
hB'_eq_14 : B' = {⟨1, _⟩, ⟨4, _⟩}
h1_in_B' : ⟨1, _⟩ ∈ B'
h4_in_B' : ⟨4, _⟩ ∈ B'
hB'_card_gt_1 : 1 < B'.ncard
```

**Goal**: `False`

---

## NEXT TINY STEP: m ≥ 3 Case

### Strategy

For m ≥ 3, the g₃ cycle is `(2 4 5 1 c₁ c₂ c₃ ... cₘ)` with length `4 + m ≥ 7`.

**Key facts**:
- `g₃²(c₁) = c₃` (by `OrbitCore.g₃_pow2_c₁_eq_c₃`)
- `c₃` IS a tailC element (unlike the m=2 case where g₃²(c₁) = 2)

**Approach**: Use `hg₃Disj : Disjoint (g₃ '' B) B` directly.

Since `|B| = 2` (because `|B'| = 2` and `|B| = |B'|`) and `B ⊆ tailC`:
- `c₁ ∈ B` (given)
- There exists exactly one other element `x ∈ B` with `x ≠ c₁`
- `x` is a tailC element

Now `g₃(c₁) = c₂` (by `OrbitCore.g₃_c₁_eq_c₂`).

**Case analysis on x**:
- If `x = c₂`: Then `g₃(c₁) = c₂ = x ∈ B`, so `c₂ ∈ (g₃ '' B) ∩ B`, contradicting `hg₃Disj`
- If `x ≠ c₂`: We need to show this also leads to contradiction...

**Simpler approach**: Show that for ANY 2-element subset `B ⊆ tailC` containing `c₁`, we have `g₃(B) ∩ B ≠ ∅`:
- `g₃(c₁) = c₂`
- If `c₂ ∈ B`, done (contradiction with `hg₃Disj`)
- If `c₂ ∉ B`, then `B = {c₁, x}` for some `x ∈ tailC`, `x ≠ c₁`, `x ≠ c₂`
  - Need to trace `g₃(x)` and `g₃⁻¹(c₁)` to find overlap...

**Alternative**: Use cycle structure. The g₃ cycle on tailC is `(c₁ c₂ c₃ ... cₘ)`. Any 2-element subset `{c₁, cᵢ}` with i ≥ 2 has:
- `g₃(c₁) = c₂`
- If `i = 2`: `c₂ ∈ B` ✓
- If `i > 2`: `g₃(cᵢ₋₁) = cᵢ`, so need `cᵢ₋₁ ∈ B`... but `B = {c₁, cᵢ}`, so `cᵢ₋₁ ∉ B` unless `i-1 = 1`, i.e., `i = 2`.

Hmm, this needs more care. The key insight is:
- `g₃⁻¹(c₁) = 1` (element 1, not c₁)
- So `c₁ ∈ g₃(B)` iff `1 ∈ B`
- But `B ⊆ tailC` and `1 ∉ tailC`, so `1 ∉ B`
- Therefore `c₁ ∉ g₃(B)`

Wait, let's think about this differently using B' = {1, 4}:
- `B' = g₃^j '' B`
- `1 ∈ B'` means `∃ y ∈ B, g₃^j(y) = 1`
- `4 ∈ B'` means `∃ z ∈ B, g₃^j(z) = 4` (we know z = c₁)
- Since `|B| = 2`, we have `B = {c₁, y}` where `g₃^j(y) = 1`

Now use `hg₃Disj`:
- `g₃(c₁) = c₂`
- Is `c₂ ∈ B`? If yes, contradiction.
- If no, then `B = {c₁, y}` with `y ≠ c₂`

What is `y`? We know `g₃^j(y) = 1`. In the cycle `(2 4 5 1 c₁ c₂ ... cₘ)`:
- `g₃(5) = 1`
- So `g₃^(j-1)(y) = 5`... this gets complicated.

**Simplest approach for tiny step**: Just use the m=2 argument structure but adapted:
1. Show `|B| = 2` (from `|B'| = 2`)
2. Show `B ⊆ tailC` with `c₁ ∈ B` and `|tailC| = m ≥ 3`
3. Use `hg₃Disj` to constrain what the other element can be
4. Derive contradiction

### Code to try

```lean
· -- Case m ≥ 3
  have hm3 : m ≥ 3 := by omega
  -- |B| = 2 since |B'| = 2
  have hB_card_2 : B.ncard = 2 := by
    have : B'.ncard = 2 := by rw [hB'_eq_14]; simp [Set.ncard_pair]; intro h; simp [Fin.ext_iff] at h
    omega
  -- g₃(c₁) = c₂
  have hg₃_c₁ : g₃ n k m (c₁ n k m hm) = ⟨6 + n + k + 1, by omega⟩ := by
    simp only [c₁]; exact @OrbitCore.g₃_c₁_eq_c₂ n k m (by omega : m ≥ 2)
  -- c₂ is a tailC element
  have hc₂_tailC : isTailC (⟨6 + n + k + 1, by omega⟩ : Omega n k m) := by
    simp only [isTailC]; omega
  -- If c₂ ∈ B, contradiction with hg₃Disj
  by_cases hc₂_in_B : (⟨6 + n + k + 1, by omega⟩ : Omega n k m) ∈ B
  · have hc₂_in_g₃B : (⟨6 + n + k + 1, by omega⟩ : Omega n k m) ∈ g₃ n k m '' B := by
      rw [← hg₃_c₁]; exact Set.mem_image_of_mem _ hc₁_in_B
    exact Set.disjoint_iff.mp hg₃Disj ⟨hc₂_in_g₃B, hc₂_in_B⟩
  · -- c₂ ∉ B, so B = {c₁, x} for some x ≠ c₁, x ≠ c₂
    -- Need more analysis here...
    sorry
```

---

## Helper Lemmas Available

### In OrbitCore namespace:
1. `g₃_c₁_eq_c₂` (m ≥ 2) - `g₃(c₁) = c₂` where c₂ = ⟨6+n+k+1, _⟩
2. `g₃_c₂_eq_c₃` (m ≥ 3) - `g₃(c₂) = c₃`
3. `g₃_pow2_c₁_eq_c₃` (m ≥ 3) - `g₃²(c₁) = c₃`
4. `g₃_pow2_c₁_eq_elem2` (m = 2) - `g₃²(c₁) = 2`

### May need to create:
- Lemma showing `g₃⁻¹(c₁) = 1` (element 1, not tailC)
- Or lemma about g₃ orbit structure on tailC

---

## File Line Count Warning

`Lemma11_5_SymmetricCases.lean` is now ~686 lines, well over the 200 LOC limit. After completing this sorry, refactoring should be considered.
