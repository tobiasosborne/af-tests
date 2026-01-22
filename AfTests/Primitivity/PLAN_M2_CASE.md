# Implementation Plan: m >= 2 Case in case2_impossible_C

**File**: `Lemma11_5_SymmetricCases.lean` (806 lines - OVER LIMIT)
**Theorem**: `case2_impossible_C`

---

## Current Status (2026-01-22)

| Item | Status |
|------|--------|
| Build | ✅ PASSING |
| Sorry count | 1 (line 807, Disjoint case in m≥3) |
| File LOC | 806 (EXCEEDS 200 limit) |

---

## PRIORITY 1: Refactor File (BEFORE sorry work)

The file is 806 lines, exceeding the 200 LOC limit by 4x. Must refactor first.

### Proposed File Split

| New File | Contents | Lines | Source Lines |
|----------|----------|-------|--------------|
| `Lemma11_5_SymmetricDefs.lean` | Definitions (b₁, c₁, containsB₁, containsC₁) + helper lemmas | ~200 | 39-239 |
| `Lemma11_5_CaseB.lean` | `case2_impossible_B` theorem | ~260 | 245-506 |
| `Lemma11_5_CaseC.lean` | `case2_impossible_C` theorem (with sorry) | ~300 | 508-807 |

### File 1: `Lemma11_5_SymmetricDefs.lean` (~200 lines)

**Contents:**
- `def b₁` - first element of tailB
- `def c₁` - first element of tailC
- `def containsB₁` - predicate for B containing b₁
- `def containsC₁` - predicate for C containing c₁
- `b₁_mem_support_g₂` - b₁ is in g₂'s support
- `c₁_mem_support_g₃` - c₁ is in g₃'s support
- `lemma11_3_tail_B_in_block` - if B contains b₁ and is g₂-stable, supp(g₂) ⊆ B
- `lemma11_3_tail_C_in_block` - if B contains c₁ and is g₃-stable, supp(g₃) ⊆ B
- `tailB_not_in_support_g₁` - tailB elements not in g₁ support
- `tailB_not_in_support_g₃` - tailB elements not in g₃ support
- `g₁_fixes_b₁`, `g₃_fixes_b₁` - g₁, g₃ fix b₁
- `tailC_not_in_support_g₁` - tailC elements not in g₁ support
- `tailC_not_in_support_g₂` - tailC elements not in g₂ support
- `g₁_fixes_c₁`, `g₂_fixes_c₁` - g₁, g₂ fix c₁
- `case2_forces_stabilization_B` - forcing lemma for B
- `case2_forces_stabilization_C` - forcing lemma for C
- `case1b_impossible_g₃` - impossibility lemma
- `case1b_impossible_g₁_from_g₂` - impossibility lemma
- `case1b_impossible_g₁` - impossibility lemma
- `case1b_impossible_g₂_from_g₃` - impossibility lemma

**Imports needed:**
```lean
import AfTests.Core
import AfTests.Primitivity.Lemma11_2
import AfTests.Primitivity.Lemma11_5_FixedPoints
import AfTests.Primitivity.Lemma11_5_CycleSupport
import AfTests.Primitivity.Lemma11_5_Defs
import AfTests.Primitivity.Lemma11_5_SupportCover
```

### File 2: `Lemma11_5_CaseB.lean` (~260 lines)

**Contents:**
- `case2_impossible_B` theorem (the k≥1 / tailB case)

**Imports needed:**
```lean
import AfTests.Primitivity.Lemma11_5_SymmetricDefs
import AfTests.Primitivity.Lemma11_5_Case2
import AfTests.Transitivity.Lemma05ListProps
import AfTests.Primitivity.Lemma11_5_ZpowBlocks
import AfTests.Primitivity.Lemma11_5_OrbitHelpers_Core
import AfTests.Primitivity.Lemma11_5_OrbitHelpers
```

### File 3: `Lemma11_5_CaseC.lean` (~300 lines)

**Contents:**
- `case2_impossible_C` theorem (the m≥1 / tailC case, with sorry at line ~300)

**Imports needed:**
```lean
import AfTests.Primitivity.Lemma11_5_SymmetricDefs
import AfTests.Primitivity.Lemma11_5_Case2
import AfTests.Transitivity.Lemma05ListProps
import AfTests.Primitivity.Lemma11_5_ZpowBlocks
import AfTests.Primitivity.Lemma11_5_OrbitHelpers_Core
import AfTests.Primitivity.Lemma11_5_OrbitHelpers
import AfTests.SignAnalysis.Lemma14
```

### Refactoring Steps

1. Create `Lemma11_5_SymmetricDefs.lean` with definitions and helper lemmas
2. Create `Lemma11_5_CaseB.lean` with `case2_impossible_B`
3. Create `Lemma11_5_CaseC.lean` with `case2_impossible_C`
4. Delete original `Lemma11_5_SymmetricCases.lean`
5. Update any files that import `Lemma11_5_SymmetricCases`
6. Build and verify

---

## PRIORITY 2: Fill Sorry (AFTER refactoring)

**Location**: `Lemma11_5_CaseC.lean`, Disjoint case in m≥3 branch

**Goal**: Prove `False` from:
- `hg₃Disj : Disjoint (g₃ '' B) B`
- `B = {c₁, c₃}` (2-element set)
- `g₃²(B) ≠ B` (Disjoint case)

**Strategy**: The m≥3 Disjoint case. We have:
- `g₃(c₁) = c₂` but `c₂ ∉ B`
- Need to show `g₃(B) ∩ B ≠ ∅` to contradict `hg₃Disj`

Since `B = {c₁, c₃}`:
- `g₃(c₁) = c₂ ∉ B`
- `g₃(c₃) = c₄` (if m≥4) or wraps

Key insight: `g₃⁻¹(c₁) = 1 ∉ tailC`, so `c₁ ∉ g₃(B)` only if `1 ∉ B` (true since B ⊆ tailC).

But we also have `g₃⁻¹(c₃) = c₂`. So `c₃ ∈ g₃(B)` iff `c₂ ∈ B`. Since `c₂ ∉ B`, we have `c₃ ∉ g₃(B)`.

Hmm, need to check `g₃({c₁, c₃}) = {g₃(c₁), g₃(c₃)} = {c₂, c₄}`.
And `{c₂, c₄} ∩ {c₁, c₃} = ∅` for m≥4... this might actually be consistent!

**Re-analysis needed**: The Disjoint case might require a different approach. Check if `g₃²(B) = B` is actually forced, making Disjoint impossible.

---

## Step-by-Step Status (case2_impossible_C)

| Step | Status | Description |
|------|--------|-------------|
| Step 1 | ✅ DONE | Find j such that g₃^j(c₁) = 4 |
| Step 2 | ✅ DONE | Define B' and establish basic properties |
| Step 3 | ✅ DONE | Show g₂(B') ≠ B' |
| Step 4a | ✅ DONE | Easy case: find g₂-fixed element z ∉ {1,4} |
| Step 4b.1 | ✅ DONE | Establish B' = {1, 4} |
| Step 4b.2 (m=2) | ✅ DONE | Contradiction via g₃²(c₁) = 2 ∉ tailC |
| Step 4b.2 (m≥3) Equality | ✅ DONE | g₃²(B) = B leads to cycle length contradiction |
| Step 4b.2 (m≥3) Disjoint | ❌ TODO | **SORRY** - needs analysis |

---

## Session Log

### 2026-01-22 Session 2
- Fixed build errors at lines 727-736 in `hB_sub` proof
- Fixes: `Ne.symm hx_not.2` → correct direction, `Ne.symm hx_not.1` → correct field
- Added explicit `hB'_card_eq_2` and `hB_card_eq_2` for omega
- Build now PASSING
- Updated plan to prioritize refactoring before sorry work

### 2026-01-22 Session 1
- Implemented m≥3 case structure (lines 686-797)
- c₂ ∈ B case complete (contradiction with hg₃Disj)
- c₂ ∉ B case partially done (Equality subcase complete, Disjoint subcase has sorry)
- Build was FAILING due to errors at lines 727-736
