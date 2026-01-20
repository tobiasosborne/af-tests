# Handoff: 2026-01-20 (Session 33)

## Completed This Session

### ThreeCycleProof.lean:121 Sorry ELIMINATED
The 6 core element cases are now fully proven structurally.

**Files Created:**
- `CoreElementLemmas.lean` (168 lines): Generator actions on core elements {0,1,2,3,4,5}
  - g₃ actions: g₃_5_eq_1, g₃_1_eq_2, g₃_fixes_3, g₃_inv_1_eq_5, g₃_inv_2_eq_1
  - g₁ actions: g₁_5_eq_3, g₁_3_eq_2, g₁_inv_3_eq_5, g₁_inv_2_eq_3, g₁_2_eq_6, g₁_inv_6_eq_2
  - g₂ actions: g₂_fixes_5, g₂_fixes_2, g₂_1_eq_3, g₂_3_eq_4, g₂_4_eq_0, g₂_inv_*

- `ProductLemmas.lean` (152 lines): Commutator and product actions
  - c₁₃⁻¹ actions: c₁₃_inv_0_eq_5, c₁₃_inv_1_eq_3, c₁₃_inv_2_eq_1, c₁₃_inv_3_eq_2, c₁₃_inv_5_eq_4
  - c₁₂ actions: c₁₂_5_eq_1, c₁₂_3_eq_5, c₁₂_1_eq_3, c₁₂_2_eq_2, c₁₂_4_eq_0
  - product actions: product_0_eq_1, product_1_eq_5, product_2_eq_3, product_3_eq_2, product_5_eq_0

**Files Updated:**
- `ThreeCycleProof.lean` (185 lines): Added squared action theorems, filled interval_cases
- `TailLemmas.lean` (198 lines): Trimmed from 206 lines
- `TailAFixing.lean` (200 lines): Trimmed from 201 lines

### LOC Violations FIXED
All ThreeCycle files now under 200 LOC.

---

## Current State

### Build Status: PASSING

### Sorry Count: 6 total
| Location | Description | Difficulty |
|----------|-------------|------------|
| ThreeCycleSymmetric.lean:54 | m≥1, k=0 case | Hard |
| ThreeCycleSymmetric.lean:77 | k≥1 case | Hard |
| Primitivity (4 sorries) | Includes known bug | N/A |

### No LOC Violations

---

## Key Learnings This Session

### 1. interval_cases Requires Named Hypothesis
After `interval_cases x.val`, x isn't substituted in the goal. Fix:
```lean
interval_cases hv : x.val
have hx : x = ⟨0, by omega⟩ := Fin.ext hv
rw [hx, ...]
```

### 2. c₁₃⁻¹ Proof Pattern (Inside-Out Rewriting)
After `rw [Perm.inv_eq_iff_eq]`, goal becomes `⟨y⟩ = c₁₃(⟨x⟩)`.
Must rewrite RHS from inside out:
```lean
theorem c₁₃_inv_0_eq_5 : (commutator_g₁_g₃ n k 0)⁻¹ ⟨0, _⟩ = ⟨5, _⟩ := by
  rw [Perm.inv_eq_iff_eq]; unfold commutator_g₁_g₃; simp only [Perm.mul_apply]
  -- Goal: ⟨0, _⟩ = g₁⁻¹(g₃⁻¹(g₁(g₃(5))))
  rw [g₃_5_eq_1, g₁_fixes_1, g₃_inv_1_eq_5, g₁_inv_5_eq_0]
```

### 3. formPerm_apply_getElem Modular Arithmetic
`simp` doesn't compute modular arithmetic well. Use explicit:
```lean
show (3 + 1) % (0 + 1 + 1 + 1 + 1) = 0 by native_decide
```

### 4. Accessing tailAList Elements
Use `Transitivity.g₁_list_getElem_tail` for tailA indexing:
```lean
have := Transitivity.g₁_list_getElem_tail n k 0 ⟨0, hn⟩
```

---

## Next Recommended Target: ThreeCycleSymmetric.lean

### Why?
- Completes the 3-cycle extraction for all parameter combinations
- Two remaining sorries: m≥1/k=0 case and k≥1 case
- Both require similar structural analysis to what we did for m=0

### Location
```lean
-- AfTests/ThreeCycle/ThreeCycleSymmetric.lean:54
sorry -- Structural proof TODO (m≥1, k=0)

-- AfTests/ThreeCycle/ThreeCycleSymmetric.lean:77
sorry -- Structural proof TODO (k≥1)
```

---

## Files Modified This Session
- AfTests/ThreeCycle/CoreElementLemmas.lean (NEW)
- AfTests/ThreeCycle/ProductLemmas.lean (NEW)
- AfTests/ThreeCycle/ThreeCycleProof.lean (MODIFIED)
- AfTests/ThreeCycle/TailLemmas.lean (MODIFIED)
- AfTests/ThreeCycle/TailAFixing.lean (MODIFIED)

---

## Generator Cycle Reference

```
g₁ = formPerm [0, 5, 3, 2, 6, 7, ..., 5+n]     -- core + tailA
g₂ = formPerm [1, 3, 4, 0, 6+n, ..., 5+n+k]   -- core + tailB
g₃ = formPerm [2, 4, 5, 1]                     -- core only (when m=0)

Cycle mappings:
g₁: 0→5→3→2→6→...→(5+n)→0
g₂: 1→3→4→0→(6+n)→...→(5+n+k)→1
g₃: 2→4→5→1→2
```

## Single Application Values (c₁₂*c₁₃⁻¹)
```
| x.val | (c₁₂*c₁₃⁻¹)(x) |
|-------|----------------|
| 0     | 1              |
| 1     | 5              |
| 2     | 3              |
| 3     | 2              |
| 4     | 5+n            |
| 5     | 0              |
```

## Squared Values (c₁₂*c₁₃⁻¹)²
```
| x.val | (c₁₂*c₁₃⁻¹)²(x) |
|-------|-----------------|
| 0     | 5               |
| 1     | 0               |
| 2     | 2               |
| 3     | 3               |
| 4     | 4               |
| 5     | 1               |
```
