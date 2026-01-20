# Handoff: 2026-01-20 (Session 30 - Continued)

## Completed This Session

### TailLemmas.lean - TailB Proofs Complete
- Proved `c₁₂_fixes_tailB`: c₁₂ fixes all tailB elements (indices 6+n to 5+n+k)
- Key technique: formPerm cycle wrapping via `List.formPerm_apply_getElem`
- Proved `c₁₃_inv_fixes_tailB`: c₁₃⁻¹ fixes tailB when m = 0
- Proved `product_fixes_tailB` and `sq_fixes_tailB`

### Technical Details
- The c₁₂_fixes_tailB proof handles two cases:
  1. When g₂(x) stays in tailB: direct via g₁ fixing tailB
  2. When g₂(x) wraps to core (x = 5+n+k): formPerm cycle wrapping shows g₂(5+n+k) = 1

## Current State

### Build Status: PASSING
All files compile with sorries as placeholders.

### Sorry Count: 8 total
- ThreeCycle: 4 sorries
- Primitivity: 4 sorries (includes known bug)

### ThreeCycle Sorries (4)
1. **ThreeCycleProof.lean:121** - 6 core element cases
   - `interval_cases x.val <;> sorry`
   - Need to prove (c₁₂ * c₁₃⁻¹)² action on elements 0-5

2. **ThreeCycleSymmetric.lean:54** - `isThreeCycle_m_ge1_k0`
   - Symmetric case when m ≥ 1 and k = 0

3. **ThreeCycleSymmetric.lean:77** - `isThreeCycle_k_ge1`
   - Uses iterated commutator [[g₁,g₂], g₂]

4. **TailLemmas.lean:192** - `sq_fixes_tailA`
   - Complex: c₁₂ does NOT fix tailA elements directly
   - Need to show (c₁₂ * c₁₃⁻¹)² fixes via 2-cycle cancellation

## Next Steps (Priority Order)

### 1. sq_fixes_tailA (Most Complex)
**Key Insight**: c₁₂ maps tailA elements in 2-cycles, not identity!
- For x = 5+n (last tailA): c₁₂(5+n) = 4, c₁₂(4) = 0, c₁₂(0) = 5+n
- This forms a 3-cycle: (5+n, 4, 0)
- Need to show that (c₁₂ * c₁₃⁻¹)² eliminates this via squaring

**Strategy**:
- Analyze c₁₂ * c₁₃⁻¹ action on tailA
- Show it has order dividing 2 on tailA elements
- Therefore squaring gives identity

### 2. Core Element Proofs (ThreeCycleProof.lean:121)
For each element 0-5, prove:
```
(c₁₂_times_c₁₃_inv n k 0 ^ 2) ⟨i, _⟩ = threeCycle_0_5_1 n k ⟨i, _⟩
```

Expected values:
| x.val | (c₁₂*c₁₃⁻¹)²(x) | threeCycle(x) |
|-------|-----------------|---------------|
| 0     | 5               | 5             |
| 1     | 0               | 0             |
| 2     | 2               | 2             |
| 3     | 3               | 3             |
| 4     | 4               | 4             |
| 5     | 1               | 1             |

### 3. Symmetric Cases (ThreeCycleSymmetric.lean)
Apply same structural argument with roles swapped.

## Files Modified This Session
- AfTests/ThreeCycle/TailLemmas.lean (major rewrite - 192 LOC)

## Technical Notes

### formPerm Cycle Wrapping
The key lemma for last-element wrapping is:
```lean
List.formPerm_apply_getElem l nodup (l.length - 1) h :
  formPerm l (l[l.length - 1]) = l[0]
```
This follows from `(len - 1 + 1) % len = 0`.

### Generator Cycle Structures
```
g₁ = [0, 5, 3, 2, 6, ..., 5+n]      -- core + tailA
g₂ = [1, 3, 4, 0, 6+n, ..., 5+n+k]  -- core + tailB
g₃ = [2, 4, 5, 1, 6+n+k, ...]       -- core + tailC (empty when m=0)
```

## DO NOT
- ❌ Use `native_decide` for general n, k, m
- ❌ Add files without checking LOC limit (200 lines max)
- ❌ Leave debugging code or verbose comments

## DO
- ✅ Use structural lemmas about formPerm
- ✅ Leverage existing Transitivity.g*_list_getElem_* lemmas
- ✅ Factor reusable proofs into helper lemmas
