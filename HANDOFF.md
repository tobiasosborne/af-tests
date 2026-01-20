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

### 1. sq_fixes_tailA - CORRECTED ANALYSIS (Session 31)

**⚠️ PREVIOUS HANDOFF WAS WRONG** - The cycle structure was incorrectly described.

**VERIFIED COMPUTATIONALLY** (via #eval in Lean):

The product `c₁₂ * c₁₃⁻¹` has cycle structure (for m=0):
```
Core: (0 1 5) 3-cycle, (2 3) 2-cycle
TailA + element 4: varies by n
```

**Actual action table for n=2, k=0, m=0:**
| x | (c₁₂*c₁₃⁻¹)(x) | Notes |
|---|----------------|-------|
| 0 | 1 | 3-cycle |
| 1 | 5 | 3-cycle |
| 2 | 3 | 2-cycle |
| 3 | 2 | 2-cycle |
| 4 | 7 | 2-cycle with last tailA! |
| 5 | 0 | 3-cycle |
| 6 | 6 | FIXED! |
| 7 | 4 | 2-cycle with 4 |

**Key Pattern by n:**
- n=1: tailA={6}, and 4↔6 is a 2-cycle
- n=2: tailA={6,7}, element 6 FIXED, 4↔7 is a 2-cycle
- n=3: tailA={6,7,8}, elements 6,7 FIXED, 4↔8 is a 2-cycle
- General: First tailA elements fixed, LAST tailA (5+n) forms 2-cycle with 4

**Why sq_fixes_tailA is TRUE:**
- Most tailA elements are FIXED by c₁₂*c₁₃⁻¹ (not in 2-cycles!)
- Only the LAST tailA element (5+n) forms 2-cycle with core element 4
- Squaring eliminates all 2-cycles → all tailA fixed

**Proof Strategy:**
1. Case x = 5+n (last tailA): Show 4↔(5+n) 2-cycle, squaring gives identity
2. Case 6 ≤ x < 5+n: Show c₁₂*c₁₃⁻¹ fixes x directly (no squaring needed)

**WARNING: 200 LOC LIMIT**
- TailLemmas.lean is at 194 lines
- Adding helper lemmas for full structural proof exceeds limit
- Consider: Create TailAHelpers.lean for helper lemmas, or use more compact proof style

**Commutator conventions (CRITICAL):**
```lean
commutator_g₁_g₂ = g₁⁻¹ * g₂⁻¹ * g₁ * g₂
-- Application: commutator(x) = g₂(g₁(g₂⁻¹(g₁⁻¹(x))))
-- In Lean: (f * g)(x) = f(g(x))  -- LEFT multiplication!
```

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
- ❌ Trust the HANDOFF blindly - verify computationally with #eval!

## DO
- ✅ Use structural lemmas about formPerm
- ✅ Leverage existing Transitivity.g*_list_getElem_* lemmas
- ✅ Factor reusable proofs into helper lemmas
- ✅ Verify cycle structures with #eval before writing proofs

## Session 31 Learnings (CRITICAL FOR NEXT AGENT)

### What Was Attempted
Tried to prove `sq_fixes_tailA` with full structural proof. Approach:
1. Prove helper lemmas for each generator action
2. Chain them to show c₁₃⁻¹ and c₁₂ actions
3. Show 2-cycle structure and squaring

### Why It Failed
1. **LOC explosion**: Helper lemmas grew file to 351 lines (limit: 200)
2. **Case complexity**: Different proofs needed for n=1 vs n≥2
3. **Inverse tracing**: g₁⁻¹(5+n) = different values depending on n

### What WOULD Work
1. **Split file**: Create `TailAHelpers.lean` for intermediate lemmas
2. **Minimal case split**: Only handle last tailA element specially
3. **Computational verification**: Use #eval to double-check before proof

### Useful Lean Commands for Debugging
```lean
-- Verify specific actions:
#eval c₁₂_times_c₁₃_inv 2 0 0 ⟨7, by omega⟩  -- gives 4
#eval (c₁₂_times_c₁₃_inv 2 0 0)^2 ⟨7, by omega⟩  -- gives 7 (fixed!)

-- Check intermediate steps:
#eval (commutator_g₁_g₃ 2 0 0)⁻¹ ⟨6, by omega⟩  -- c₁₃⁻¹(6)
#eval commutator_g₁_g₂ 2 0 0 ⟨4, by omega⟩  -- c₁₂(4)
```

### Alternative Approach to Consider
The core element sorry at **ThreeCycleProof.lean:121** might be EASIER:
- It's `interval_cases x.val <;> sorry` for 6 cases (0-5)
- Each case is independent
- Can prove them one at a time with formPerm lemmas
- Core elements have FIXED positions in all generator cycles

### Key Helper Lemmas That Exist
```lean
-- In Transitivity/Lemma05ListProps.lean:
Transitivity.g₁_list_getElem_tail  -- Access tailA elements in g₁ list
Transitivity.g₂_list_getElem_tail  -- Access tailB elements in g₂ list

-- In ThreeCycleExtractHelpers.lean:
ThreeCycleExtract.g₃_fixes_val_ge_6  -- g₃ fixes elements ≥ 6 when m=0
ThreeCycleExtract.g₃_m0_eq  -- g₃ = formPerm [2,4,5,1] when m=0

-- In TailLemmas.lean:
g₁_fixes_tailB, g₁_fixes_1  -- g₁ fixing lemmas
```
