# Handoff: 2026-01-20 (Session 27)

## Completed This Session

- **Analyzed main theorem structure** - The proof chain is complete; only 3-cycle extraction sorries block it
- **Developed alternate strategy**: Prove `(c₁₂ * c₁₃⁻¹)² = threeCycle_0_5_1 n k` via `Equiv.Perm.ext`
- **Created ThreeCycleProof.lean** - New helper file with:
  - `g₃_fixes_ge6`: g₃ fixes elements ≥ 6 when m = 0
  - `threeCycle_fixes_ge6`: threeCycle_0_5_1 fixes elements ≥ 6
  - `threeCycle_fixes_2`, `threeCycle_fixes_3`, `threeCycle_fixes_4`: core fixes
  - Computational verifications for n,k ∈ {1..5}
- **Verified computationally**:
  - `(c₁₂_times_c₁₃_inv n k 0)² = threeCycle_0_5_1 n k` for all tested (n,k)
  - c₁₂ * c₁₃⁻¹ has cycle structure: (0 1 5)(2 3)(4 6) for n=1, k=0
  - Squaring: 2-cycles vanish, 3-cycle remains as (0 5 1)

## Current State

- **Build status**: ✅ PASSING (1895 jobs)
- **Sorry count**: **8** (4 in MainTheorem+ThreeCycleProof, 3 in Primitivity, 1 BUG)
- **Open P0 issues**: None

## Remaining Sorries

| File | Line | Description | Status |
|------|------|-------------|--------|
| MainTheorem.lean | 73 | c₁₂_times_c₁₃_inv_squared_isThreeCycle_n_m0 | **Critical** - blocks main theorem |
| MainTheorem.lean | 81 | c₁₃_times_c₂₃_inv_squared_isThreeCycle_m_k0 | Symmetric to above |
| MainTheorem.lean | 104 | iteratedComm_g₂_squared_isThreeCycle | Same pattern |
| ThreeCycleProof.lean | 148 | sq_isThreeCycle_n_ge1_m0 | Duplicate (modular proof) |
| Lemma11_5_SymmetricMain.lean | 159 | case2_impossible_B | Orbit structure |
| Lemma11_5_SymmetricMain.lean | 181 | case2_impossible_C | Orbit structure |
| Lemma11_5_Case2_Helpers.lean | 155 | case2_B_ncard_le_one | **FALSE** - needs redesign |

## Key Discovery: Permutation Equality Strategy

### New Approach

Instead of cycle type extraction, prove permutation equality directly:
```
(c₁₂_times_c₁₃_inv n k 0)² = threeCycle_0_5_1 n k
```

Then use existing `threeCycle_0_5_1_isThreeCycle` theorem.

### Why This Works

Both permutations:
1. Act on Omega n k 0 (same type)
2. Map 0 → 5 → 1 → 0 (the 3-cycle action)
3. Fix all elements not in {0, 1, 5}

### Proof Steps

1. Use `Equiv.Perm.ext`: reduce to showing agreement on all elements
2. For x.val ∈ {0, 1, 5}: Show same action (both follow 3-cycle)
3. For x.val ∈ {2, 3, 4}: Both fix (computationally verified)
4. For x.val ≥ 6: Both fix (structural: g₃_fixes_ge6 + threeCycle_fixes_ge6)

### Implementation Barrier

The challenge is proving agreement for arbitrary n, k. Currently:
- Steps 2-3 verified computationally for n,k ∈ {1..5}
- Step 4 has structural proofs (in ThreeCycleProof.lean)
- Need to connect these for the general case

## Next Steps (Priority Order)

1. **Complete permutation equality proof** (ThreeCycleProof.lean)
   - Show `(c₁₂ * c₁₃⁻¹)²` and `threeCycle_0_5_1` agree on all elements
   - Key: use structural lemmas for tail elements, computational facts for core

2. **Handle symmetric cases** (MainTheorem:81, 104)
   - Same pattern with different generator combinations

3. **Fix Lemma11_5 orbit arguments** (2 sorries)
   - These are simpler once 3-cycle proofs are done

4. **Redesign Case2 approach** (FALSE theorem)
   - Need different proof strategy per AF Node 1.9.5

## Files Modified This Session

### New Files
- `AfTests/ThreeCycle/ThreeCycleProof.lean` - Structural lemmas for 3-cycle extraction

### Modified
- `HANDOFF.md` - This file (updated)

## Known Issues / Gotchas

- **The 3-cycle is (0 5 1)** - Squaring reverses direction: (0 1 5)² = (0 5 1)
- **c₁₂ * c₁₃⁻¹ cycle structure**: (0 1 5)(2 3)(4 6...) varies with n, k
- **Index convention**: AF 1-indexed, Lean 0-indexed
- **FALSE theorem**: Lemma11_5_Case2_Helpers:155 needs complete redesign

## Main Theorem Dependency Chain

```
main_theorem
  └── lemma15_H_classification ✅
       └── H_contains_alternating (Jordan) ✅
            └── H_contains_threecycle ← BLOCKED (3 sorries)
                 ├── c₁₂_times_c₁₃_inv_squared_isThreeCycle_n_m0 (n≥1, m=0)
                 ├── c₁₃_times_c₂₃_inv_squared_isThreeCycle_m_k0 (m≥1, k=0)
                 └── iteratedComm_g₂_squared_isThreeCycle (k≥1)
```

The main theorem is 3 sorries away from completion!
