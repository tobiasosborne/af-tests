# Handoff: 2026-01-20 (Session 25)

## Completed This Session

- **Created ThreeCycleExtractHelpers.lean** with:
  - Structural lemmas: `g₃_fixes_tailA`, `g₃_fixes_tailB`, `g₃_fixes_val_ge_6`
  - Key insight proved: When m=0, g₃ fixes all tail elements (indices ≥ 6)
  - Computational verification: `isThreeCycle_n1_k0`, `isThreeCycle_n2_k0`, etc.
  - General lemma: `threeCycle_0_5_1_isThreeCycle` proves c[0,5,1] is a 3-cycle for all n,k

- **Updated IMPLEMENTATION_PLAN.md** with Session 24 findings
  - Added Appendix E documenting current sorry status
  - Documented proof strategies for MainTheorem 3-cycle sorries
  - Noted Case 2 theorem is FALSE in Lemma11_5

## Current State

- **Build status**: PASSING (1895 jobs)
- **Sorry count**: **6** (unchanged)
- **Open P0 issues**: None

## Remaining Sorries

| File | Line | Description | Status |
|------|------|-------------|--------|
| MainTheorem.lean | 69 | c₁₂_times_c₁₃_inv_squared_isThreeCycle_n_m0 | Helpers ready, need general proof |
| MainTheorem.lean | 75 | c₁₃_times_c₂₃_inv_squared_isThreeCycle_m_k0 | Symmetric to above |
| MainTheorem.lean | 96 | iteratedComm_g₂_squared_isThreeCycle | Same pattern |
| Lemma11_5_SymmetricMain.lean | 159 | case2_impossible_B | Blocked - needs redesign |
| Lemma11_5_SymmetricMain.lean | 181 | case2_impossible_C | Blocked - needs redesign |
| Lemma11_5_Case2_Helpers.lean | 155 | case2_B_ncard_le_one | **FALSE** - theorem incorrect |

## Progress on MainTheorem 3-Cycle Proofs

### What's Been Proven

1. **g₃ fixes tail elements** (ThreeCycleExtractHelpers.lean:48-75)
   - `g₃_fixes_val_ge_6`: For x.val ≥ 6, g₃ n k 0 x = x
   - `g₃_fixes_tailA`, `g₃_fixes_tailB`: Specific for tailA/tailB predicates

2. **Computational verification** confirms pattern:
   - Support is always {0, 1, 5} for n ∈ {1,2,3}, k ∈ {0,2,3}, m=0
   - The 3-cycle is always c[0, 5, 1]
   - Cycle type before squaring: {3, 2, 2}

3. **threeCycle_0_5_1_isThreeCycle** (general):
   - Proves c[0,5,1] defined via formPerm is a 3-cycle for ALL n, k

### What's Still Needed

To eliminate the sorries, need to prove:
```lean
theorem sq_eq_threeCycle (n k : ℕ) (hn : n ≥ 1) :
    (c₁₂_times_c₁₃_inv n k 0) ^ 2 = threeCycle_0_5_1 n k
```

This would require:
1. Showing [g₁, g₃] fixes all tail elements (follows from g₃ fixing them)
2. Showing c₁₂ * c₁₃⁻¹ acts uniformly on core elements regardless of tail length
3. Showing the 2-cycles in c₁₂ * c₁₃⁻¹ get eliminated by squaring

## Next Steps (Priority Order)

1. **Complete MainTheorem 3-cycle general proof**
   - Try proving sq_eq_threeCycle by showing permutations are equal on all elements
   - Core elements: trace through formPerm actions
   - Tail elements: use g₃_fixes_tailA and related lemmas

2. **Symmetric cases** (lines 75, 96)
   - Apply same techniques with appropriate generator swaps

3. **Lemma11_5 redesign** (3 sorries)
   - Current approach is fundamentally flawed
   - Need to add block system hypothesis per AF Node 1.9.5

## Files Created/Modified This Session

### Created
- `AfTests/ThreeCycle/ThreeCycleExtractHelpers.lean` (183 LOC)

### Modified
- `AfTests/MainTheorem.lean` - Added import, updated sorry comments
- `IMPLEMENTATION_PLAN.md` - Added Appendix E with current status
- `HANDOFF.md` - This file

## Known Issues / Gotchas

- **Case 2 theorem FALSE**: Lemma11_5_Case2_Helpers.lean:155 is provably false for n≥3
- **Index convention**: AF 1-indexed, Lean 0-indexed. AF {1,4,6} = Lean {0,3,5}
- **native_decide warnings**: Lint warns about native_decide but it's necessary for computational proofs
