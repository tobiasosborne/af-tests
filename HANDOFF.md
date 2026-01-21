# Handoff: 2026-01-21 (Session 44)

## Completed This Session

### Proved Two Orbit Computation Sorries
- **`g₂_pow_b₁_eq_tailB_elem`**: Proved using `List.formPerm_pow_apply_getElem`
  - Shows g₂^j(b₁) = 6+n+j for j < k
  - Key insight: Element at index 4+j in g₂ list is tailB[j]

- **`g₃_pow_c₁_eq_tailC_elem`**: Symmetric proof for g₃
  - Shows g₃^j(c₁) = 6+n+k+j for j < m

### Critical Discovery: FALSE THEOREMS

**`g₂_pow_orbit_hits_core` and `g₃_pow_orbit_hits_core` ARE FALSE AS STATED!**

**Counterexample** for j=6, k=8:
- g₂ cycle length = 12
- gcd(6, 12) = 6
- Orbit of position 4 under +6 (mod 12) = {4, 10}
- Both positions 4 and 10 are in tailB (positions 4-11 for k=8)
- **The orbit NEVER exits tailB!**

The theorem claims `∃ r ≥ 1, g₂^{rj}(b₁) ∉ tailB`, but for j=6, k=8 the orbit stays at {6+n, 6+n+6} forever.

**Root Cause**: When gcd(j, 4+k) ≥ 5, the orbit from position 4 only visits positions ≡ 4 (mod gcd), and none of {0,1,2,3} satisfy this.

**The theorem IS true when gcd(j, 4+k) ≤ 4** because:
- gcd=1: 3 ≡ 4 (mod 1) ✓
- gcd=2: 2 ≡ 4 (mod 2) ✓
- gcd=3: 1 ≡ 4 (mod 3) ✓
- gcd=4: 0 ≡ 4 (mod 4) ✓

---

## Current State

### Build Status: PASSING ✓

### Axiom Count: 0

### Sorry Count: 5 total
| Location | Description | Status |
|----------|-------------|--------|
| Lemma11_5_OrbitHelpers_TailB.lean:143 | `g₂_pow_orbit_hits_core` | **FALSE - needs redesign** |
| Lemma11_5_OrbitHelpers_TailC.lean:140 | `g₃_pow_orbit_hits_core` | **FALSE - needs redesign** |
| Lemma11_5_Case2.lean:170 | `case2_impossible` | Needs block hypothesis |

---

## Key Technical Details

### Why This Breaks the Proof

The proof strategy in `case2_impossible_B` (Lemma11_5_SymmetricMain.lean:136-193):
1. Finds second element x ∈ B at distance j from b₁
2. Shows g₂^j(B) = B using block property
3. Iterates: g₂^{rj}(B) = B for all r
4. Claims orbit eventually exits tailB ← **FALSE for gcd(j, 4+k) ≥ 5**

### Potential Fixes

**Option 1**: Add hypothesis `Nat.gcd j (4 + k) ≤ 4`
- Need to prove this holds in the call context (may not always be true)

**Option 2**: Different proof strategy
- Instead of orbit argument, use block system partition properties
- The g₂ orbit of B visits (4+k)/|B| blocks total
- Only k/|B| blocks can fit entirely in tailB
- Since (4+k)/|B| > k/|B|, some block must intersect core
- Derive contradiction from H-invariance constraints

**Option 3**: Restrict to specific n,k,m values
- The counterexamples require k ≥ 6 (for j=5) or k ≥ 8 (for j=6)
- Small k cases might be handled separately

---

## Files Modified This Session
- `Lemma11_5_OrbitHelpers_TailB.lean` (proved one sorry, documented false theorem)
- `Lemma11_5_OrbitHelpers_TailC.lean` (proved one sorry, documented false theorem)

---

## Next Session Priority

### Task 1: Fix Case 2 Proof Strategy (P0)
The orbit argument doesn't work. Need to either:
1. Add gcd hypothesis and verify it's satisfied
2. Find alternative proof that B ⊆ tailB leads to contradiction
3. Use block counting argument (see Option 2 above)

### Task 2: Understand Block System Constraints
Key question: Can B = {6+n, 6+n+6} actually exist in a valid H-invariant block system?
- Need to analyze if the counterexample scenario is actually reachable
- The block system must partition ALL of Ω, not just tailB

---

## Session Close Checklist
- [x] Build passes
- [x] HANDOFF.md updated
- [ ] Changes committed and pushed
- [ ] Beads synced
