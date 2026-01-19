# Handoff: 2026-01-19 (Session 23)

## Completed This Session

- **Analyzed `case2_B_ncard_le_one` theorem** in `Lemma11_5_Case2_Helpers.lean`
  - **CRITICAL FINDING**: The theorem as stated is FALSE for n >= 3
  - Counterexample: B = {6, 8} for n = 3 satisfies all hypotheses but |B| = 2
  - Root cause: `g_1(B) cap B = emptyset` does NOT imply `g_1^2(B) cap B = emptyset`
  - The AF proof (Node 1.9.5) uses a different approach - does NOT claim |B| <= 1

- **Created issue af-tests-5jc** to track the required redesign

- **Updated documentation** with detailed explanation of the bug and correct approach

## Current State

- **Build status**: PASSING
- **Sorry count**: **8** (unchanged - this sorry cannot be eliminated, needs redesign)
- **Open P0 issues**: None
- **Open P1 issues**: 1 (af-tests-5jc - theorem redesign)

## The Case 2 Bug Explained

The theorem `case2_B_ncard_le_one` attempts to prove |B| <= 1 given:
1. B cap supp(g_2) = emptyset
2. B cap supp(g_3) = emptyset
3. g_1(B) cap B = emptyset
4. a_1 in B

For n = 3, B = {6, 8} satisfies all these but:
- g_1({6, 8}) = {7, 0}
- g_1^2({6, 8}) = {8, 5}
- {8, 5} cap {6, 8} = {8} != emptyset

So B cannot be a proper block in a g_1-invariant block system, but the theorem doesn't require that!

The correct approach (per AF Node 1.9.5) requires B to be a proper block where the FULL orbit under g_1 consists of pairwise disjoint sets.

## Remaining Sorries

| File | Line | Description | Status |
|------|------|-------------|--------|
| Lemma03.lean | 138 | H_6_iso_S4 (tetrahedral isomorphism) | Hard |
| Lemma11.lean | 82 | block_to_system (type coercion) | Medium |
| Lemma11_5.lean | 156 | Symmetric case (k>=1 or m>=1) | Easy |
| Lemma11_5_Case2_Helpers.lean | 155 | case2_B_ncard_le_one | **BLOCKED - needs redesign** |
| MainTheorem.lean | 109, 117, 138, 153 | Main theorem assembly | Medium |

## Next Steps (Priority Order)

1. **Redesign case2_impossible** (af-tests-5jc)
   - Option A: Add hypothesis that B is a proper block (orbit pairwise disjoint)
   - Option B: Follow AF proof - use orbit structure with element 0 in supp(g_1) cap supp(g_2)
   - The correct contradiction is |B| = N (full space), not |B| <= 1

2. **Lemma11_5.lean:156** - Symmetric case for k>=1/m>=1

3. **Lemma11.lean:82** - `block_to_system` type coercion

4. **MainTheorem.lean** - Assembly of lemmas

5. **Lemma03.lean:138** - H_6_iso_S4 tetrahedral isomorphism

## Known Issues / Gotchas

- **Beads prefix mismatch**: `bd sync` fails with prefix error. Use `--rename-on-import` flag.

- **Case 2 is fundamentally broken**: The current approach cannot work without additional block system hypotheses.

- **Index convention**: AF 1-indexed, Lean 0-indexed. AF {1,4,6} = Lean {0,3,5}

## Files Modified This Session

- `AfTests/Primitivity/Lemma11_5_Case2_Helpers.lean` (documented bug, updated docstring)

## Issue Status

- **af-tests-5jc** (case2_B_ncard_le_one redesign): OPEN - P1 bug
- **af-tests-qvq** (Lemma11_5): IN PROGRESS - blocked by af-tests-5jc
- **af-5zd** (Lemma11 H_primitive): OPEN
