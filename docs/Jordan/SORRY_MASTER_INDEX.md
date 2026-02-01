# Jordan Algebra Sorry Elimination: Master Index

**Generated:** 2026-02-01
**Total Sorries:** 21
**Estimated Total LOC:** 600-800

---

## Quick Reference: All Sorries

| # | File | Theorem | Line | Difficulty | LOC | Priority |
|---|------|---------|------|------------|-----|----------|
| 1 | Primitive.lean | `lagrange_idempotent_in_peirce_one` (coeff) | 261 | EASY | 15-20 | P0 |
| 2 | Primitive.lean | `primitive_peirce_one_dim_one` | 322 | MEDIUM-HARD | 60-80 | P1 |
| 3 | Primitive.lean | `orthogonal_primitive_peirce_sq` | 390 | HARD | 60-80 | P2 |
| 4 | Primitive.lean | `orthogonal_primitive_structure` | 402 | MEDIUM | 40-55 | P2 |
| 5 | Primitive.lean | `exists_primitive_decomp` | 435 | HARD | 90-120 | P2 |
| 6 | Primitive.lean | `csoi_refine_primitive` | 442 | MEDIUM-HARD | 70-90 | P2 |
| 7 | FundamentalFormula.lean | `linearized_jordan_aux` | 54 | MEDIUM | 30-40 | P1 |
| 8 | FundamentalFormula.lean | `fundamental_formula` | 83 | HARD | 80-120 | P1 |
| 9 | OperatorIdentities.lean | `L_e_L_a_L_e` | 172 | MEDIUM | 15 | P1 |
| 10 | OperatorIdentities.lean | `opComm_double_idempotent` | 179 | MEDIUM | 25 | P1 |
| 11 | Quadratic.lean | `U_idempotent_comp` | 134 | MEDIUM | 35 | P2 |
| 12 | SpectralTheorem.lean | `spectral_decomposition_exists` | 59 | HARD | 80-100 | P2 |
| 13 | SpectralTheorem.lean | `spectral_decomposition_finset` | 71 | MEDIUM | 20-30 | P2 |
| 14 | SpectralTheorem.lean | `spectrum_eq_eigenvalueSet` | 80 | MEDIUM-HARD | 30-40 | P2 |
| 15 | SpectralTheorem.lean | `spectrum_sq` | 159,162 | MEDIUM | 40-50 | P2 |
| 16 | SpectralTheorem.lean | `sq_eigenvalues_nonneg` | 173 | EASY | 15-20 | P3 |
| 17 | FormallyReal/Def.lean | `of_sq_eq_zero` (case 1) | 75 | BLOCKED | 0 | - |
| 18 | FormallyReal/Def.lean | `of_sq_eq_zero` (case 2) | 80 | BLOCKED | 0 | - |
| 19 | FormallyReal/Square.lean | `isPositiveSqrt_unique` | 102 | MEDIUM | 40-50 | P3 |
| 20 | FormallyReal/Square.lean | `HasPositiveSqrt.of_positiveElement` | 118 | HARD | 60-80 | P3 |
| 21 | FormallyReal/Spectrum.lean | `spectral_sq_eigenvalues_nonneg` | 136 | MEDIUM | 30-40 | P3 |
| 22 | Classification/RealSymmetric.lean | `isSimple` | 81 | MEDIUM | 80-90 | P2 |
| 23 | Classification/ComplexHermitian.lean | `isSimple` | 78 | MEDIUM | 80-90 | P2 |

---

## Dependency Graph

```
                    ┌─────────────────────────────────────┐
                    │  INDEPENDENT TRACKS                 │
                    └─────────────────────────────────────┘
                              │
        ┌─────────────────────┼─────────────────────┐
        │                     │                     │
        ▼                     ▼                     ▼
   ┌─────────┐         ┌───────────┐         ┌─────────────┐
   │ TRACK A │         │  TRACK B  │         │   TRACK C   │
   │ Operator│         │ Primitive │         │Classification│
   │ Theory  │         │  Theory   │         │  (Matrix)   │
   └────┬────┘         └─────┬─────┘         └──────┬──────┘
        │                    │                      │
        ▼                    ▼                      │
   #9,10 opComm         #1 lagrange_coeff          │
        │                    │                      │
        ▼                    ▼                      │
   #7 linearized_aux    #2 peirce_one_dim          │
        │                    │                      │
        ▼                    ▼                      │
   #8 fundamental       #3,4,5,6 primitive         │
        │                structure                  │
        │                    │                      │
        ▼                    ▼                      ▼
   #11 U_idempotent     #12-16 Spectral        #22,23 isSimple
        │                Theorem                    │
        │                    │                      │
        └────────────────────┼──────────────────────┘
                             │
                             ▼
                    ┌────────────────┐
                    │  TRACK D       │
                    │ FormallyReal   │
                    │ (depends on    │
                    │  spectral)     │
                    └────────────────┘
                             │
                             ▼
                    #19,20,21 Square roots,
                    spectrum non-neg

                    (Sorries #17,18 are BLOCKED -
                     circular dependency, document as gap)
```

---

## Execution Order (Critical Path)

### Phase 1: Independent Quick Wins (Sessions 1-2)

| Session | Sorry # | Theorem | File | LOC | Notes |
|---------|---------|---------|------|-----|-------|
| 1 | #1 | `lagrange_idempotent_in_peirce_one` | Primitive.lean:261 | 15-20 | Pure algebra, no deps |
| 1 | #9,10 | `opComm_double_idempotent`, `L_e_L_a_L_e` | OperatorIdentities.lean | 40 | Algebraically equivalent |

### Phase 2: Primitive & Fundamental (Sessions 3-6)

| Session | Sorry # | Theorem | File | LOC | Notes |
|---------|---------|---------|------|-----|-------|
| 2 | #2 | `primitive_peirce_one_dim_one` | Primitive.lean:322 | 60-80 | Requires #1 |
| 3 | #7 | `linearized_jordan_aux` | FundamentalFormula.lean:54 | 30-40 | May be unnecessary |
| 3-4 | #8 | `fundamental_formula` | FundamentalFormula.lean:83 | 80-120 | Core theorem |
| 4 | #11 | `U_idempotent_comp` | Quadratic.lean:134 | 35 | Requires #8 |

### Phase 3: Primitive Structure (Sessions 5-7)

| Session | Sorry # | Theorem | File | LOC | Notes |
|---------|---------|---------|------|-----|-------|
| 5 | #3 | `orthogonal_primitive_peirce_sq` | Primitive.lean:390 | 60-80 | Requires #2 |
| 5 | #4 | `orthogonal_primitive_structure` | Primitive.lean:402 | 40-55 | Requires #2 |
| 6 | #5 | `exists_primitive_decomp` | Primitive.lean:435 | 90-120 | Requires #2,3,4 |
| 6 | #6 | `csoi_refine_primitive` | Primitive.lean:442 | 70-90 | Requires #5 |

### Phase 4: Spectral Theory (Sessions 7-9)

| Session | Sorry # | Theorem | File | LOC | Notes |
|---------|---------|---------|------|-----|-------|
| 7 | #12 | `spectral_decomposition_exists` | SpectralTheorem.lean:59 | 80-100 | Requires #6 |
| 8 | #13 | `spectral_decomposition_finset` | SpectralTheorem.lean:71 | 20-30 | Requires #12 |
| 8 | #14 | `spectrum_eq_eigenvalueSet` | SpectralTheorem.lean:80 | 30-40 | Requires #12 |
| 9 | #15 | `spectrum_sq` | SpectralTheorem.lean:159,162 | 40-50 | Requires #14 |
| 9 | #16 | `sq_eigenvalues_nonneg` | SpectralTheorem.lean:173 | 15-20 | Requires #15 |

### Phase 5: Classification (Sessions 8-10, PARALLEL with Phase 4)

| Session | Sorry # | Theorem | File | LOC | Notes |
|---------|---------|---------|------|-----|-------|
| 8-9 | #22 | `RealSymmetricMatrix.isSimple` | Classification/RealSymmetric.lean:81 | 80-90 | Matrix units approach |
| 9-10 | #23 | `ComplexHermitianMatrix.isSimple` | Classification/ComplexHermitian.lean:78 | 80-90 | Same approach |

### Phase 6: FormallyReal Cleanup (Sessions 10-12)

| Session | Sorry # | Theorem | File | LOC | Notes |
|---------|---------|---------|------|-----|-------|
| 10 | #21 | `spectral_sq_eigenvalues_nonneg` | FormallyReal/Spectrum.lean:136 | 30-40 | Requires #15 |
| 11 | #19 | `isPositiveSqrt_unique` | FormallyReal/Square.lean:102 | 40-50 | Requires spectral |
| 12 | #20 | `HasPositiveSqrt.of_positiveElement` | FormallyReal/Square.lean:118 | 60-80 | Requires spectral |

### Sorries to Document as Gaps (No Implementation)

| Sorry # | Theorem | File | Reason |
|---------|---------|------|--------|
| #17,18 | `of_sq_eq_zero` | FormallyReal/Def.lean:75,80 | Circular dependency with OrderedCone |

---

## Plan Documents

Detailed elimination strategies for each sorry:

| File | Plan Document |
|------|---------------|
| Primitive.lean | [PLAN_Primitive.md](./PLAN_Primitive.md) |
| SpectralTheorem.lean | [PLAN_SpectralTheorem.md](./PLAN_SpectralTheorem.md) |
| FundamentalFormula.lean | [PLAN_FundamentalFormula.md](./PLAN_FundamentalFormula.md) |
| FormallyReal/*.lean | [PLAN_FormallyReal.md](./PLAN_FormallyReal.md) |
| OperatorIdentities.lean, Quadratic.lean | [PLAN_OperatorIdentities.md](./PLAN_OperatorIdentities.md) |
| Classification/*.lean | [PLAN_Classification.md](./PLAN_Classification.md) |

---

## Summary Statistics

| Metric | Value |
|--------|-------|
| Total sorries | 23 |
| Actionable sorries | 21 |
| Blocked sorries (gaps) | 2 |
| Estimated total LOC | 600-800 |
| Estimated sessions | 10-12 |
| Independent parallel tracks | 3 (A: Operator, B: Primitive, C: Classification) |

---

## Getting Started

**Recommended first session:**
1. Start with Sorry #1 (`lagrange_idempotent_in_peirce_one` coefficient) - pure algebra, 15-20 LOC
2. Then tackle Sorries #9,10 (`opComm_double_idempotent`, `L_e_L_a_L_e`) - 40 LOC combined
3. Both are independent and unblock downstream work

**After that:**
- Follow the Phase order above
- Track C (Classification) can run in parallel with Tracks A and B
