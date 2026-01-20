# Handoff: 2026-01-20 (Session 33 continued)

## Completed This Session

### Infrastructure for ThreeCycleSymmetric.lean Sorries
Created helper files with computational verifications and structural lemmas:

**SymmetricCase1Helpers.lean** (115 lines):
- `g₂_k0_eq`: g₂ when k=0 equals formPerm of core list only
- `g₂_fixes_val_ge_6`: g₂ fixes elements ≥ 6 when k=0
- `threeCycle_3_4_5`: The 3-cycle (3,4,5) definition
- `threeCycle_3_4_5_isThreeCycle`: Proof it's a 3-cycle
- Computational verifications for n∈{0..3}, m∈{1..3}

**SymmetricCase2Helpers.lean** (95 lines):
- `iteratedComm_g₂'`: The iterated commutator [[g₁,g₂], g₂]
- `threeCycle_1_2_3`: The 3-cycle (1,2,3) definition
- `threeCycle_1_2_3_isThreeCycle`: Proof it's a 3-cycle
- Computational verifications for various (n,k,m)

**Updated ThreeCycleSymmetric.lean** (117 lines):
- Added imports for helper files
- Improved documentation on structural proof approach

---

## Current State

### Build Status: PASSING

### Sorry Count: 6 total (unchanged)
| Location | Description | Difficulty |
|----------|-------------|------------|
| ThreeCycleSymmetric.lean:57 | m≥1, k=0 case | Medium |
| ThreeCycleSymmetric.lean:84 | k≥1 case | Medium |
| Primitivity (4 sorries) | Includes known bug | N/A |

### No LOC Violations

---

## 🎯 RECOMMENDED NEXT TARGET: ThreeCycleSymmetric.lean:57

### Why This Sorry?
- Helper infrastructure already created
- Structural approach clearly documented
- Symmetric to ThreeCycleProof.lean pattern

### The Structural Proof Pattern

Both sorries follow the same pattern as ThreeCycleProof.lean:

1. **Prove squared product = threeCycle via extensionality**
2. **Use threeCycle_isThreeCycle**

### Case 1 (m≥1, k=0): Prove for each element

```lean
-- Need to prove:
(c₁₃_times_c₂₃_inv n m) ^ 2 = SymmetricCase1.threeCycle_3_4_5 n m

-- Element-wise:
| x.val | Expected result |
|-------|-----------------|
| 0     | 0 (fixed)       |
| 1     | 1 (fixed)       |
| 2     | 2 (fixed)       |
| 3     | 4               |
| 4     | 5               |
| 5     | 3               |
| ≥6    | x (fixed)       |
```

### Case 2 (k≥1): Prove for each element

```lean
-- Need to prove:
(SymmetricCase2.iteratedComm_g₂' n k m) ^ 2 = SymmetricCase2.threeCycle_1_2_3 n k m

-- Element-wise:
| x.val | Expected result |
|-------|-----------------|
| 0     | 0 (fixed)       |
| 1     | 2               |
| 2     | 3               |
| 3     | 1               |
| 4     | 4 (fixed)       |
| 5     | 5 (fixed)       |
| ≥6    | x (fixed)       |
```

---

## Required Helper Lemmas

### For Case 1 (m≥1, k=0)

Need lemmas similar to ProductLemmas.lean but for c₁₃ and c₂₃:

```lean
-- Single application values:
-- (c₁₃ * c₂₃⁻¹)(0) = 1, (c₁₃ * c₂₃⁻¹)(1) = 0, etc.

-- Squared action lemmas:
theorem sq_3_eq_4 : (c₁₃_times_c₂₃_inv n m ^ 2) ⟨3, _⟩ = ⟨4, _⟩
theorem sq_4_eq_5 : (c₁₃_times_c₂₃_inv n m ^ 2) ⟨4, _⟩ = ⟨5, _⟩
theorem sq_5_eq_3 : (c₁₃_times_c₂₃_inv n m ^ 2) ⟨5, _⟩ = ⟨3, _⟩
-- etc. for fixed points
```

### For Case 2 (k≥1)

Similar lemmas for the iterated commutator:

```lean
theorem sq_1_eq_2 : (iteratedComm_g₂' n k m ^ 2) ⟨1, _⟩ = ⟨2, _⟩
theorem sq_2_eq_3 : (iteratedComm_g₂' n k m ^ 2) ⟨2, _⟩ = ⟨3, _⟩
theorem sq_3_eq_1 : (iteratedComm_g₂' n k m ^ 2) ⟨3, _⟩ = ⟨1, _⟩
-- etc.
```

---

## Key Learnings

### 1. Symmetry Between Cases

| Case | Condition | Empty Tail | Product | 3-Cycle |
|------|-----------|------------|---------|---------|
| n≥1, m=0 | tailC empty | g₃ | c₁₂*c₁₃⁻¹ | (0,5,1) |
| m≥1, k=0 | tailB empty | g₂ | c₁₃*c₂₃⁻¹ | (3,4,5) |
| k≥1 | - | - | [[g₁,g₂],g₂] | (1,2,3) |

### 2. Computational Verification First

Use #eval to verify expected values before writing structural proofs:
```lean
#eval (c₁₃_times_c₂₃_inv 1 1 ^ 2) ⟨3, by omega⟩  -- expect 4
```

---

## Files Modified This Session
- AfTests/ThreeCycle/SymmetricCase1Helpers.lean (NEW)
- AfTests/ThreeCycle/SymmetricCase2Helpers.lean (NEW)
- AfTests/ThreeCycle/ThreeCycleSymmetric.lean (MODIFIED)
- AfTests/Scratch/SymmetricCycleVerify.lean (NEW, scratch)

---

## Generator Reference for Symmetric Cases

### When k = 0 (Case 1)
```
g₁ = formPerm [0, 5, 3, 2, 6, ..., 5+n]     (core + tailA)
g₂ = formPerm [1, 3, 4, 0]                   (core only, no tailB!)
g₃ = formPerm [2, 4, 5, 1, 6+n, ..., 5+n+m] (core + tailC)
```

### When k ≥ 1 (Case 2)
```
g₁, g₂, g₃ all have their normal structures
iteratedComm_g₂' = c₁₂⁻¹ * g₂⁻¹ * c₁₂ * g₂ = [[g₁,g₂], g₂]
```

---

## Session Close Checklist
- [x] Build passes
- [x] No new LOC violations
- [ ] HANDOFF.md updated
- [ ] Changes committed and pushed
