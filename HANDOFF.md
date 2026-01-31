# Handoff: 2026-01-31 (Session 71)

## Completed This Session

- **Import cycle fixed**: Removed unnecessary import of Primitive.lean from Peirce.lean
- **Proof structure for orthogonal_primitive_peirce_sq**: Added helper lemma and decomposition steps
- **FinDimJordanAlgebra hypothesis added**: Theorems now match H-O 2.9.4 assumptions

### Key Technical Changes

1. **Removed `import AfTests.Jordan.Primitive` from Peirce.lean** — it wasn't used and created a cycle
2. **Added `import AfTests.Jordan.Peirce` to Primitive.lean** — enables use of Peirce multiplication rules
3. **New helper lemma `primitive_peirce_one_scalar`** — key characterization: P₁(e) = ℝe for primitive e
4. **Structured proof of `orthogonal_primitive_peirce_sq`** — decomposes into clear steps using Peirce tools

---

## Current State

| Metric | Value |
|--------|-------|
| Total Sorries | ~26 (added 1 helper lemma sorry) |
| Build Status | PASSING |

### Primitive.lean Status (5 sorries)

| Line | Theorem | Status | Notes |
|------|---------|--------|-------|
| 95 | `primitive_peirce_one_scalar` | NEW | Key helper: P₁(e) = ℝe |
| 122 | `orthogonal_primitive_peirce_sq` | IN PROGRESS | H-O 2.9.4(iv), proof structured |
| 134 | `orthogonal_primitive_structure` | BLOCKED | Depends on peirce_sq |
| 167 | `exists_primitive_decomp` | BLOCKED | Needs primitivity characterization |
| 174 | `csoi_refine_primitive` | BLOCKED | Depends on exists_primitive_decomp |

---

## Next Steps (Priority Order)

### 1. Prove `primitive_peirce_one_scalar` (P1) - af-lhxr
**Key missing lemma.** Shows that for primitive e, PeirceSpace e 1 = ℝe.

**Proof strategy:**
- In finite-dim formally real Jordan algebra, if dim(P₁(e)) > 1
- Then P₁(e) contains non-scalar elements
- The subalgebra {eAe} = P₁(e) is itself a Jordan algebra with identity e
- In a formally real Jordan algebra of dim > 1, there exist non-trivial idempotents
- This contradicts primitivity of e

**Requires:** May need spectral theorem for finite-dim subalgebras (circular?)

### 2. Complete `orthogonal_primitive_peirce_sq` proof (P1)
Once `primitive_peirce_one_scalar` is proven:
- Steps 1-3 are written (decomposition, obtain scalars)
- Step 4: Show r₁ = r₂ (coefficients equal)
- Step 5: Show μ ≥ 0 (formal reality)

### 3. Chain through to spectral theory
- `orthogonal_primitive_structure` → uses peirce_sq
- `exists_primitive_decomp` → induction using primitivity
- `csoi_refine_primitive` → uses decomp

---

## Key Insight: Potential Circularity

The proof of `primitive_peirce_one_scalar` may require showing that finite-dimensional
formally real Jordan algebras have idempotents (from spectral theory). But spectral
theory depends on primitivity.

**Options:**
1. **Axiomatize**: Add P₁(e) = ℝe as part of primitive definition for fin-dim case
2. **Direct proof**: Show P₁(e) = ℝe without full spectral theorem
3. **Literature search**: Check H-O for how they prove this

Recommend checking H-O Section 2.9 more carefully for the exact proof.

---

## Files Modified This Session

- `AfTests/Jordan/Peirce.lean` — Removed import of Primitive.lean
- `AfTests/Jordan/Primitive.lean` — Added Peirce import, helper lemma, structured proof
- `HANDOFF.md` — This file

---

## Issue Status

| Issue | Status | Notes |
|-------|--------|-------|
| af-lhxr | IN PROGRESS | orthogonal_primitive_peirce_sq |
| af-4g40 | OPEN | Spectral sorry elimination, blocked |
| af-hbnj | OPEN | exists_primitive_decomp |
| af-5zpv | OPEN (P0) | JordanTrace needs instances |
