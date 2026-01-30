# Handoff: 2026-01-30 (Session 37)

## Completed This Session

### Sorry Elimination: Matrix/JordanProduct.lean

**Eliminated** the sorry at `IsHermitian.jordanMul` (line 72).

**Problem:** Conflicting `Star R` instances between section variables and theorem-local `[StarRing R]`.

**Solution:**
1. Restructured file into two sections: `Basic` (no Star) and `Hermitian` (only StarRing)
2. Proof uses `star_mul'`, `star_inv₀`, `star_ofNat`, and `hA.apply`/`hB.apply`
3. Final step: `simp only [eq1, eq2, add_comm]` where eq1/eq2 rewrite matrix entries

**Key insight:** The `[Star R]` in the original variable declaration conflicted with `[StarRing R]` which provides its own `Star` instance. Separating into sections resolved this.

### Analysis: FormallyReal/Def.lean:58

**NOT eliminated** - documented as requiring deeper theory.

**Problem:** `of_sq_eq_zero` tries to prove:
- Given: `∀ a, jsq(a) = 0 → a = 0`
- Prove: `∀ n (a : Fin n → J), Σ jsq(aᵢ) = 0 → ∀ i, aᵢ = 0`

**Why it's hard:**
- Requires proving squares form a *salient cone* (if x and -x are sums of squares, then x = 0)
- This is circular with `positiveCone_salient` which uses `sum_sq_eq_zero`
- Classical proof uses Koecher-Vinberg theorem or spectral theory

**Resolution options documented:**
1. Add explicit ordering axioms to JordanAlgebra
2. Develop spectral theory (P3 task created: `af-tpm2`)
3. For concrete algebras, prove both properties directly

---

## Current State

### Jordan Algebra Project
- 8 files, ~740 LOC total
- **1 sorry remaining:**
  - `FormallyReal/Def.lean` - `of_sq_eq_zero` (requires spectral theory)
- Matrix Jordan product now fully proven

### Archimedean Closure Project: COMPLETE
- 44 files, 4,943 LOC, 0 sorries

---

## Next Steps

### Immediate (unblocked tasks)
1. `af-dcxu`: Jordan/Matrix/Instance.lean - JordanAlgebra instance for Hermitian matrices
2. `af-j4dq`: Jordan/FormallyReal/Spectrum.lean - Spectral properties
3. `af-dc2h`: Jordan/Matrix/RealHermitian.lean - Real symmetric matrices
4. `af-noad`: Jordan/FormallyReal/Square.lean - Square roots

### Deferred
- `af-0xrg`: of_sq_eq_zero - needs architectural decision (spectral theory vs axioms)
- `af-tpm2`: Spectral theory development (P3)

---

## Files Modified This Session

- `AfTests/Jordan/Matrix/JordanProduct.lean` (restructured, sorry eliminated)
- `AfTests/Jordan/FormallyReal/Def.lean` (added documentation)
- `HANDOFF.md` (updated)

---

## Sorries

1. `AfTests/Jordan/FormallyReal/Def.lean:58-68` - `of_sq_eq_zero`
   - Proving: single-element property implies sum-of-squares property
   - Status: **Requires spectral theory or ordering axioms**
   - See: Faraut-Korányi "Analysis on Symmetric Cones"

---

## Technical Notes

### IsHermitian.jordanMul Proof Pattern
The proof works entry-wise:
```lean
have eq1 : ∀ x, star (A j x * B x i) = B i x * A x j := fun x => by
  rw [star_mul', hA.apply, hB.apply, mul_comm]
have eq2 : ∀ x, star (B j x * A x i) = A i x * B x j := fun x => by
  rw [star_mul', hB.apply, hA.apply, mul_comm]
simp only [eq1, eq2, add_comm]
```

### of_sq_eq_zero Circularity
```
of_sq_eq_zero needs → cone salience
cone salience needs → sum_sq_eq_zero
sum_sq_eq_zero is → what of_sq_eq_zero proves
```
Breaking this requires either external ordering or spectral decomposition.

---

## Beads Summary

- 1 task closed this session (af-yxux)
- 1 new task created (af-tpm2 - spectral theory, P3)
- af-0xrg remains in progress (blocked on architectural decision)

---

## Previous Sessions

### Session 36 (2026-01-30)
- Jordan FormallyReal properties, cone, matrix product (3 files, 269 LOC)

### Session 35 (2026-01-30)
- Jordan algebra core infrastructure (5 files, 460 LOC)

### Session 34 (2026-01-30)
- Jordan implementation plan complete (45 tasks)
