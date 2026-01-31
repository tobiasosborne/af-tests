# Handoff: 2026-01-31 (Session 72)

## Completed This Session

- **PROVEN: `spectral_sq`** - Key structural theorem now has no sorry!
- **PROVEN: `jsq_sum_orthog_idem`** - Squaring sums of orthogonal idempotents
- **PROVEN: `sum_jmul`** - Left multiplication distributes over sums

### Key Technical Achievement

**`spectral_sq` is now proven without sorry:**
```lean
theorem spectral_sq (a : J) (sd : SpectralDecomp a) :
    ∃ sd_sq : SpectralDecomp (jsq a), sd_sq.n = sd.n
```

This theorem shows: if `a = Σ λᵢ eᵢ` (orthogonal idempotents), then `a² = Σ λᵢ² eᵢ`.

The proof uses the helper lemma `jsq_sum_orthog_idem` which expands:
```
(∑ᵢ coef i • eᵢ)² = ∑ᵢ (coef i)² • eᵢ
```
This follows from orthogonality (cross-terms vanish) and idempotency (diagonal terms simplify).

---

## Current State

| Metric | Value |
|--------|-------|
| Total Sorries in Jordan/ | ~26 |
| Build Status | PASSING |
| SpectralTheorem.lean | 6 sorries (was 7) |

### SpectralTheorem.lean Status (6 sorries)

| Line | Theorem | Status | Notes |
|------|---------|--------|-------|
| 59 | `spectral_decomposition_exists` | sorry | Depends on primitivity |
| 71 | `spectral_decomposition_finset` | sorry | Depends on line 59 |
| 80 | `spectrum_eq_eigenvalueSet` | sorry | Needs spectral decomp |
| 140 | `spectral_sq` | **PROVEN** | No longer has sorry! |
| 159, 162 | `spectrum_sq` (2 cases) | sorry | Relates operator eigenvalues to decomp |
| 173 | `sq_eigenvalues_nonneg` | sorry | Needs spectrum_sq |

### Primitive.lean Status (5 sorries) - UNCHANGED

Still blocking the main spectral theorems.

---

## Key Discovery: Two Notions of "Eigenvalue"

The file has two related but distinct concepts:

1. **Operator eigenvalues** (`spectrum a`): Eigenvalues of `L_a : v ↦ a ∘ v`
2. **Decomposition coefficients** (`SpectralDecomp.eigenvalues`): The λᵢ in `a = Σ λᵢ eᵢ`

These are related when the eᵢ are primitive idempotents, but proving this relationship
requires more Peirce theory. The theorem `spectrum_sq` (with 2 sorries) aims to prove
they're equal, but this needs `spectral_decomposition_exists` which depends on primitivity.

**Key insight:** `spectral_sq` (now proven) works with decomposition coefficients,
not operator eigenvalues. It's structural and doesn't need primitivity.

---

## Next Steps (Priority Order)

### 1. Prove `primitive_peirce_one_scalar` (P1) - af-lhxr
**Still the key blocker.** Shows P₁(e) = ℝe for primitive e.

**CANONICAL H-O PROOF (Lemma 2.9.4(ii)):**

Uses **Lemma 2.9.3**: Commutative ring without nilpotents + DCC → direct sum of fields.

1. {pAp} is commutative associative (Peirce theory - DONE)
2. Has no nilpotents (formal reality)
3. Finite-dimensional → DCC
4. **Apply 2.9.3** → {pAp} = F₁ ⊕ ... ⊕ Fₙ (direct sum of fields)
5. p = e₁ + ... + eₙ (sum of field identities)
6. **Minimality** → n = 1 (else eᵢ is sub-idempotent)
7. {pAp} is a single field F
8. **Formally real** → F ≠ ℂ
9. Only formally real field over ℝ is ℝ (H-O 2.2.6)
10. Hence {pAp} = ℝp

**Mathlib search needed:** Structure theorem for semisimple commutative algebras.

### 2. Complete Primitive.lean sorries → unlocks spectral theory

### 3. Then prove `spectral_decomposition_exists`

---

## Files Modified This Session

- `AfTests/Jordan/SpectralTheorem.lean` — Added `sum_jmul`, `jsq_sum_orthog_idem`; proved `spectral_sq`
- `HANDOFF.md` — This file

---

## Issue Status

| Issue | Status | Notes |
|-------|--------|-------|
| af-4g40 | IN PROGRESS | spectral_sq now proven! |
| af-lhxr | OPEN (P1) | primitive_peirce_one_scalar - key blocker |
| af-hbnj | OPEN (P1) | exists_primitive_decomp |
| af-5zpv | OPEN (P0) | JordanTrace needs instances |
