# Phase 3: Pre-Hilbert Space Structure

## Overview

Define inner product `⟨[a], [b]⟩ = φ(b*a)` on the quotient A/N_φ.

## Files

| File | LOC Target | Status | Key Content |
|------|------------|--------|-------------|
| `PreHilbert/InnerProduct.lean` | 70-90 | Not Started | ⟨[a], [b]⟩ = φ(b*a) |
| `PreHilbert/Positive.lean` | 60-80 | Not Started | ⟨x, x⟩ = 0 ↔ x = 0 |
| `PreHilbert/Seminorm.lean` | 60-80 | Not Started | InnerProductSpace instance |

## Definitions

```lean
def gnsInner (φ : State A) : gnsQuotient φ → gnsQuotient φ → ℂ :=
  Quotient.lift₂ (fun a b => φ (star b * a)) (well_defined_proof)

noncomputable def gnsNorm (x : gnsQuotient φ) : ℝ :=
  Real.sqrt (gnsInner φ x x).re
```

## Key Lemmas

### InnerProduct.lean
- `gnsInner_mk` - ⟨[a], [b]⟩ = φ(b*a)
- `gnsInner_conj_symm` - ⟨x, y⟩ = conj(⟨y, x⟩)
- `gnsInner_add_left`, `gnsInner_smul_left` - Linearity

### Positive.lean
- `gnsInner_self_nonneg` - ⟨x, x⟩.re ≥ 0
- `gnsInner_self_eq_zero_iff` - ⟨x, x⟩ = 0 ↔ x = 0

### Seminorm.lean
- `gnsQuotient.innerProductSpace` - The InnerProductSpace instance

## Well-Definedness Proof

Need: if a₁ - a₂ ∈ N_φ and b₁ - b₂ ∈ N_φ, then φ(b₁*a₁) = φ(b₂*a₂).

```
φ(b₁*a₁) - φ(b₂*a₂) = φ(b₁*(a₁-a₂)) + φ((b₁-b₂)*a₂)
First term: |φ(b₁*(a₁-a₂))|² ≤ φ((a₁-a₂)*(a₁-a₂))·φ(b₁*b₁) = 0
Second term: Similarly 0
```

## Dependencies

```
NullSpace/Quotient.lean
         │
    ┌────┴────┐
    ▼         ▼
InnerProduct  Seminorm
    │         │
    └────┬────┘
         ▼
     Positive
```
