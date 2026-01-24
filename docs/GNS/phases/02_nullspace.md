# Phase 2: GNS Null Space

## Overview

The **GNS null space** is `N_φ = {a ∈ A : φ(a*a) = 0}`. It's a left ideal,
enabling the quotient construction.

## Files

| File | LOC Target | Status | Key Content |
|------|------------|--------|-------------|
| `NullSpace/Basic.lean` | 50-70 | Not Started | N_φ as AddSubgroup |
| `NullSpace/LeftIdeal.lean` | 50-70 | Not Started | ba ∈ N_φ when a ∈ N_φ |
| `NullSpace/Quotient.lean` | 60-80 | Not Started | A / N_φ as module |

## Definitions

```lean
def gnsNullSpace (φ : State A) : AddSubgroup A where
  carrier := {a : A | φ (star a * a) = 0}
  zero_mem' := by simp [star_zero, zero_mul, map_zero]
  add_mem' := ... -- Uses Cauchy-Schwarz
  neg_mem' := by simp [star_neg, neg_mul_neg]

def gnsNullIdeal (φ : State A) : Submodule ℂ A := ...

abbrev gnsQuotient (φ : State A) := A ⧸ gnsNullIdeal φ
```

## Key Lemmas

### Basic.lean
- `mem_gnsNullSpace_iff` - a ∈ N_φ ↔ φ(a*a) = 0
- `zero_mem`, `neg_mem` - Direct
- `add_mem` - Via Cauchy-Schwarz: φ(b*a)² ≤ φ(a*a)·φ(b*b) = 0

### LeftIdeal.lean
- `mul_mem_left` - ba ∈ N_φ when a ∈ N_φ (key for quotient action)

### Quotient.lean
- `gnsQuotientMk` - Quotient map A →ₗ[ℂ] A/N_φ
- `gnsLeftAction` - Action a • [b] = [ab]

## Proof Strategies

### add_mem (a, b ∈ N_φ implies a+b ∈ N_φ)
```
φ((a+b)*(a+b)) = φ(a*a) + φ(a*b) + φ(b*a) + φ(b*b)
               = 0 + φ(a*b) + φ(b*a) + 0
By Cauchy-Schwarz: |φ(a*b)|² ≤ φ(a*a)·φ(b*b) = 0
So φ(a*b) = φ(b*a) = 0, hence φ((a+b)*(a+b)) = 0
```

### mul_mem_left (ba ∈ N_φ when a ∈ N_φ)
```
φ((ba)*(ba)) = φ(a*b*ba)
By C-S applied cleverly: |φ(a*·b*ba)|² ≤ φ(a*a)·φ(...) = 0
```

## Dependencies

```
State/CauchySchwarz.lean
         │
         ▼
   NullSpace/Basic.lean
         │
         ▼
   NullSpace/LeftIdeal.lean
         │
         ▼
   NullSpace/Quotient.lean
```
