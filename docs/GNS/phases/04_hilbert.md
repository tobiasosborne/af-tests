# Phase 4: GNS Hilbert Space

## Overview

Complete the pre-Hilbert space to get the GNS Hilbert space H_φ.

## Files

| File | LOC Target | Status | Key Content |
|------|------------|--------|-------------|
| `HilbertSpace/Completion.lean` | 50-70 | Not Started | H_φ = completion |
| `HilbertSpace/CyclicVector.lean` | 50-70 | Not Started | Ω_φ = [1] |

## Definitions

```lean
def gnsHilbertSpace (φ : State A) : Type* :=
  UniformSpace.Completion (gnsQuotient φ)

instance (φ : State A) : InnerProductSpace ℂ (gnsHilbertSpace φ) :=
  UniformSpace.Completion.innerProductSpace ℂ (gnsQuotient φ)

instance (φ : State A) : CompleteSpace (gnsHilbertSpace φ) :=
  UniformSpace.Completion.completeSpace (gnsQuotient φ)

def gnsEmbed (φ : State A) : gnsQuotient φ →L[ℂ] gnsHilbertSpace φ := ...

def gnsCyclicVector (φ : State A) : gnsHilbertSpace φ :=
  gnsEmbed φ (gnsQuotientMk φ 1)
```

## Key Lemmas

### Completion.lean
- `gnsEmbed_isometry` - Embedding is isometric
- `gnsEmbed_denseRange` - Quotient is dense in completion
- `gnsHilbertSpace.inner_embed` - ⟨embed x, embed y⟩ = ⟨x, y⟩

### CyclicVector.lean
- `gnsCyclicVector_norm` - ‖Ω_φ‖ = 1
- `gnsCyclicVector_inner_self` - ⟨Ω_φ, Ω_φ⟩ = 1
- `gnsCyclicVector_span_dense` - {π(a)Ω : a ∈ A} is dense

## Mathlib Usage

Heavy use of `UniformSpace.Completion`:
- `UniformSpace.Completion.innerProductSpace`
- `UniformSpace.Completion.toComplₗᵢ`
- `UniformSpace.Completion.denseRange_coe`

## Dependencies

```
PreHilbert/Seminorm.lean
         │
         ▼
  Completion.lean
         │
         ▼
  CyclicVector.lean
```
