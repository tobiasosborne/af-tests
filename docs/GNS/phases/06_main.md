# Phase 6: Main GNS Theorems

## Overview

The culmination: φ(a) = ⟨Ω_φ, π_φ(a)Ω_φ⟩ and uniqueness.

## Files

| File | LOC Target | Status | Key Content |
|------|------------|--------|-------------|
| `Main/VectorState.lean` | 50-70 | **Proven** | φ(a) = ⟨Ω, π(a)Ω⟩ |
| `Main/Uniqueness.lean` | 70-90 | **Partial** | Quotient intertwiner (Steps 1-3 pending) |
| `Main/UniquenessExtension.lean` | ~160 | **Not Started** | Extension + surjectivity |
| `Main/UniquenessEquiv.lean` | ~75 | **Not Started** | LinearIsometryEquiv |
| `Main/UniquenessIntertwine.lean` | ~95 | **Not Started** | Intertwining property |
| `Main/UniquenessTheorem.lean` | ~35 | **Not Started** | Final gns_uniqueness |
| `Main/Theorem.lean` | 40-60 | **Proven** | Main GNS theorem |

**See:** [06_main_uniqueness_plan.md](06_main_uniqueness_plan.md) for detailed implementation plan.

## Main Theorems

### VectorState.lean

```lean
theorem gns_vector_state (a : A) : φ a = ⟪Ω_ φ, gnsRep φ a (Ω_ φ)⟫ := by
  -- ⟨Ω_φ, π(a)Ω_φ⟩ = ⟨[1], [a·1]⟩ = ⟨[1], [a]⟩ = φ(1*·a) = φ(a)
  simp [gnsCyclicVector, gnsRep_cyclicVector]
  simp [gnsHilbertSpace.inner_embed, gnsInner_mk, star_one, one_mul]
```

### Uniqueness.lean

```lean
theorem gns_uniqueness
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hξ_norm : ‖ξ‖ = 1)
    (hξ_cyclic : DenseRange (fun a => π a ξ))
    (hξ_state : ∀ a, ⟪ξ, π a ξ⟫ = φ a) :
    ∃ U : gnsHilbertSpace φ ≃ₗᵢ[ℂ] H,
      U (Ω_ φ) = ξ ∧ ∀ a, U ∘L gnsRep φ a = π a ∘L U
```

### Theorem.lean

```lean
/-- The cyclic orbit {π_φ(a)Ω_φ : a ∈ A} is dense in the GNS Hilbert space. -/
theorem gnsCyclicVector_denseRange :
    DenseRange (fun a : A => φ.gnsRep a φ.gnsCyclicVector)

/-- The GNS Construction Theorem: Every state arises as a vector state. -/
theorem gns_theorem :
    ‖φ.gnsCyclicVector‖ = 1 ∧
    (∀ a : A, φ a = ⟪φ.gnsCyclicVector, φ.gnsRep a φ.gnsCyclicVector⟫) ∧
    DenseRange (fun a : A => φ.gnsRep a φ.gnsCyclicVector)
```

## Uniqueness Proof Strategy

1. Define U₀ : A/N_φ → H by U₀[a] = π(a)ξ
2. U₀ well-defined: [a] = [b] → π(a)ξ = π(b)ξ
3. U₀ isometric: ‖U₀[a]‖ = ‖π(a)ξ‖ = √⟨ξ, π(a*a)ξ⟩ = √φ(a*a) = ‖[a]‖
4. Extend to isometry U : H_φ → H
5. Surjective by cyclicity of ξ
6. Intertwining: U(π_φ(a)·) = π(a)(U·)

## Dependencies

```
Representation/Star.lean
HilbertSpace/CyclicVector.lean
            │
      ┌─────┴─────┐
      ▼           ▼
VectorState.lean  Uniqueness.lean
      │           │
      └─────┬─────┘
            ▼
      Theorem.lean
```
