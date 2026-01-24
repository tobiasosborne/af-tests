# Archimedean Closure via State Duality

Formalization of the characterization of positivity in constrained C*-algebra representations.

---

## Main Theorem

For a self-adjoint element A in a free *-algebra with Archimedean quadratic module M:

> **A ∈ M̄ ⟺ A ≥ 0 in all constrained *-representations**

where:
- M̄ is the closure of M in the state seminorm topology
- Constrained *-representations are those where π(gⱼ) ≥ 0 for all generators

---

## Mathematical Overview

### Key Concepts

1. **Free *-algebra A₀** = ℂ⟨g₁,...,gₙ⟩ with self-adjoint generators
2. **Quadratic module** M = {Σ aᵢ*aᵢ + Σ bⱼₖ*gⱼbⱼₖ}
3. **Archimedean property**: ∀a, ∃N, N·1 - a*a ∈ M
4. **M-positive state**: φ : A₀ → ℂ with φ(1)=1 and φ(m)≥0 for m∈M
5. **State seminorm**: ||a||_M = sup{|φ(a)| : φ ∈ S_M}

### Proof Structure

1. **Boundedness Lemma**: |φ(a)|² ≤ φ(a*a) ≤ Nₐ (Cauchy-Schwarz + Archimedean)
2. **Compactness**: S_M is compact (Tychonoff + closedness)
3. **Seminorm closure**: M̄ is a closed convex cone
4. **Dual characterization**: A ∈ M̄ ⟺ φ(A) ≥ 0 ∀φ ∈ S_M (Riesz extension)
5. **GNS correspondence**: M-positive states ↔ constrained representations

---

## Mathlib Dependencies

### Core (Available)
| Component | Mathlib Location |
|-----------|------------------|
| Riesz Extension | `Analysis.Convex.Cone.Extension` |
| Convex Cones | `Geometry.Convex.Cone.Basic` |
| Cone Closure | `Analysis.Convex.Cone.Closure` |
| Tychonoff | `Topology.Compactness.Compact` |
| Weak-* topology | `Topology.Algebra.Module.WeakDual` |
| Seminorms | `Analysis.Seminorm` |
| Star algebras | `Algebra.Star.Basic` |
| Free algebras | `Algebra.FreeAlgebra` |

### Project Infrastructure (Reuse)
- GNS construction (AfTests/GNS) - 1956 LOC, complete
- Cauchy-Schwarz for states

### Must Build (~965 LOC)
- Free *-algebra with SA generators
- Quadratic module M
- M-positive states
- State seminorm
- Generating cone lemma
- Constrained representations

---

## Implementation Plan

### Phase 1: Algebraic Setup (140 LOC)
- `Algebra/FreeStarAlgebra.lean` - Free *-algebra quotient
- `Algebra/QuadraticModule.lean` - Cone M
- `Algebra/Archimedean.lean` - Archimedean property

### Phase 2: States (120 LOC)
- `State/MPositiveState.lean` - M-positive state structure
- `State/MPositiveStateProps.lean` - Conjugate symmetry, linearity
- `State/NonEmptiness.lean` - S_M ≠ ∅

### Phase 3: Boundedness (110 LOC)
- `Boundedness/CauchySchwarzM.lean` - |φ(b*a)|² ≤ φ(a*a)φ(b*b)
- `Boundedness/ArchimedeanBound.lean` - φ(a*a) ≤ Nₐ
- `Boundedness/GeneratingCone.lean` - M ∩ (A₀)_sa generates (A₀)_sa

### Phase 4: Topology (110 LOC)
- `Topology/StateTopology.lean` - Pointwise convergence
- `Topology/Compactness.lean` - S_M compact (Tychonoff)
- `Topology/Continuity.lean` - States are ||·||_M-continuous

### Phase 5: Seminorm (105 LOC)
- `Seminorm/StateSeminorm.lean` - ||a||_M = sup|φ(a)|
- `Seminorm/SeminormProps.lean` - Seminorm properties
- `Seminorm/Closure.lean` - M̄ = closure(M)

### Phase 6: Dual Characterization (215 LOC)
- `Dual/Forward.lean` - A ∈ M̄ ⟹ φ(A) ≥ 0
- `Dual/SpanIntersection.lean` - M ∩ span{A} = {0}
- `Dual/SeparatingFunctional.lean` - ψ₀ on span{A}
- `Dual/RieszApplication.lean` - Apply Riesz theorem
- `Dual/ComplexExtension.lean` - ψ → φ complex extension
- `Dual/Normalization.lean` - Normalize to get state

### Phase 7: Representations (110 LOC)
- `Representation/Constrained.lean` - Constrained *-reps
- `Representation/VectorState.lean` - Vector states are M-positive
- `Representation/GNSConstrained.lean` - GNS gives constrained rep

### Phase 8: Main Theorem (55 LOC)
- `Main/DualCharacterization.lean` - Theorem 5.1
- `Main/Theorem.lean` - Main theorem

---

## Risk Assessment

### Low Risk
- Tychonoff, Riesz extension (mathlib available)
- Cone closures, seminorms

### Medium Risk
- Free *-algebra with star (quotient construction)
- M-positive state structure
- Seminorm definition via supremum

### High Risk
- Generating cone property proof
- GNS rep is constrained proof
- Seminorm equivalence with C*-seminorm

---

## File Structure

```
AfTests/ArchimedeanClosure/
├── Algebra/           # Core algebraic structures
├── State/             # M-positive states
├── Boundedness/       # Key estimates
├── Topology/          # Compactness
├── Seminorm/          # ||·||_M
├── Dual/              # Separation theorem
├── Representation/    # Constrained reps + GNS
└── Main/              # Final theorems
```

**Total: 26 files, ~965 LOC**

---

## Documentation

- [ARCHITECTURE.md](ARCHITECTURE.md) - High-level design
- [FILE_PLAN.md](FILE_PLAN.md) - Detailed file specifications
- Source: `examples2/archimedean_closure_revised_v2.md`

---

## Status

**Status: Planning Complete**

Next steps:
1. Create directory structure
2. Implement Phase 1 (Algebra)
3. Implement Phase 2 (States)
4. Build incrementally following dependency graph
