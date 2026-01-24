# GNS Construction Documentation

## Overview

The **Gelfand-Naimark-Segal (GNS) construction** builds a Hilbert space
representation from a state on a C*-algebra. Given `A` and state `φ : A → ℂ`:

1. **Hilbert space** `H_φ`
2. **\*-representation** `π_φ : A → B(H_φ)`
3. **Cyclic vector** `Ω_φ ∈ H_φ`

Such that `φ(a) = ⟨Ω_φ, π_φ(a) Ω_φ⟩` for all `a ∈ A`.

## File Structure

```
AfTests/GNS/
├── State/
│   ├── Basic.lean          # State definition
│   ├── Positivity.lean     # map_star, self-adjoint → real
│   └── CauchySchwarz.lean  # |φ(b*a)|² ≤ φ(a*a)·φ(b*b)
├── NullSpace/
│   ├── Basic.lean          # N_φ = {a : φ(a*a) = 0}
│   ├── LeftIdeal.lean      # ba ∈ N_φ when a ∈ N_φ
│   └── Quotient.lean       # A / N_φ
├── PreHilbert/
│   ├── InnerProduct.lean   # ⟨[a], [b]⟩ = φ(b*a)
│   ├── Positive.lean       # Positive definiteness
│   └── Seminorm.lean       # ‖[a]‖ = √φ(a*a)
├── HilbertSpace/
│   ├── Completion.lean     # H_φ = completion
│   └── CyclicVector.lean   # Ω_φ = [1]
├── Representation/
│   ├── PreRep.lean         # π(a)[b] = [ab]
│   ├── Bounded.lean        # ‖π(a)‖ ≤ ‖a‖
│   ├── Extension.lean      # Extend to completion
│   └── Star.lean           # π(a*) = π(a)*
└── Main/
    ├── VectorState.lean    # φ(a) = ⟨Ω, π(a)Ω⟩
    ├── Uniqueness.lean     # Unitary equivalence
    └── Theorem.lean        # Main GNS theorem
```

## Phases

| Phase | Files | Status | Details |
|-------|-------|--------|---------|
| 1. States | State/*.lean | In Progress | See [phases/01_states.md](phases/01_states.md) |
| 2. Null Space | NullSpace/*.lean | Not Started | See [phases/02_nullspace.md](phases/02_nullspace.md) |
| 3. Pre-Hilbert | PreHilbert/*.lean | Not Started | See [phases/03_prehilbert.md](phases/03_prehilbert.md) |
| 4. Hilbert Space | HilbertSpace/*.lean | Not Started | See [phases/04_hilbert.md](phases/04_hilbert.md) |
| 5. Representation | Representation/*.lean | Not Started | See [phases/05_representation.md](phases/05_representation.md) |
| 6. Main Theorems | Main/*.lean | Not Started | See [phases/06_main.md](phases/06_main.md) |

## Mathlib Infrastructure

### Available (use directly)
- `CStarAlgebra A` - Base typeclass
- `InnerProductSpace 𝕜 E` - Pre-Hilbert spaces
- `UniformSpace.Completion` - Hilbert completion
- `ContinuousLinearMap` - Bounded operators
- `IsSelfAdjoint` - Self-adjoint elements

### Must Build
- `State A` - Positive normalized functional
- `gnsNullSpace φ` - Left ideal {a : φ(a*a) = 0}
- `gnsInner φ` - Inner product ⟨[a], [b]⟩ = φ(b*a)
- `gnsRep φ` - Representation π_φ(a)[b] = [ab]

## Key Learnings

See [LEARNINGS.md](LEARNINGS.md) for technical discoveries made during implementation.

## Current Status

Track progress in [HANDOFF.md](../../HANDOFF.md) and beads issues:
```bash
bd list --status=open | grep -i gns
```
