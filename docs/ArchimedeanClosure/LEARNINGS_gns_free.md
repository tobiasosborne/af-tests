# GNS Construction for FreeStarAlgebra

## Key Insight: Archimedean Property Guarantees Boundedness

**Discovery (Schmudgen 2020, Cimpric 2009):** For general *-algebras (not C*-algebras),
the GNS construction may produce unbounded operators. However, when the quadratic
module is Archimedean, **all M-positive representations act by bounded operators**.

This is why our formalization strategy works: we don't face domain issues or
unbounded operator complications because the Archimedean property is assumed.

## Construction Overview (7 files, ~320 LOC)

```
AfTests/ArchimedeanClosure/GNS/
├── NullSpace.lean   (~50 LOC) - N_φ = {a : φ(a*a) = 0}, left ideal
├── Quotient.lean    (~50 LOC) - A/N_φ with ⟨[a],[b]⟩ = φ(a*b)
├── Completion.lean  (~40 LOC) - Hilbert space H_φ, cyclic vector Ω
├── PreRep.lean      (~40 LOC) - Left multiplication: a • [b] = [ab]
├── Bounded.lean     (~50 LOC) - ‖a • x‖ ≤ √N_a · ‖x‖ (uses Archimedean!)
├── Extension.lean   (~50 LOC) - Extend to completion, *-algebra hom
└── Constrained.lean (~40 LOC) - π(gⱼ) ≥ 0 from M-positivity
```

## Difference from C*-algebra GNS (AfTests/GNS/)

| Aspect | C*-Algebra GNS | FreeStarAlgebra GNS |
|--------|----------------|---------------------|
| **Boundedness** | Uses C*-norm: ‖π(a)‖ ≤ ‖a‖ | Uses Archimedean: ‖π(a)‖ ≤ √N_a |
| **State type** | `A →L[ℂ] ℂ` (continuous) | `A →ₗ[ℝ] ℝ` (just linear) |
| **Scalar field** | ℂ throughout | ℝ for algebra, ℂ for Hilbert space |
| **Constrained** | N/A | Must prove π(gⱼ) ≥ 0 |

## Key Proof: Generators Map to Positive Operators

**Theorem:** For GNS representation π_φ of M-positive state φ, each π_φ(gⱼ) is positive.

**Proof:**
1. For [b] in quotient: ⟨[b], π_φ(gⱼ)[b]⟩ = φ(b* · gⱼ · b)
2. But b* · gⱼ · b ∈ M by definition of quadratic module
3. So φ(b* · gⱼ · b) ≥ 0 by M-positivity of φ
4. Extend to completion by density

## References

- **Schmudgen (2020)**: "An Invitation to Unbounded Representations of *-Algebras on Hilbert Space"
  - Chapter 10: Archimedean quadratic modules → bounded representations

- **Cimpric (2009)**: "A representation theorem for Archimedean quadratic modules on *-rings"
  - arxiv:0807.5020
  - Generalizes Jacobi's representation theorem

## Mathlib Tools

```lean
import Mathlib.Analysis.InnerProductSpace.Defs       -- PreInnerProductSpace.Core
import Mathlib.Analysis.InnerProductSpace.Completion -- UniformSpace.Completion.innerProductSpace
import Mathlib.Analysis.InnerProductSpace.Positive   -- ContinuousLinearMap.IsPositive
import Mathlib.Algebra.Star.StarAlgHom              -- StarAlgHom
```
