/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Trace
import Mathlib.Analysis.InnerProductSpace.Defs

/-!
# Inner Product Space Structure from Trace

This file constructs an `InnerProductSpace ℝ J` instance from a formally real Jordan trace.
This is the key infrastructure needed for the spectral theorem.

## Main results

* `traceInnerCore` - The `InnerProductSpace.Core` structure from `traceInner`
* `traceInnerProductSpace` - The `InnerProductSpace ℝ J` instance

## Implementation notes

For ℝ (a real field), `RCLike.re = id` and `RCLike.conj = id`, so the requirements
for `InnerProductSpace.Core` simplify:
- `conj_inner_symm` becomes symmetry: `inner y x = inner x y`
- `re_inner_nonneg` becomes: `0 ≤ inner x x`
- `smul_left` becomes: `inner (r • x) y = r * inner x y`
-/

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J] [FormallyRealTrace J]

/-- The inner product from trace, as a function to ℝ.
    This is needed for `InnerProductSpace.Core` which expects `Inner 𝕜 F`. -/
noncomputable def traceInnerReal : J → J → ℝ := fun a b => traceInner a b

/-- The `InnerProductSpace.Core` structure on a formally real Jordan algebra with trace.
    Uses `traceInner` as the inner product. -/
noncomputable def traceInnerCore : InnerProductSpace.Core ℝ J where
  inner := traceInnerReal
  conj_inner_symm := fun x y => by
    simp only [RCLike.conj_to_real, traceInnerReal]
    exact traceInner_symm y x
  re_inner_nonneg := fun x => by
    simp only [RCLike.re_to_real, traceInnerReal]
    exact traceInner_self_nonneg x
  add_left := fun x y z => by
    simp only [traceInnerReal]
    exact traceInner_add_left x y z
  smul_left := fun x y r => by
    simp only [RCLike.conj_to_real, traceInnerReal]
    exact traceInner_smul_left r x y
  definite := fun x hx => by
    simp only [traceInnerReal] at hx
    exact traceInner_self_eq_zero_iff.mp hx

/-! ### Normed and Inner Product Space Instances -/

section Instances

/-- The norm on J induced by the trace inner product: ‖x‖ = √(traceInner x x). -/
noncomputable def traceNormedAddCommGroup : NormedAddCommGroup J :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ J _ _ _ traceInnerCore

attribute [local instance] traceNormedAddCommGroup
attribute [local instance] traceInnerCore

/-- The inner product space structure on a formally real Jordan algebra with trace.
    The inner product is `traceInner`, the norm is `√(traceInner x x)`. -/
noncomputable def traceInnerProductSpace : InnerProductSpace ℝ J :=
  InnerProductSpace.ofCore inferInstance

end Instances

end JordanAlgebra
