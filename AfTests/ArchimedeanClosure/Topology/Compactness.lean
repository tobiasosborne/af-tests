/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.ArchimedeanClosure.Topology.StateTopology
import AfTests.ArchimedeanClosure.Boundedness.ArchimedeanBound
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

/-! # Compactness of State Space S_M

This file proves that the set of M-positive states is compact in the pointwise
convergence topology.

## Main results

* `MPositiveState.apply_mem_closedBall` - Each state value is bounded
* `MPositiveState.stateSet_subset_product` - S_M ⊆ product of closed balls

## Proof strategy

1. The Archimedean bound shows |φ(a)| ≤ √Nₐ for all φ ∈ S_M
2. S_M embeds into ∏ₐ closedBall 0 √Nₐ ⊆ (FreeStarAlgebra n → ℝ)
3. This product is compact by Tychonoff
4. S_M is closed (defined by closed conditions)
5. Closed subset of compact is compact
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ}

section Embedding

/-- The embedding of S_M into a product of reals.

Each state φ is mapped to the function a ↦ φ(a). -/
def toProductFun (φ : MPositiveState n) : FreeStarAlgebra n → ℝ := fun a => φ a

/-- The embedding is injective. -/
theorem toProductFun_injective : Function.Injective (toProductFun (n := n)) := by
  intro φ ψ h
  apply DFunLike.coe_injective'
  exact h

end Embedding

section Bounded

variable [IsArchimedean n]

/-- The bound function: maps each element to its Archimedean bound. -/
noncomputable def bound (a : FreeStarAlgebra n) : ℝ := Real.sqrt (archimedeanBound a)

/-- States are bounded: each evaluation lands in a closed ball. -/
theorem apply_mem_closedBall (φ : MPositiveState n) (a : FreeStarAlgebra n) :
    φ a ∈ Metric.closedBall (0 : ℝ) (bound a) := by
  rw [Metric.mem_closedBall, dist_zero_right]
  exact φ.apply_abs_le a

/-- States map into the bounded product set. -/
theorem stateSet_subset_product :
    Set.range (toProductFun (n := n)) ⊆
    { f | ∀ a, f a ∈ Metric.closedBall (0 : ℝ) (bound a) } := by
  intro f ⟨φ, hφ⟩ a
  rw [← hφ]
  exact φ.apply_mem_closedBall a

/-- The product of closed balls is compact (Tychonoff). -/
theorem product_compact :
    IsCompact { f : FreeStarAlgebra n → ℝ | ∀ a, f a ∈ Metric.closedBall (0 : ℝ) (bound a) } := by
  -- Rewrite using Set.pi
  have h_eq : { f : FreeStarAlgebra n → ℝ | ∀ a, f a ∈ Metric.closedBall (0 : ℝ) (bound a) } =
      Set.univ.pi (fun a => Metric.closedBall (0 : ℝ) (bound a)) := by
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  rw [h_eq]
  -- Apply Tychonoff: product of compact sets is compact
  apply isCompact_univ_pi
  intro a
  exact ProperSpace.isCompact_closedBall 0 (bound a)

end Bounded

end MPositiveState

end FreeStarAlgebra
