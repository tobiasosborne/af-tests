/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.ArchimedeanClosure.Seminorm.SeminormProps
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-! # Seminorm Topology on FreeStarAlgebra

This file defines the topology on FreeStarAlgebra induced by the state seminorm,
and shows it is locally convex.

## Main definitions

* `stateSeminormFamily` - The state seminorm as a SeminormFamily (indexed by Unit)
* `seminormTopology` - TopologicalSpace induced by state seminorm

## Main results

* `withSeminorms_stateSeminormFamily` - The topology satisfies WithSeminorms
* `locallyConvexSpace_seminormTopology` - The topology is locally convex

## Purpose

This infrastructure enables using `ProperCone.hyperplane_separation_point` for
the Riesz extension theorem in AC-P6.4.
-/

namespace FreeStarAlgebra

variable {n : ℕ} [IsArchimedean n]

/-- The state seminorm as a SeminormFamily indexed by Unit. -/
noncomputable def stateSeminormFamily : SeminormFamily ℝ (FreeStarAlgebra n) Unit :=
  fun _ => stateSeminormSeminorm

/-- The topology induced by the state seminorm family. -/
noncomputable def seminormTopology : TopologicalSpace (FreeStarAlgebra n) :=
  stateSeminormFamily.moduleFilterBasis.topology

section WithTopology
/-! ### Results requiring the seminorm topology -/

attribute [local instance] seminormTopology

/-- The topology is exactly the seminorm family topology. -/
theorem withSeminorms_stateSeminormFamily :
    WithSeminorms (stateSeminormFamily (n := n)) :=
  WithSeminorms.mk rfl

/-- The seminorm topology makes FreeStarAlgebra locally convex. -/
theorem locallyConvexSpace_seminormTopology : LocallyConvexSpace ℝ (FreeStarAlgebra n) :=
  WithSeminorms.toLocallyConvexSpace withSeminorms_stateSeminormFamily

end WithTopology

end FreeStarAlgebra
