/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Macdonald.FreeSpecialJordan
import Mathlib.Algebra.Star.Free
import Mathlib.Algebra.Star.Module
import Mathlib.Data.Real.Star
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor Product Setup for Macdonald's Theorem (Steps 14-17)

Sets up the infrastructure for the tensor product embedding used in Steps 14-17
of the Macdonald theorem proof (Hanche-Olsen 2.4).

## Main definitions

* `FA` - The associative free algebra `FreeAlgebra ℝ (Fin 2)` on two generators
* `FA2` - The tensor product `FA ⊗ FA`, which has a natural algebra structure
* `symTensor` - The submodule of symmetric tensors `{t | comm(t) = t}`
* `evalFA` - Evaluation map `FreeJordanAlg → FA` (canonical surjection)
## Main results

* `gamma_mac` - The correct gamma map for Macdonald: `γ(p,q) = ½(pzq* + qzp*)` in FA3
* `gamma_mac_comm` - `gamma_mac` is symmetric in its arguments

## Design notes

We use Mathlib's `FreeAlgebra ℝ (Fin 2)` as the associative free algebra, connected
to the project's `FreeJordanAlg` via `evalAssoc`. The star (anti-involution) from
`Mathlib.Algebra.Star.Free` reverses words; generators are self-adjoint (`star_ι`).
The correct gamma for Macdonald maps into FA3 (3-generator free algebra) via
`gamma_mac(p,q) = ½(pzq* + qzp*)`, which is injective on symmetric tensors.
-/

/-! ### Free algebra FA = FreeAlgebra ℝ (Fin 2) -/

/-- The associative free ℝ-algebra on two generators. -/
abbrev FA := FreeAlgebra ℝ (Fin 2)

/-- Generator x of the associative free algebra. -/
noncomputable def FA.x : FA := FreeAlgebra.ι ℝ (0 : Fin 2)

/-- Generator y of the associative free algebra. -/
noncomputable def FA.y : FA := FreeAlgebra.ι ℝ (1 : Fin 2)

@[simp] theorem FA.star_x : star FA.x = FA.x := FreeAlgebra.star_ι (0 : Fin 2)
@[simp] theorem FA.star_y : star FA.y = FA.y := FreeAlgebra.star_ι (1 : Fin 2)

/-- `StarModule ℝ FA`: star commutes with real scalar multiplication. -/
instance : StarModule ℝ FA where
  star_smul r a := by
    simp only [Algebra.smul_def, star_mul, FreeAlgebra.star_algebraMap, star_trivial]
    rw [Algebra.commutes]

/-! ### Tensor product FA ⊗ FA -/

/-- The tensor product `FA ⊗ FA`, which inherits `Ring` and `Algebra ℝ` structure. -/
abbrev FA2 := TensorProduct ℝ FA FA

/-- Symmetric tensors: the submodule of `FA ⊗ FA` fixed by the swap map.
    An element `t` is symmetric iff `comm(t) = t` where `comm` swaps tensor factors. -/
noncomputable def symTensor : Submodule ℝ FA2 :=
  LinearMap.eqLocus LinearMap.id (TensorProduct.comm ℝ FA FA).toLinearMap

/-! ### Evaluation map: FreeJordanAlg → FA -/

/-- The canonical evaluation map sending `FreeJordanAlg` into `FA`, mapping
    generators to generators and using the Jordan (symmetrized) product `½(ab+ba)`. -/
noncomputable def evalFA : FreeJordanAlg → FA :=
  FreeJordanAlg.evalAssoc FA.x FA.y

@[simp] theorem evalFA_x : evalFA FreeJordanAlg.x = FA.x := by
  unfold evalFA; simp [FA.x]

@[simp] theorem evalFA_y : evalFA FreeJordanAlg.y = FA.y := by
  unfold evalFA; simp [FA.y]

theorem evalFA_add (u v : FreeJordanAlg) :
    evalFA (u + v) = evalFA u + evalFA v :=
  FreeJordanAlg.evalAssoc_add FA.x FA.y u v

theorem evalFA_smul (r : ℝ) (u : FreeJordanAlg) :
    evalFA (r • u) = r • evalFA u :=
  FreeJordanAlg.evalAssoc_smul FA.x FA.y r u

theorem evalFA_mul (u v : FreeJordanAlg) :
    evalFA (FreeJordanAlg.mul u v) =
    (1/2 : ℝ) • (evalFA u * evalFA v + evalFA v * evalFA u) :=
  FreeJordanAlg.evalAssoc_mul FA.x FA.y u v

/-! ### Three-generator free algebra FA3 = FreeAlgebra ℝ (Fin 3) -/

/-- The associative free ℝ-algebra on three generators x, y, z.
    Used in Macdonald's theorem: z is the "generic" third variable. -/
abbrev FA3 := FreeAlgebra ℝ (Fin 3)

/-- Generator z of the three-generator free algebra (the "test element"). -/
noncomputable def FA3.z : FA3 := FreeAlgebra.ι ℝ (2 : Fin 3)

/-- Embed FA = FreeAlgebra ℝ (Fin 2) into FA3 = FreeAlgebra ℝ (Fin 3)
    by the natural inclusion Fin 2 → Fin 3. -/
noncomputable def FA_to_FA3 : FA →ₐ[ℝ] FA3 :=
  FreeAlgebra.lift ℝ (fun i => FreeAlgebra.ι ℝ (Fin.castSucc i))

/-- Star (word-reversal anti-involution) on FA3. -/
instance : StarRing FA3 := FreeAlgebra.instStarRing

/-! ### Correct gamma map for Macdonald's theorem (H-O 2.4.25)

The correct gamma maps symmetric tensors in FA ⊗ FA to FA3 via:
`γ(p ⊗ q) = ½(p·z·q* + q·z·p*)`
where `*` is word reversal and z is the third generator.
This is injective because z acts as a separator in monomials. -/

/-- The gamma map for Macdonald's theorem: sends `p ⊗ q` to `½(pzq* + qzp*)` in FA3.
    This is the bilinear map from FA × FA → FA3 before restricting to symmetric tensors. -/
noncomputable def gamma_mac (p q : FA) : FA3 :=
  (1/2 : ℝ) • (FA_to_FA3 p * FA3.z * star (FA_to_FA3 q)
             + FA_to_FA3 q * FA3.z * star (FA_to_FA3 p))

/-- gamma_mac is symmetric in its arguments. -/
theorem gamma_mac_comm (p q : FA) : gamma_mac p q = gamma_mac q p := by
  unfold gamma_mac; congr 1; exact add_comm _ _
