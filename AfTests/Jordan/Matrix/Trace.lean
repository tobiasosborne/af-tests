/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Matrix.Instance
import AfTests.Jordan.Trace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.RCLike.Basic

/-!
# Trace Inner Product on Hermitian Matrices

The trace inner product on Hermitian matrices is `⟨A, B⟩ = Tr(AB)`. This makes
Hermitian matrices into a real inner product space.

## Main definitions

* `HermitianMatrix.traceInner` - The trace inner product `Tr(AB)`

## Main results

* `HermitianMatrix.traceInner_comm` - Symmetry: `⟨A, B⟩ = ⟨B, A⟩`
* `HermitianMatrix.traceInner_self_nonneg` - Positivity: `0 ≤ ⟨A, A⟩`
* `HermitianMatrix.traceInner_self_eq_zero` - Definiteness: `⟨A, A⟩ = 0 ↔ A = 0`
-/

open Matrix Finset BigOperators

open scoped ComplexOrder MatrixOrder

namespace HermitianMatrix

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Trace Inner Product Definition -/

/-- The trace inner product on Hermitian matrices: `⟨A, B⟩ = Tr(AB)`. -/
def traceInner (A B : HermitianMatrix n 𝕜) : 𝕜 :=
  (A.val * B.val).trace

omit [DecidableEq n] in
theorem traceInner_def (A B : HermitianMatrix n 𝕜) :
    traceInner A B = (A.val * B.val).trace := rfl

/-! ### Basic Properties -/

omit [DecidableEq n] in
/-- Trace inner product is commutative. -/
theorem traceInner_comm (A B : HermitianMatrix n 𝕜) :
    traceInner A B = traceInner B A := by
  simp only [traceInner_def]
  exact trace_mul_comm A.val B.val

omit [DecidableEq n] in
/-- Trace inner product is additive in the first argument. -/
theorem traceInner_add_left (A B C : HermitianMatrix n 𝕜) :
    traceInner (A + B) C = traceInner A C + traceInner B C := by
  simp only [traceInner_def, AddSubgroup.coe_add, add_mul, trace_add]

omit [DecidableEq n] in
/-- Trace inner product is additive in the second argument. -/
theorem traceInner_add_right (A B C : HermitianMatrix n 𝕜) :
    traceInner A (B + C) = traceInner A B + traceInner A C := by
  simp only [traceInner_def, AddSubgroup.coe_add, mul_add, trace_add]

omit [DecidableEq n] in
/-- Trace inner product with zero. -/
theorem traceInner_zero_left (A : HermitianMatrix n 𝕜) :
    traceInner 0 A = 0 := by
  simp only [traceInner_def, AddSubgroup.coe_zero, zero_mul, trace_zero]

omit [DecidableEq n] in
theorem traceInner_zero_right (A : HermitianMatrix n 𝕜) :
    traceInner A 0 = 0 := by
  simp only [traceInner_def, AddSubgroup.coe_zero, mul_zero, trace_zero]

/-! ### Self Inner Product -/

omit [DecidableEq n] in
/-- `⟨A, A⟩ = Tr(A²)` for Hermitian A. -/
theorem traceInner_self (A : HermitianMatrix n 𝕜) :
    traceInner A A = (A.val * A.val).trace := rfl

omit [DecidableEq n] in
/-- For Hermitian A, `A² = Aᴴ * A`. -/
theorem sq_eq_conjTranspose_mul' (A : HermitianMatrix n 𝕜) :
    A.val * A.val = A.valᴴ * A.val := by
  rw [A.prop.isHermitian.eq]

omit [DecidableEq n] in
/-- `⟨A, A⟩` is real (equals its conjugate). -/
theorem traceInner_self_conj (A : HermitianMatrix n 𝕜) :
    star (traceInner A A) = traceInner A A := by
  simp only [traceInner_self, sq_eq_conjTranspose_mul']
  rw [← trace_conjTranspose]
  congr 1
  rw [conjTranspose_mul, conjTranspose_conjTranspose, A.prop.isHermitian.eq]

omit [DecidableEq n] in
/-- `⟨A, A⟩` is nonnegative. -/
theorem traceInner_self_nonneg (A : HermitianMatrix n 𝕜) :
    0 ≤ traceInner A A := by
  simp only [traceInner_self, sq_eq_conjTranspose_mul']
  exact (posSemidef_conjTranspose_mul_self A.val).trace_nonneg

omit [DecidableEq n] in
/-- `⟨A, A⟩ = 0` if and only if `A = 0`. -/
theorem traceInner_self_eq_zero (A : HermitianMatrix n 𝕜) :
    traceInner A A = 0 ↔ A = 0 := by
  simp only [traceInner_self, sq_eq_conjTranspose_mul']
  rw [trace_conjTranspose_mul_self_eq_zero_iff]
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    simp [h]

/-! ### Trace of Jordan Product -/

/-- The trace inner product equals `Tr(A ∘ B)` where ∘ is Jordan product.
    Since `Tr(AB) = Tr(BA)`, we have `Tr((AB + BA)/2) = Tr(AB)`. -/
theorem traceInner_eq_trace_jmul (A B : HermitianMatrix n 𝕜) :
    traceInner A B = (jmul A B).val.trace := by
  simp only [traceInner_def, jmul_val, jordanMul_def]
  rw [trace_smul, trace_add, trace_mul_comm B.val A.val]
  rw [← two_smul 𝕜 (A.val * B.val).trace]
  rw [smul_smul]
  simp

omit [DecidableEq n] in
/-- The trace inner product is real-valued for all Hermitian pairs. -/
theorem traceInner_conj (A B : HermitianMatrix n 𝕜) :
    star (traceInner A B) = traceInner A B := by
  simp only [traceInner_def]
  rw [← trace_conjTranspose, conjTranspose_mul, A.prop.isHermitian.eq, B.prop.isHermitian.eq]
  exact trace_mul_comm B.val A.val

/-! ### Real Inner Product -/

/-- The real-valued trace inner product. -/
def traceInnerReal (A B : HermitianMatrix n 𝕜) : ℝ :=
  RCLike.re (traceInner A B)

omit [DecidableEq n] in
theorem traceInnerReal_def (A B : HermitianMatrix n 𝕜) :
    traceInnerReal A B = RCLike.re (traceInner A B) := rfl

omit [DecidableEq n] in
/-- Real trace inner product is commutative. -/
theorem traceInnerReal_comm (A B : HermitianMatrix n 𝕜) :
    traceInnerReal A B = traceInnerReal B A := by
  simp only [traceInnerReal_def, traceInner_comm]

omit [DecidableEq n] in
/-- Real trace inner product is additive. -/
theorem traceInnerReal_add_left (A B C : HermitianMatrix n 𝕜) :
    traceInnerReal (A + B) C = traceInnerReal A C + traceInnerReal B C := by
  simp only [traceInnerReal_def, traceInner_add_left, map_add]

omit [DecidableEq n] in
/-- Real trace inner product self is nonnegative. -/
theorem traceInnerReal_self_nonneg (A : HermitianMatrix n 𝕜) :
    0 ≤ traceInnerReal A A := by
  simp only [traceInnerReal_def]
  have h := traceInner_self_nonneg A
  exact (RCLike.nonneg_iff.mp h).1

omit [DecidableEq n] in
/-- Real trace inner product self equals zero iff A = 0. -/
theorem traceInnerReal_self_eq_zero (A : HermitianMatrix n 𝕜) :
    traceInnerReal A A = 0 ↔ A = 0 := by
  simp only [traceInnerReal_def]
  constructor
  · intro h
    -- traceInner A A is real (star = self), so im = 0
    have h_im : RCLike.im (traceInner A A) = 0 := RCLike.conj_eq_iff_im.mp (traceInner_self_conj A)
    -- With re = 0 and im = 0, we have traceInner A A = 0
    have h_zero : traceInner A A = 0 := by
      rw [← RCLike.re_add_im (traceInner A A), h, h_im]
      simp
    exact (traceInner_self_eq_zero A).mp h_zero
  · intro h
    simp [h, traceInner_zero_left]

/-! ### JordanTrace Instance -/

/-- The trace functional for Hermitian matrices as a real number.
For Hermitian matrices, Tr(A) is always real since A = A*. -/
def traceReal (A : HermitianMatrix n 𝕜) : ℝ := RCLike.re A.val.trace

omit [DecidableEq n] in
theorem traceReal_def (A : HermitianMatrix n 𝕜) :
    traceReal A = RCLike.re A.val.trace := rfl

omit [DecidableEq n] in
/-- The trace of a Hermitian matrix is real (imaginary part is zero). -/
theorem trace_im_zero (A : HermitianMatrix n 𝕜) :
    RCLike.im A.val.trace = 0 := by
  have h : A.val.trace = star A.val.trace := by
    rw [← trace_conjTranspose, A.prop.isHermitian.eq]
  rw [← RCLike.conj_eq_iff_im]
  exact h.symm

omit [DecidableEq n] in
/-- For Hermitian matrices, trace equals its real part as an element of 𝕜. -/
theorem trace_eq_re (A : HermitianMatrix n 𝕜) :
    A.val.trace = (traceReal A : 𝕜) := by
  rw [traceReal_def, ← RCLike.re_add_im A.val.trace, trace_im_zero A]
  simp

omit [DecidableEq n] in
theorem traceReal_add (A B : HermitianMatrix n 𝕜) :
    traceReal (A + B) = traceReal A + traceReal B := by
  simp only [traceReal_def, AddSubgroup.coe_add, trace_add, map_add]

omit [DecidableEq n] in
theorem traceReal_smul (r : ℝ) (A : HermitianMatrix n 𝕜) :
    traceReal (r • A) = r * traceReal A := by
  simp only [traceReal_def]
  show RCLike.re ((r • A).val).trace = r * RCLike.re A.val.trace
  have h : (r • A).val = r • A.val := rfl
  rw [h]
  unfold trace
  simp only [diag_smul, Pi.smul_apply, map_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  exact RCLike.smul_re r (A.val x x)

theorem traceReal_jmul_comm (A B : HermitianMatrix n 𝕜) :
    traceReal (jmul A B) = traceReal (jmul B A) := by
  rw [jmul_comm]

/-- The key self-adjointness property: Tr((A∘V)∘W) = Tr(V∘(A∘W)).
This follows from the cyclicity of the trace: Tr(XYZ) = Tr(YZX) = Tr(ZXY).

Both sides expand to sums of traces of products AVW, VAW, VWA, AWV, WAV, WVA.
By trace cyclicity, cyclic permutations have equal traces, so both sides are equal.

PROOF SKETCH:
- jmul (jmul A V) W = ((A∘V)∘W) = (((AV+VA)/2)*W + W*((AV+VA)/2))/2
- After expansion: (AVW + VAW + WAV + WVA)/4
- Similarly jmul V (jmul A W) = (V*(AW+WA)/2 + (AW+WA)/2*V)/2
- After expansion: (VAW + VWA + AWV + WAV)/4
- By trace cyclicity: Tr(AVW)=Tr(VWA)=Tr(WAV), Tr(VAW)=Tr(AWV)=Tr(WVA)
- Both sums equal 2*Tr(AVW) + 2*Tr(VAW) after applying cyclicity.
-/
theorem traceReal_L_selfadjoint (A V W : HermitianMatrix n 𝕜) :
    traceReal (jmul (jmul A V) W) = traceReal (jmul V (jmul A W)) := by
  simp only [traceReal_def, jmul_val, jordanMul_def]
  simp only [smul_add, mul_add, add_mul, trace_add, trace_smul]
  simp only [mul_smul_comm, smul_mul_assoc]
  simp only [trace_smul, Matrix.mul_assoc]
  congr 1
  -- Use trace cyclicity: trace_mul_cycle' A B C : (A*(B*C)).trace = (C*(A*B)).trace
  have h1 : (A.val * (V.val * W.val)).trace = (V.val * (W.val * A.val)).trace := by
    have step1 := trace_mul_cycle' A.val V.val W.val
    have step2 := trace_mul_cycle' W.val A.val V.val
    rw [step1, step2]
  have h2 : (W.val * (V.val * A.val)).trace = (A.val * (W.val * V.val)).trace :=
    trace_mul_cycle' W.val V.val A.val
  rw [h1, h2]
  ring

theorem traceReal_jone_pos [Nonempty n] :
    0 < traceReal (HermitianMatrix.one : HermitianMatrix n 𝕜) := by
  simp only [traceReal_def, HermitianMatrix.one_val, trace_one]
  have h : (Fintype.card n : 𝕜) = ((Fintype.card n : ℕ) : 𝕜) := rfl
  rw [h]
  simp only [RCLike.natCast_re]
  exact Nat.cast_pos.mpr (Fintype.card_pos)

/-! ### FormallyRealTrace Properties -/

/-- For Hermitian A, traceReal (jsq A) = traceInnerReal A A.
    This follows because jsq A = jmul A A has underlying value A.val * A.val. -/
theorem traceReal_jsq_eq_traceInnerReal (A : HermitianMatrix n 𝕜) :
    traceReal (jsq A) = traceInnerReal A A := by
  simp only [traceReal_def, traceInnerReal_def, traceInner_def]
  -- jsq A = jmul A A, and (jmul A A).val = jordanMul A.val A.val = A.val * A.val
  congr 1
  simp only [JordanAlgebra.jsq_def, jmul_val, jordanMul_self]

/-- Trace of a square is non-negative for Hermitian matrices. -/
theorem traceReal_jsq_nonneg (A : HermitianMatrix n 𝕜) :
    0 ≤ traceReal (jsq A) := by
  rw [traceReal_jsq_eq_traceInnerReal]
  exact traceInnerReal_self_nonneg A

/-- Trace of a square is zero iff the element is zero. -/
theorem traceReal_jsq_eq_zero_iff (A : HermitianMatrix n 𝕜) :
    traceReal (jsq A) = 0 ↔ A = 0 := by
  rw [traceReal_jsq_eq_traceInnerReal]
  exact traceInnerReal_self_eq_zero A

end HermitianMatrix

/-! ### JordanTrace Instance for Hermitian Matrices -/

/-- Hermitian matrices with the Jordan product have a trace satisfying the JordanTrace axioms. -/
instance jordanTraceHermitianMatrix {n : Type*} [DecidableEq n] [Fintype n] [Nonempty n]
    {𝕜 : Type*} [RCLike 𝕜] : JordanAlgebra.JordanTrace (HermitianMatrix n 𝕜) where
  trace := HermitianMatrix.traceReal
  trace_add := HermitianMatrix.traceReal_add
  trace_smul := HermitianMatrix.traceReal_smul
  trace_jmul_comm := HermitianMatrix.traceReal_jmul_comm
  trace_L_selfadjoint := HermitianMatrix.traceReal_L_selfadjoint
  trace_jone_pos := HermitianMatrix.traceReal_jone_pos

/-! ### FormallyRealTrace Instance for Hermitian Matrices -/

/-- Hermitian matrices satisfy FormallyRealTrace: trace of squares is non-negative and definite. -/
instance formallyRealTraceHermitianMatrix {n : Type*} [DecidableEq n] [Fintype n] [Nonempty n]
    {𝕜 : Type*} [RCLike 𝕜] : JordanAlgebra.FormallyRealTrace (HermitianMatrix n 𝕜) where
  trace_jsq_nonneg := HermitianMatrix.traceReal_jsq_nonneg
  trace_jsq_eq_zero_iff := HermitianMatrix.traceReal_jsq_eq_zero_iff
