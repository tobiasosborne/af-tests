/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Matrix.Instance
import AfTests.Jordan.Matrix.FormallyReal
import AfTests.Jordan.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Complex Hermitian Matrices as a Jordan Algebra

Complex Hermitian matrices (satisfying `Aᴴ = A`) form a formally real Jordan algebra.
This file provides a convenient type alias and complex-specific properties.

## Main definitions

* `ComplexHermitianMatrix` - Type alias for `HermitianMatrix n ℂ`

## Main results

* `JordanAlgebra (ComplexHermitianMatrix n)` - Inherited from HermitianMatrix
* `FormallyRealJordan (ComplexHermitianMatrix n)` - Inherited from HermitianMatrix
* `diag_re_eq_diag` - Diagonal entries are real

## Implementation notes

For complex matrices, `conjTranspose` applies entrywise complex conjugation and transpose.
A matrix is Hermitian iff `Aᴴ = A`, which implies:
- Diagonal entries `A i i` are real
- Off-diagonal entries satisfy `A j i = conj(A i j)`
-/

noncomputable section

open Matrix RCLike

/-! ### Complex Hermitian Matrix Type -/

/-- Complex Hermitian matrices, defined as `HermitianMatrix n ℂ`.

These are matrices satisfying `Aᴴ = A` where `Aᴴ` is the conjugate transpose. -/
abbrev ComplexHermitianMatrix (n : Type*) [Fintype n] := HermitianMatrix n ℂ

namespace ComplexHermitianMatrix

variable {n : Type*} [DecidableEq n] [Fintype n]

/-! ### Basic Properties -/

omit [DecidableEq n] in
/-- A complex Hermitian matrix satisfies `Aᴴ = A`. -/
theorem conjTranspose_eq (A : ComplexHermitianMatrix n) : A.val.conjTranspose = A.val :=
  A.prop.isHermitian.eq

/-- Construct a ComplexHermitianMatrix from a Hermitian matrix. -/
def ofHermitian (A : Matrix n n ℂ) (h : A.IsHermitian) : ComplexHermitianMatrix n :=
  ⟨A, h.isSelfAdjoint⟩

omit [DecidableEq n] in
@[simp]
theorem ofHermitian_val (A : Matrix n n ℂ) (h : A.IsHermitian) : (ofHermitian A h).val = A := rfl

omit [DecidableEq n] in
/-- The underlying matrix of a ComplexHermitianMatrix is Hermitian. -/
theorem val_isHermitian (A : ComplexHermitianMatrix n) : A.val.IsHermitian :=
  A.prop.isHermitian

/-! ### Diagonal Entries are Real -/

omit [DecidableEq n] in
/-- Diagonal entries of a complex Hermitian matrix are real. -/
theorem diag_re_eq_self (A : ComplexHermitianMatrix n) (i : n) :
    (Complex.re (A.val i i) : ℂ) = A.val i i :=
  A.prop.isHermitian.coe_re_apply_self i

omit [DecidableEq n] in
/-- The diagonal of a complex Hermitian matrix equals its real part. -/
theorem diag_re_eq_diag (A : ComplexHermitianMatrix n) :
    (fun i => (Complex.re (A.val.diag i) : ℂ)) = A.val.diag :=
  A.prop.isHermitian.coe_re_diag

omit [DecidableEq n] in
/-- Off-diagonal entries satisfy the Hermitian conjugate relation. -/
theorem apply_conj (A : ComplexHermitianMatrix n) (i j : n) :
    starRingEnd ℂ (A.val j i) = A.val i j :=
  A.prop.isHermitian.apply i j

/-! ### Instances -/

/-- Complex Hermitian matrices form a Jordan algebra. -/
instance : JordanAlgebra (ComplexHermitianMatrix n) := inferInstance

/-- Complex Hermitian matrices form a formally real Jordan algebra. -/
instance : FormallyRealJordan (ComplexHermitianMatrix n) := inferInstance

/-! ### Special Matrices -/

/-- The identity matrix is Hermitian. -/
def one : ComplexHermitianMatrix n := HermitianMatrix.one

/-- The zero matrix is Hermitian. -/
def zero : ComplexHermitianMatrix n := ⟨0, by simp⟩

/-- Real diagonal matrices are Hermitian.

For a real-valued diagonal, the resulting matrix is Hermitian since real numbers
are self-conjugate. -/
def realDiagonal (d : n → ℝ) : ComplexHermitianMatrix n :=
  ⟨Matrix.diagonal (fun i => (d i : ℂ)), by
    have h : (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
      congr 1
      funext i
      simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    exact h.isSelfAdjoint⟩

@[simp]
theorem realDiagonal_val (d : n → ℝ) :
    (realDiagonal d).val = Matrix.diagonal (fun i => (d i : ℂ)) := rfl

/-- Complex diagonal matrices with self-conjugate entries are Hermitian. -/
def diagonal (d : n → ℂ) (hd : ∀ i, starRingEnd ℂ (d i) = d i) : ComplexHermitianMatrix n :=
  ⟨Matrix.diagonal d, by
    have h : (Matrix.diagonal d).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
      congr 1
      funext i
      exact hd i
    exact h.isSelfAdjoint⟩

/-! ### Trace Inner Product -/

/-- The trace inner product for complex Hermitian matrices. -/
def traceInner (A B : ComplexHermitianMatrix n) : ℂ :=
  HermitianMatrix.traceInner A B

/-- The real trace inner product for complex Hermitian matrices.

For Hermitian matrices, `Tr(AB)` is always real, so this extracts the real part. -/
def traceInnerReal (A B : ComplexHermitianMatrix n) : ℝ :=
  HermitianMatrix.traceInnerReal A B

omit [DecidableEq n] in
theorem traceInner_comm (A B : ComplexHermitianMatrix n) : traceInner A B = traceInner B A :=
  HermitianMatrix.traceInner_comm A B

omit [DecidableEq n] in
theorem traceInnerReal_comm (A B : ComplexHermitianMatrix n) :
    traceInnerReal A B = traceInnerReal B A :=
  HermitianMatrix.traceInnerReal_comm A B

omit [DecidableEq n] in
theorem traceInnerReal_self_nonneg (A : ComplexHermitianMatrix n) : 0 ≤ traceInnerReal A A :=
  HermitianMatrix.traceInnerReal_self_nonneg A

end ComplexHermitianMatrix

end
