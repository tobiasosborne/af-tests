/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Matrix.Instance
import AfTests.Jordan.Matrix.FormallyReal
import AfTests.Jordan.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Real.Star

/-!
# Real Symmetric Matrices as a Jordan Algebra

For real matrices, "Hermitian" and "symmetric" coincide since `star` on ℝ is the identity.
This file establishes this equivalence and provides a convenient type alias.

## Main definitions

* `RealSymmetricMatrix` - Type alias for `HermitianMatrix n ℝ`
* `isHermitian_iff_isSymm` - Over ℝ, `IsHermitian A ↔ IsSymm A`

## Main results

* `JordanAlgebra (RealSymmetricMatrix n)` - Inherited from HermitianMatrix
* `FormallyRealJordan (RealSymmetricMatrix n)` - Inherited from HermitianMatrix

## Implementation notes

Over ℝ, `TrivialStar` holds, meaning `star x = x`. Therefore:
- `conjTranspose A = transpose A` for real matrices
- `IsHermitian A ↔ IsSymm A`
- `selfAdjoint (Matrix n n ℝ)` = symmetric matrices
-/

noncomputable section

open Matrix

namespace Matrix

variable {n : Type*}

/-! ### Hermitian ↔ Symmetric for Real Matrices -/

/-- Over ℝ, a matrix is Hermitian iff it is symmetric. -/
theorem isHermitian_iff_isSymm (A : Matrix n n ℝ) : A.IsHermitian ↔ A.IsSymm := by
  rw [IsHermitian, Matrix.IsSymm]
  rw [conjTranspose_eq_transpose_of_trivial A]

/-- Over ℝ, conjTranspose = transpose. -/
theorem conjTranspose_eq_transpose_real (A : Matrix m n ℝ) : A.conjTranspose = A.transpose :=
  conjTranspose_eq_transpose_of_trivial A

/-- Symmetric real matrices are Hermitian. -/
theorem IsSymm.isHermitian {A : Matrix n n ℝ} (h : A.IsSymm) : A.IsHermitian :=
  (isHermitian_iff_isSymm A).mpr h

/-- Hermitian real matrices are symmetric. -/
theorem IsHermitian.isSymm_of_real {A : Matrix n n ℝ} (h : A.IsHermitian) : A.IsSymm :=
  (isHermitian_iff_isSymm A).mp h

end Matrix

/-! ### Real Symmetric Matrix Type -/

/-- Real symmetric matrices, defined as `HermitianMatrix n ℝ`.

Over ℝ, this coincides with the set of matrices satisfying `Aᵀ = A`. -/
abbrev RealSymmetricMatrix (n : Type*) [Fintype n] := HermitianMatrix n ℝ

namespace RealSymmetricMatrix

variable {n : Type*} [DecidableEq n] [Fintype n]

/-! ### Basic Properties -/

omit [DecidableEq n] in
/-- A real symmetric matrix satisfies `Aᵀ = A`. -/
theorem transpose_eq (A : RealSymmetricMatrix n) : A.val.transpose = A.val := by
  rw [← Matrix.conjTranspose_eq_transpose_real]
  exact A.prop.isHermitian.eq

/-- Construct a RealSymmetricMatrix from a symmetric matrix. -/
def ofSymm (A : Matrix n n ℝ) (h : A.IsSymm) : RealSymmetricMatrix n :=
  ⟨A, h.isHermitian.isSelfAdjoint⟩

omit [DecidableEq n] in
@[simp]
theorem ofSymm_val (A : Matrix n n ℝ) (h : A.IsSymm) : (ofSymm A h).val = A := rfl

omit [DecidableEq n] in
/-- The underlying matrix of a RealSymmetricMatrix is symmetric. -/
theorem isSymm (A : RealSymmetricMatrix n) : A.val.IsSymm :=
  A.prop.isHermitian.isSymm_of_real

/-! ### Instances -/

/-- Real symmetric matrices form a Jordan algebra. -/
instance : JordanAlgebra (RealSymmetricMatrix n) := inferInstance

/-- Real symmetric matrices form a formally real Jordan algebra. -/
instance : FormallyRealJordan (RealSymmetricMatrix n) := inferInstance

/-! ### Special Matrices -/

/-- The identity matrix is symmetric. -/
def one : RealSymmetricMatrix n := HermitianMatrix.one

/-- The zero matrix is symmetric. -/
def zero : RealSymmetricMatrix n := ⟨0, by simp⟩

/-- Diagonal matrices are symmetric. -/
def diagonal (d : n → ℝ) : RealSymmetricMatrix n :=
  ⟨Matrix.diagonal d, (isSymm_diagonal d).isHermitian.isSelfAdjoint⟩

@[simp]
theorem diagonal_val (d : n → ℝ) : (diagonal d).val = Matrix.diagonal d := rfl

/-! ### Trace Inner Product -/

/-- The trace inner product for real symmetric matrices. -/
def traceInner (A B : RealSymmetricMatrix n) : ℝ :=
  HermitianMatrix.traceInnerReal A B

omit [DecidableEq n] in
theorem traceInner_comm (A B : RealSymmetricMatrix n) : traceInner A B = traceInner B A :=
  HermitianMatrix.traceInnerReal_comm A B

omit [DecidableEq n] in
theorem traceInner_self_nonneg (A : RealSymmetricMatrix n) : 0 ≤ traceInner A A :=
  HermitianMatrix.traceInnerReal_self_nonneg A

end RealSymmetricMatrix

end
