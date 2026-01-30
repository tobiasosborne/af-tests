/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Basic
import AfTests.Jordan.Matrix.Instance
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Algebra.Star.Module

/-!
# Quaternionic Hermitian Matrices

Quaternionic Hermitian matrices (satisfying `Aᴴ = A` where `ᴴ` is conjugate transpose)
form a Jordan algebra over ℝ. This file defines the type and proves basic properties.

## Main definitions

* `QuaternionHermitianMatrix` - Type alias for `HermitianMatrix n (Quaternion ℝ)`

## Main results

* `CharZero (Quaternion ℝ)` - Quaternions have characteristic zero
* `conjTranspose_mul_hermitian` - For Hermitian A, B: `(A * B)ᴴ = B * A`

## Implementation notes

The star operation on `Quaternion ℝ` is quaternion conjugation:
`star ⟨a, b, c, d⟩ = ⟨a, -b, -c, -d⟩`.
For a matrix A over quaternions, `Aᴴ_{ij} = star(A_{ji})`.

A matrix A is Hermitian iff `Aᴴ = A`, which for quaternions means:
- Diagonal entries are real (pure real part)
- Off-diagonal: `star(A j i) = A i j`

Unlike complex Hermitian matrices, quaternionic Hermitian matrices require
special handling because quaternions are non-commutative.
-/

noncomputable section

open Matrix

/-! ### CharZero Instance -/

/-- Quaternions over ℝ have characteristic zero. -/
instance Quaternion.instCharZero : CharZero (Quaternion ℝ) where
  cast_injective m n h := by
    have h' : (m : Quaternion ℝ).re = (n : Quaternion ℝ).re := by rw [h]
    simp only [Quaternion.re_natCast] at h'
    exact Nat.cast_injective h'

/-! ### StarModule Instance -/

/-- Quaternions over ℝ form a `StarModule` over ℝ.

This allows real scalar multiplication to commute with conjugate transpose
in quaternion matrices: `(r • A)ᴴ = r • Aᴴ`. -/
instance Quaternion.instStarModule : StarModule ℝ (Quaternion ℝ) where
  star_smul r q := by
    simp only [Algebra.smul_def]
    rw [StarMul.star_mul]
    have h1 : star ((algebraMap ℝ (Quaternion ℝ)) r) = (algebraMap ℝ (Quaternion ℝ)) r := by
      change star (r : Quaternion ℝ) = (r : Quaternion ℝ)
      exact Quaternion.star_coe r
    have h2 : (star r : ℝ) = r := star_trivial r
    rw [h1, h2]
    change star q * (r : Quaternion ℝ) = (r : Quaternion ℝ) * star q
    rw [Quaternion.coe_commutes]

/-! ### Scalar-Star Commutativity -/

/-- Real scalars commute with star in quaternions.

For r : ℝ and q : Quaternion ℝ, we have `star(r • q) = r • star(q)`.
This holds because real quaternions are central and self-conjugate. -/
theorem Quaternion.smul_star_comm (r : ℝ) (q : Quaternion ℝ) : star (r • q) = r • star q := by
  simp only [Algebra.smul_def]
  have h1 : algebraMap ℝ (Quaternion ℝ) r = (r : Quaternion ℝ) := rfl
  rw [h1, StarMul.star_mul, Quaternion.star_coe, Quaternion.coe_commutes]

/-! ### Quaternionic Hermitian Matrix Type -/

/-- Quaternionic Hermitian matrices, defined as `HermitianMatrix n (Quaternion ℝ)`.

These are matrices A satisfying `Aᴴ = A` where `ᴴ` is conjugate transpose
using quaternion conjugation. -/
abbrev QuaternionHermitianMatrix (n : Type*) [Fintype n] := HermitianMatrix n (Quaternion ℝ)

namespace QuaternionHermitianMatrix

variable {n : Type*} [Fintype n]

/-! ### Basic Properties -/

/-- A quaternionic Hermitian matrix satisfies `Aᴴ = A`. -/
theorem conjTranspose_eq (A : QuaternionHermitianMatrix n) : A.val.conjTranspose = A.val :=
  A.prop.isHermitian.eq

/-- Construct a QuaternionHermitianMatrix from a Hermitian matrix. -/
def ofHermitian (A : Matrix n n (Quaternion ℝ)) (h : A.IsHermitian) :
    QuaternionHermitianMatrix n :=
  ⟨A, h.isSelfAdjoint⟩

@[simp]
theorem ofHermitian_val (A : Matrix n n (Quaternion ℝ)) (h : A.IsHermitian) :
    (ofHermitian A h).val = A := rfl

/-- The underlying matrix of a QuaternionHermitianMatrix is Hermitian. -/
theorem val_isHermitian (A : QuaternionHermitianMatrix n) : A.val.IsHermitian :=
  A.prop.isHermitian

/-! ### Diagonal Entries are Real -/

/-- Diagonal entries of a quaternionic Hermitian matrix are real (self-conjugate). -/
theorem diag_self_conj (A : QuaternionHermitianMatrix n) (i : n) :
    star (A.val i i) = A.val i i :=
  A.prop.isHermitian.apply i i

/-! ### Conjugate Transpose Properties -/

omit [Fintype n] in
/-- For real scalar multiplication, conjugate transpose distributes. -/
theorem conjTranspose_smul_real (r : ℝ) (A : Matrix n n (Quaternion ℝ)) :
    (r • A).conjTranspose = r • A.conjTranspose := by
  funext i j
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply]
  exact Quaternion.smul_star_comm r (A j i)

/-- For Hermitian quaternion matrices A, B: `(A * B)ᴴ = B * A`.

This is anti-commutative because quaternion star is anti-multiplicative. -/
theorem conjTranspose_mul_hermitian {A B : Matrix n n (Quaternion ℝ)}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B) :
    (A * B).conjTranspose = B * A := by
  rw [Matrix.conjTranspose_mul, hA.eq, hB.eq]

/-! ### Special Matrices -/

variable [DecidableEq n]

/-- The identity matrix is Hermitian. -/
def one : QuaternionHermitianMatrix n :=
  ⟨1, isHermitian_one.isSelfAdjoint⟩

/-- The zero matrix is Hermitian. -/
def zero : QuaternionHermitianMatrix n := ⟨0, by simp⟩

/-- Real diagonal matrices are Hermitian over quaternions.

For a real-valued diagonal, the resulting matrix is Hermitian since real numbers
embed as self-conjugate quaternions. -/
def realDiagonal (d : n → ℝ) : QuaternionHermitianMatrix n :=
  ⟨Matrix.diagonal (fun i => (d i : Quaternion ℝ)), by
    have h : (Matrix.diagonal (fun i => (d i : Quaternion ℝ))).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
      congr 1
      funext i
      simp only [Pi.star_apply, Quaternion.star_coe]
    exact h.isSelfAdjoint⟩

@[simp]
theorem realDiagonal_val (d : n → ℝ) :
    (realDiagonal d).val = Matrix.diagonal (fun i => (d i : Quaternion ℝ)) := rfl

end QuaternionHermitianMatrix

end
