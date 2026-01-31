/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Simple
import AfTests.Jordan.Matrix.FormallyReal
import AfTests.Jordan.SpinFactor.FormallyReal
import AfTests.Jordan.Quaternion.FormallyReal

/-!
# Classification of Simple Formally Real Jordan Algebras

The Jordan-von Neumann-Wigner theorem (1934) classifies all finite-dimensional
simple formally real Jordan algebras into exactly five types.

## The Five Types

| Type | Symbol | Description | Dimension |
|------|--------|-------------|-----------|
| I_n | H_n(ℝ) | n×n real symmetric matrices | n(n+1)/2 |
| II_n | H_n(ℂ) | n×n complex Hermitian matrices | n² |
| III_n | H_n(ℍ) | n×n quaternionic Hermitian matrices | n(2n-1) |
| IV_n | V_n | Spin factors (n ≥ 2) | n |
| V | H₃(𝕆) | 3×3 octonionic Hermitian matrices | 27 |

## Key Properties

1. Types I-IV are **reversible** (embed into associative algebras with reversal)
2. Type V (Albert algebra) is **exceptional** (not special, not reversible)
3. All types are **formally real**: Σᵢ aᵢ² = 0 implies all aᵢ = 0

## Formalization Status

| Type | Defined | FormallyReal | JordanAlgebra |
|------|---------|--------------|---------------|
| I_n | ✓ HermitianMatrix n ℝ | ✓ | ✓ |
| II_n | ✓ HermitianMatrix n ℂ | ✓ | ✓ |
| III_n | ✓ QuaternionHermitianMatrix n | ✓ | ✓ |
| IV_n | ✓ SpinFactor n | ✓ | ✓ |
| V | ✗ (octonions not in mathlib) | ✗ | ✗ |

## References

* Jordan, von Neumann, Wigner, "On an Algebraic Generalization of the
  Quantum Mechanical Formalism" (1934)
* Hanche-Olsen & Størmer, "Jordan Operator Algebras", Chapter 3
-/

namespace JordanAlgebra

/-! ### Type Enumeration -/

/-- The five types of simple formally real Jordan algebras. -/
inductive SimpleType where
  | typeI   : ℕ → SimpleType  -- H_n(ℝ): real symmetric matrices
  | typeII  : ℕ → SimpleType  -- H_n(ℂ): complex Hermitian matrices
  | typeIII : ℕ → SimpleType  -- H_n(ℍ): quaternionic Hermitian matrices
  | typeIV  : ℕ → SimpleType  -- V_n: spin factors (n ≥ 2)
  | typeV   : SimpleType      -- H₃(𝕆): Albert algebra (exceptional)
  deriving DecidableEq, Repr

namespace SimpleType

/-- The dimension of a simple type. -/
def dimension : SimpleType → ℕ
  | typeI n   => n * (n + 1) / 2
  | typeII n  => n * n
  | typeIII n => n * (2 * n - 1)
  | typeIV n  => n
  | typeV     => 27

/-- Whether a type is reversible (embeds into associative with reversal). -/
def isReversible : SimpleType → Bool
  | typeV => false
  | _     => true

/-- Whether a type is exceptional (not special). -/
def isExceptional : SimpleType → Bool
  | typeV => true
  | _     => false

/-- The minimum n for which the type is defined. -/
def minIndex : SimpleType → ℕ
  | typeI _   => 1
  | typeII _  => 1
  | typeIII _ => 1
  | typeIV _  => 2  -- V_1 ≅ ℝ, not "spin"
  | typeV     => 0  -- No index

end SimpleType

/-! ### Instances for Concrete Types -/

section Instances

variable {n : Type*} [Fintype n] [DecidableEq n]

-- Type I: Real symmetric matrices ≅ HermitianMatrix n ℝ
-- (requires RCLike ℝ instance, which exists)

-- Type II: Complex Hermitian matrices = HermitianMatrix n ℂ
-- Already defined and has FormallyRealJordan instance

-- Type III: Quaternionic Hermitian matrices = QuaternionHermitianMatrix n
-- Already defined and has FormallyRealJordan instance

-- Type IV: Spin factors = SpinFactor m for m : ℕ
-- Already defined and has FormallyRealJordan instance

-- Type V: Albert algebra (3×3 octonion Hermitian)
-- Not formalized: octonions not in mathlib

end Instances

end JordanAlgebra
