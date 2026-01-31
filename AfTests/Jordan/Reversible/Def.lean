/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Basic
import Mathlib.Algebra.Symmetrized

/-!
# Reversible Jordan Algebras

A Jordan algebra is reversible if it can be realized as a Jordan subalgebra of an
associative algebra that is closed under the "reversal" operation abc + cba.

## Main definitions

* `IsReversible J` - Typeclass for reversible Jordan algebras

## References

* Hanche-Olsen & Størmer, "Jordan Operator Algebras", Section 2.5
-/

open JordanAlgebra

/-- A Jordan algebra is reversible if it admits an embedding into an associative algebra
A such that the image is closed under the triple product abc + cba.

This is a property of the abstract Jordan algebra, not tied to a specific embedding.
Every special Jordan algebra (one that embeds into an associative algebra) that is
closed under reversal is reversible. -/
class IsReversible (J : Type*) [JordanAlgebra J] : Prop where
  /-- There exists an associative algebra and an embedding. -/
  exists_embedding : ∃ (A : Type*) (_ : Ring A) (_ : Algebra ℝ A)
    (f : J →ₗ[ℝ] A),
    -- f preserves the Jordan product
    (∀ a b : J, f (jmul a b) = (1/2 : ℝ) • (f a * f b + f b * f a)) ∧
    -- f preserves the identity
    f jone = 1 ∧
    -- f is injective
    Function.Injective f ∧
    -- Image is closed under reversal: abc + cba
    (∀ a b c : J, ∃ d : J, f d = f a * f b * f c + f c * f b * f a)

namespace IsReversible

variable {J : Type*} [JordanAlgebra J] [IsReversible J]

-- Note: Derived theorems require careful universe handling.
-- See Jordan/Reversible/Properties.lean for results about reversible algebras.

end IsReversible

/-!
## Instances

Concrete instances of `IsReversible` are provided in:
- `Jordan/Matrix/Reversible.lean` - Hermitian matrices
- `Jordan/SpinFactor/Reversible.lean` - Spin factors
-/
