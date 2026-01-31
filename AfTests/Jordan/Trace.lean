/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.FormallyReal.Def

/-!
# Trace on Jordan Algebras

This file defines the trace functional on Jordan algebras and the trace inner product.

## Main definitions

* `JordanTrace` - Class for Jordan algebras with a trace functional
* `traceInner` - The trace inner product τ(a,b) = trace(a ∘ b)

## Main results

* `traceInner_symm` - The trace inner product is symmetric
* `traceInner_add_left` - Linearity in first argument
-/

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-! ### Trace Class -/

/-- A Jordan algebra with a trace functional.

The trace is a linear functional that is symmetric under the Jordan product. -/
class JordanTrace (J : Type*) [JordanAlgebra J] where
  /-- The trace functional. -/
  trace : J → ℝ
  /-- Trace is additive. -/
  trace_add : ∀ a b, trace (a + b) = trace a + trace b
  /-- Trace is homogeneous. -/
  trace_smul : ∀ r a, trace (r • a) = r * trace a
  /-- Trace is symmetric under Jordan product. -/
  trace_jmul_comm : ∀ a b, trace (jmul a b) = trace (jmul b a)
  /-- L_a is self-adjoint w.r.t. the trace inner product: τ(a∘v, w) = τ(v, a∘w).
  This is the key property for eigenspace orthogonality. For Hermitian matrices,
  it follows from cyclicity of the trace. -/
  trace_L_selfadjoint : ∀ a v w, trace (jmul (jmul a v) w) = trace (jmul v (jmul a w))
  /-- Trace of identity is positive. -/
  trace_jone_pos : 0 < trace jone

export JordanTrace (trace trace_add trace_smul trace_jmul_comm trace_L_selfadjoint trace_jone_pos)

/-! ### Basic Trace Properties -/

variable [JordanTrace J]

theorem trace_zero : trace (0 : J) = 0 := by
  have h := trace_smul (0 : ℝ) (jone : J)
  simp only [zero_smul, zero_mul] at h
  exact h

theorem trace_neg (a : J) : trace (-a) = -trace a := by
  have h := trace_smul (-1 : ℝ) a
  simp only [neg_one_smul, neg_one_mul] at h
  exact h

theorem trace_sub (a b : J) : trace (a - b) = trace a - trace b := by
  rw [sub_eq_add_neg, trace_add, trace_neg, sub_eq_add_neg]

/-! ### Trace Inner Product -/

/-- The trace inner product: τ(a,b) = trace(a ∘ b). -/
def traceInner (a b : J) : ℝ := trace (jmul a b)

theorem traceInner_symm (a b : J) : traceInner a b = traceInner b a := by
  unfold traceInner
  rw [jmul_comm]

theorem traceInner_add_left (a b c : J) :
    traceInner (a + b) c = traceInner a c + traceInner b c := by
  unfold traceInner
  rw [add_jmul, trace_add]

theorem traceInner_add_right (a b c : J) :
    traceInner a (b + c) = traceInner a b + traceInner a c := by
  rw [traceInner_symm, traceInner_add_left, traceInner_symm a b, traceInner_symm a c]

theorem traceInner_smul_left (r : ℝ) (a b : J) :
    traceInner (r • a) b = r * traceInner a b := by
  unfold traceInner
  rw [jmul_smul, trace_smul]

theorem traceInner_smul_right (r : ℝ) (a b : J) :
    traceInner a (r • b) = r * traceInner a b := by
  rw [traceInner_symm, traceInner_smul_left, traceInner_symm]

theorem traceInner_zero_left (a : J) : traceInner 0 a = 0 := by
  unfold traceInner
  rw [zero_jmul, trace_zero]

theorem traceInner_zero_right (a : J) : traceInner a 0 = 0 := by
  rw [traceInner_symm, traceInner_zero_left]

theorem traceInner_neg_left (a b : J) : traceInner (-a) b = -traceInner a b := by
  unfold traceInner
  rw [neg_jmul, trace_neg]

theorem traceInner_neg_right (a b : J) : traceInner a (-b) = -traceInner a b := by
  rw [traceInner_symm, traceInner_neg_left, traceInner_symm]

/-- L_a is self-adjoint w.r.t. the trace inner product. -/
theorem traceInner_jmul_left (a v w : J) :
    traceInner (jmul a v) w = traceInner v (jmul a w) := by
  unfold traceInner
  exact trace_L_selfadjoint a v w

end JordanAlgebra

/-! ### Non-degeneracy -/

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-- A trace on a formally real Jordan algebra that is positive definite.

This is the key property needed for spectral theory: trace(a²) > 0 for a ≠ 0.
In concrete cases (Hermitian matrices), this follows from the formula trace(A*A) = Σ|aᵢⱼ|².
For abstract Jordan algebras, this is an axiom that is verified via spectral theory. -/
class FormallyRealTrace (J : Type*) [JordanAlgebra J] extends JordanTrace J where
  /-- Trace of a square is non-negative. -/
  trace_jsq_nonneg : ∀ a : J, 0 ≤ trace (jsq a)
  /-- Trace of a square is zero iff the element is zero. -/
  trace_jsq_eq_zero_iff : ∀ a : J, trace (jsq a) = 0 ↔ a = 0

export FormallyRealTrace (trace_jsq_nonneg trace_jsq_eq_zero_iff)

variable [FormallyRealTrace J]

/-- In a formally real Jordan algebra with trace, traceInner is positive definite. -/
theorem traceInner_self_nonneg (a : J) : 0 ≤ traceInner a a :=
  trace_jsq_nonneg a

/-- traceInner(a,a) = 0 iff a = 0. -/
theorem traceInner_self_eq_zero_iff {a : J} : traceInner a a = 0 ↔ a = 0 :=
  trace_jsq_eq_zero_iff a

/-- In a formally real Jordan algebra, traceInner(a,a) > 0 for a ≠ 0. -/
theorem traceInner_self_pos {a : J} (ha : a ≠ 0) : 0 < traceInner a a := by
  have hne : ¬(traceInner a a = 0) := by
    rw [traceInner_self_eq_zero_iff]
    exact ha
  exact lt_of_le_of_ne (traceInner_self_nonneg a) (Ne.symm hne)

/-- Non-degeneracy: if τ(a,b) = 0 for all b, then a = 0. -/
theorem traceInner_nondegenerate {a : J} (h : ∀ b, traceInner a b = 0) : a = 0 := by
  have := h a
  rw [traceInner_self_eq_zero_iff] at this
  exact this

end JordanAlgebra
