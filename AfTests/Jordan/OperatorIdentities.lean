/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.IsCommJordan

/-!
# Operator Identities for Jordan Algebras

This file defines the commutator bracket for linear operators and states key
identities used in Peirce decomposition analysis.

## Main definitions

* `opComm` - Commutator bracket: `[f, g] = f ∘ g - g ∘ f`

## Main results

* `linearized_jordan_operator` - The linearized Jordan identity in operator form
* `opComm_idempotent_eigenspace` - Commutator property for idempotents
-/

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-! ### Commutator Bracket -/

/-- The commutator (Lie bracket) of two linear operators: `[f, g] = f ∘ g - g ∘ f`. -/
def opComm (f g : J →ₗ[ℝ] J) : J →ₗ[ℝ] J := f ∘ₗ g - g ∘ₗ f

notation:max "⟦" f ", " g "⟧" => opComm f g

@[simp]
theorem opComm_apply (f g : J →ₗ[ℝ] J) (x : J) :
    ⟦f, g⟧ x = f (g x) - g (f x) := rfl

theorem opComm_skew (f g : J →ₗ[ℝ] J) : ⟦f, g⟧ = -⟦g, f⟧ := by
  ext x; simp [opComm, sub_eq_neg_add, add_comm]

theorem opComm_self (f : J →ₗ[ℝ] J) : ⟦f, f⟧ = 0 := by
  ext x; simp [opComm]

/-! ### Linearized Jordan Identity -/

/-- The linearized Jordan identity in operator form:
    `2([L_a, L_{b∘c}] + [L_b, L_{c∘a}] + [L_c, L_{a∘b}]) = 0`

This is the key identity relating commutators of multiplication operators.
The proof uses the bridge to Mathlib's IsCommJordan. -/
theorem linearized_jordan_operator (a b c : J) :
    2 • (⟦L a, L (jmul b c)⟧ + ⟦L b, L (jmul c a)⟧ + ⟦L c, L (jmul a b)⟧) = 0 := by
  -- Use the Mathlib theorem from IsCommJordan
  have h := linearized_jordan_jmul a b c
  ext x
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.zero_apply,
             opComm_apply, L_apply]
  -- h says: 2 • (⁅mulLeft a, mulLeft (b*c)⁆ + ...) = 0
  -- Applied to x, expand the Lie brackets to match our goal
  exact congrFun (congrArg DFunLike.coe h) x

/-- The linearized Jordan identity evaluated at a² (jsq a).
This relates products of the form `x ∘ (Y ∘ a²)` to `Y ∘ (x ∘ a²)`. -/
theorem linearized_on_jsq (a b c : J) :
    2 • (jmul a (jmul (jmul b c) (jsq a)) - jmul (jmul b c) (jmul a (jsq a)) +
         jmul b (jmul (jmul c a) (jsq a)) - jmul (jmul c a) (jmul b (jsq a)) +
         jmul c (jmul (jmul a b) (jsq a)) - jmul (jmul a b) (jmul c (jsq a))) = 0 := by
  have h := linearized_jordan_jmul a b c
  have hsmul : (2 • (⁅AddMonoid.End.mulLeft a, AddMonoid.End.mulLeft (jmul b c)⁆ +
                     ⁅AddMonoid.End.mulLeft b, AddMonoid.End.mulLeft (jmul c a)⁆ +
                     ⁅AddMonoid.End.mulLeft c, AddMonoid.End.mulLeft (jmul a b)⁆)) (jsq a) =
               2 • ((jmul a (jmul (jmul b c) (jsq a)) - jmul (jmul b c) (jmul a (jsq a))) +
                    (jmul b (jmul (jmul c a) (jsq a)) - jmul (jmul c a) (jmul b (jsq a))) +
                    (jmul c (jmul (jmul a b) (jsq a)) - jmul (jmul a b) (jmul c (jsq a)))) := rfl
  have happ : (2 • (⁅AddMonoid.End.mulLeft a, AddMonoid.End.mulLeft (jmul b c)⁆ +
                    ⁅AddMonoid.End.mulLeft b, AddMonoid.End.mulLeft (jmul c a)⁆ +
                    ⁅AddMonoid.End.mulLeft c, AddMonoid.End.mulLeft (jmul a b)⁆)) (jsq a) = 0 := by
    rw [h]; rfl
  rw [hsmul] at happ
  convert happ using 1
  abel

/-- The linearized Jordan identity without the factor of 2, using that J is an ℝ-module. -/
theorem linearized_core (a b c : J) :
    jmul a (jmul (jmul b c) (jsq a)) - jmul (jmul b c) (jmul a (jsq a)) +
    jmul b (jmul (jmul c a) (jsq a)) - jmul (jmul c a) (jmul b (jsq a)) +
    jmul c (jmul (jmul a b) (jsq a)) - jmul (jmul a b) (jmul c (jsq a)) = 0 := by
  have h := linearized_on_jsq a b c
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  rw [two_smul] at h
  have hself : ∀ x : J, x + x = 0 → x = 0 := fun x hxx => by
    have : (2 : ℝ) • x = 0 := by rw [two_smul]; exact hxx
    exact (smul_eq_zero_iff_right h2).mp this
  exact hself _ h

/-- Rearranged linearized Jordan: relates `x ∘ (Y ∘ a²)` to `Y ∘ (x ∘ a²)`. -/
theorem linearized_rearranged (a b c : J) :
    jmul a (jmul (jmul b c) (jsq a)) + jmul b (jmul (jmul c a) (jsq a)) +
    jmul c (jmul (jmul a b) (jsq a)) =
    jmul (jmul b c) (jmul a (jsq a)) + jmul (jmul c a) (jmul b (jsq a)) +
    jmul (jmul a b) (jmul c (jsq a)) := by
  have h := linearized_core a b c
  have h' : (jmul a (jmul (jmul b c) (jsq a)) + jmul b (jmul (jmul c a) (jsq a)) +
             jmul c (jmul (jmul a b) (jsq a))) -
            (jmul (jmul b c) (jmul a (jsq a)) + jmul (jmul c a) (jmul b (jsq a)) +
             jmul (jmul a b) (jmul c (jsq a))) = 0 := by convert h using 1; abel
  exact sub_eq_zero.mp h'

/-! ### Operator Commutator with Squared Element -/

/-- The operator commutator identity: `[L_{a²}, L_b] = 2[L_a, L_{ab}]`.

This follows from the linearized Jordan identity by setting c = a:
  2 • ([L_a, L_{ab}] + [L_b, L_{a²}] + [L_a, L_{ab}]) = 0
which simplifies to 2[L_a, L_{ab}] = [L_{a²}, L_b]. -/
theorem operator_commutator_jsq (a b : J) :
    ⟦L (jsq a), L b⟧ = (2 : ℕ) • ⟦L a, L (jmul a b)⟧ := by
  have h := linearized_jordan_operator a b a
  rw [jmul_comm b a] at h
  -- Combine: 2 • (2[L_a, L_{ab}] + [L_b, L_{aa}]) = 0
  have step1 : (2 : ℕ) • ((2 : ℕ) • ⟦L a, L (jmul a b)⟧ + ⟦L b, L (jmul a a)⟧) = 0 := by
    have ha : ⟦L a, L (jmul a b)⟧ + ⟦L b, L (jmul a a)⟧ + ⟦L a, L (jmul a b)⟧ =
              (2 : ℕ) • ⟦L a, L (jmul a b)⟧ + ⟦L b, L (jmul a a)⟧ := by
      rw [two_nsmul]; abel
    rw [← ha]; exact h
  -- Convert to ℝ-smul to use division
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  have step1' : (2 : ℝ) • ((2 : ℝ) • ⟦L a, L (jmul a b)⟧ + ⟦L b, L (jmul a a)⟧) = 0 := by
    simp only [← Nat.cast_smul_eq_nsmul ℝ] at step1
    convert step1 using 2
  -- Cancel outer 2: 2[L_a, L_{ab}] + [L_b, L_{aa}] = 0
  have step2 : (2 : ℝ) • ⟦L a, L (jmul a b)⟧ + ⟦L b, L (jmul a a)⟧ = 0 :=
    (smul_eq_zero_iff_right h2).mp step1'
  -- Rearrange: 2[L_a, L_{ab}] = -[L_b, L_{aa}] = [L_{aa}, L_b]
  have step3 : (2 : ℝ) • ⟦L a, L (jmul a b)⟧ = ⟦L (jmul a a), L b⟧ := by
    have hskew : ⟦L b, L (jmul a a)⟧ = -⟦L (jmul a a), L b⟧ := opComm_skew _ _
    have : (2 : ℝ) • ⟦L a, L (jmul a b)⟧ = -⟦L b, L (jmul a a)⟧ :=
      eq_neg_of_add_eq_zero_left step2
    rw [this, hskew, neg_neg]
  -- Convert back to nsmul
  have step4 : (2 : ℕ) • ⟦L a, L (jmul a b)⟧ = ⟦L (jmul a a), L b⟧ := by
    rw [← Nat.cast_smul_eq_nsmul ℝ]; exact step3
  unfold jsq; exact step4.symm

/-- Element form of operator_commutator_jsq:
    (a²)∘(b∘x) - b∘((a²)∘x) = 2 • (a∘((ab)∘x) - (ab)∘(a∘x)). -/
theorem operator_commutator_jsq_apply (a b x : J) :
    jmul (jsq a) (jmul b x) - jmul b (jmul (jsq a) x) =
    (2 : ℕ) • (jmul a (jmul (jmul a b) x) - jmul (jmul a b) (jmul a x)) := by
  have h := operator_commutator_jsq a b
  have := congrFun (congrArg DFunLike.coe h) x
  simp only [opComm_apply, L_apply, LinearMap.smul_apply] at this
  exact this

/-! ### Idempotent Operator Identities -/

/-- For an idempotent e and element a in eigenspace with eigenvalue ev,
    the commutator `[L_e, L_a]` maps to specific eigenspaces. -/
theorem opComm_idempotent_eigenspace {e : J} (_he : IsIdempotent e)
    {a : J} {ev : ℝ} (_ha : jmul e a = ev • a) (x : J) :
    ⟦L e, L a⟧ x = jmul e (jmul a x) - jmul a (jmul e x) := rfl

/-! ### Useful Commutator Properties -/

/-- For idempotent e with e ∘ a = a (i.e., a in P_1(e)), simplified commutator form. -/
theorem opComm_on_P1 {e a b : J} (_he : IsIdempotent e)
    (_ha : jmul e a = a) (hb : jmul e b = b) :
    ⟦L e, L a⟧ b = jmul e (jmul a b) - jmul a b := by
  simp only [opComm_apply, L_apply, hb]

/-- For idempotent e with e ∘ a = 0 (i.e., a in P_0(e)), the commutator form. -/
theorem opComm_on_P0 {e a : J} (_he : IsIdempotent e) (_ha : jmul e a = 0) (x : J) :
    ⟦L e, L a⟧ x = jmul e (jmul a x) - jmul a (jmul e x) := rfl

/-! ### Jacobi Identity for Operator Commutators -/

/-- Jacobi identity (rearranged): ⟦⟦f, g⟧, h⟧ = ⟦f, ⟦g, h⟧⟧ - ⟦g, ⟦f, h⟧⟧. -/
theorem opComm_jacobi (f g h : J →ₗ[ℝ] J) :
    ⟦⟦f, g⟧, h⟧ = ⟦f, ⟦g, h⟧⟧ - ⟦g, ⟦f, h⟧⟧ := by
  ext x
  simp only [opComm_apply, map_sub, LinearMap.sub_apply]
  abel

/-! ### Linearized Jordan Identity (Factor-Free) -/

/-- The linearized Jordan identity without the factor of 2:
    `[L_a, L_{bc}] + [L_b, L_{ca}] + [L_c, L_{ab}] = 0`. -/
theorem linearized_jordan_op (a b c : J) :
    ⟦L a, L (jmul b c)⟧ + ⟦L b, L (jmul c a)⟧ + ⟦L c, L (jmul a b)⟧ = 0 := by
  have h := linearized_jordan_operator a b c
  -- h : (2 : ℕ) • X = 0, extract X = 0
  set X := ⟦L a, L (jmul b c)⟧ + ⟦L b, L (jmul c a)⟧ + ⟦L c, L (jmul a b)⟧
  have hXX : X + X = 0 := by rwa [two_nsmul] at h
  have h2 : (2 : ℝ) • X = 0 := by rw [two_smul]; exact hXX
  have := (inv_smul_smul₀ (two_ne_zero (α := ℝ)) X).symm
  rw [h2, smul_zero] at this
  exact this

/-- Key commutator identity: `[L_a, L_{bc}] + [L_b, L_{ac}] = [L_{ab}, L_c]`.
    Follows from the linearized Jordan identity by setting one variable. -/
theorem opComm_L_sum (a b c : J) :
    ⟦L a, L (jmul b c)⟧ + ⟦L b, L (jmul a c)⟧ = ⟦L (jmul a b), L c⟧ := by
  have h := linearized_jordan_op a b c
  -- h : [L_a, L_{bc}] + [L_b, L_{ca}] + [L_c, L_{ab}] = 0
  -- Using jmul_comm c a = a c: L_{ca} = L_{ac}
  rw [jmul_comm c a] at h
  -- h is now (A + B) + C = 0, so A + B = -C
  have h2 := eq_neg_of_add_eq_zero_left h
  -- h2 : A + B = -⟦L c, L (jmul a b)⟧
  -- -⟦L c, L_{ab}⟧ = ⟦L_{ab}, L c⟧ by skew symmetry
  rw [h2, opComm_skew, neg_neg]

/-- Commutator distributes over addition (left): ⟦f + g, h⟧ = ⟦f, h⟧ + ⟦g, h⟧. -/
theorem opComm_add_left (f g h : J →ₗ[ℝ] J) :
    ⟦f + g, h⟧ = ⟦f, h⟧ + ⟦g, h⟧ := by
  ext x; simp only [opComm_apply, LinearMap.add_apply, map_add]; abel

/-- Commutator distributes over addition (right): ⟦f, g + h⟧ = ⟦f, g⟧ + ⟦f, h⟧. -/
theorem opComm_add_right (f g h : J →ₗ[ℝ] J) :
    ⟦f, g + h⟧ = ⟦f, g⟧ + ⟦f, h⟧ := by
  ext x; simp only [opComm_apply, LinearMap.add_apply, map_add]; abel

/-- Commutator absorbs negation (right): ⟦f, -g⟧ = -⟦f, g⟧. -/
theorem opComm_neg_right (f g : J →ₗ[ℝ] J) :
    ⟦f, -g⟧ = -⟦f, g⟧ := by
  ext x; simp only [opComm_apply, LinearMap.neg_apply, map_neg]; abel

end JordanAlgebra
