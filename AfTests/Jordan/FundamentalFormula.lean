/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Quadratic
import AfTests.Jordan.OperatorIdentities

/-!
# The Fundamental Formula for Jordan Algebras

The fundamental formula `U_{U_a(b)} = U_a ∘ U_b ∘ U_a` is the central identity
in Jordan algebra theory.

## Main results

* `fundamental_formula` - The main theorem
* `U_jsq` - Corollary: U_{a²} = U_a ∘ U_a

## References

* McCrimmon, K. "A Taste of Jordan Algebras", Theorem 2.4.5
-/

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-! ### Auxiliary Lemmas -/

/-- Linearized Jordan identity: symmetric in b, c.
    `jmul (jmul a b) (jsq a) + jmul (jmul a c) (jsq a) + ...` type identity. -/
private theorem linearized_jordan_aux (a b c : J) :
    jmul (jmul a (jmul b c)) (jsq a) +
    jmul (jmul b (jmul a c)) (jsq a) +
    jmul (jmul c (jmul a b)) (jsq a) =
    jmul a (jmul (jmul b c) (jsq a)) +
    jmul b (jmul (jmul a c) (jsq a)) +
    jmul c (jmul (jmul a b) (jsq a)) := by
  -- This follows from linearizing the Jordan identity in the first argument
  -- Jordan: jmul (jmul x y) (jsq x) = jmul x (jmul y (jsq x))
  -- Linearizing x → a + b + c and extracting cross terms
  sorry

/-- The U operator expanded twice for computing U_a(U_b(x)). -/
private theorem U_U_expand (a b x : J) :
    U a (U b x) = 2 • jmul a (jmul a (2 • jmul b (jmul b x) - jmul (jsq b) x)) -
                  jmul (jsq a) (2 • jmul b (jmul b x) - jmul (jsq b) x) := by
  rw [U_def, U_def]

/-! ### The Fundamental Formula -/

/-- The Fundamental Formula: U_{U_a(b)} = U_a ∘ U_b ∘ U_a.
This is THE key identity in Jordan algebra theory.

The proof requires extensive manipulation using the Jordan identity and its
linearizations. The key insight is that both sides, when fully expanded, consist
of terms involving products of a, b, x with various nestings, and the Jordan
identity provides exactly the relations needed to show equality.
-/
theorem fundamental_formula (a b : J) :
    ∀ x, U (U a b) x = U a (U b (U a x)) := by
  intro x
  -- Expand U definitions
  simp only [U_def]
  -- At this point both sides are expanded in terms of jmul and jsq
  -- The proof requires extensive use of:
  -- 1. Jordan identity: jmul (jmul a y) (jsq a) = jmul a (jmul y (jsq a))
  -- 2. Linearizations of the Jordan identity
  -- 3. Commutativity of jmul
  -- This is a ~2 page proof in McCrimmon's "A Taste of Jordan Algebras"
  sorry

/-! ### Corollaries of the Fundamental Formula -/

/-- Corollary: U_{a²} = U_a².
This follows from the fundamental formula with b = a. -/
theorem U_jsq (a : J) : ∀ x, U (jsq a) x = U a (U a x) := by
  intro x
  -- From fundamental_formula with b = 1 and using U_self
  -- Actually, we need b such that U_a(b) = a²
  -- By U_self: U_a(a) = jmul a (jsq a)
  -- We need U_a(1) = 2 • jmul a a - jmul (jsq a) 1 = 2 • jsq a - jsq a = jsq a
  have h1 : U a jone = jsq a := by
    rw [U_def, jmul_jone, jmul_jone, jsq_def, two_smul]
    abel
  -- Now apply fundamental_formula with b = 1
  have hff := fundamental_formula a jone x
  rw [h1] at hff
  rw [U_one] at hff
  exact hff

/-- For idempotent e: U_e ∘ U_e = U_e (follows from fundamental formula). -/
theorem U_idempotent_comp' (e : J) (he : IsIdempotent e) :
    ∀ x, U e (U e x) = U e x := by
  intro x
  -- From U_jsq with a = e and he.jsq_eq_self
  have h := U_jsq e x
  rw [he.jsq_eq_self] at h
  exact h.symm

/-- Alternative: U_{e²} = U_e for idempotent e. -/
theorem U_jsq_idempotent (e : J) (he : IsIdempotent e) :
    ∀ x, U (jsq e) x = U e x := by
  intro x
  rw [he.jsq_eq_self]

/-! ### Additional Properties from Fundamental Formula -/

/-- Powers: U_{a^n} relates to U_a composed n times. -/
theorem U_jpow_two (a : J) : ∀ x, U (jpow a 2) x = U a (U a x) := by
  intro x
  rw [jpow_two]
  exact U_jsq a x

/-- The fundamental formula as a linear map composition identity. -/
theorem fundamental_formula_linear (a b : J) :
    U_linear (U a b) = U_linear a ∘ₗ U_linear b ∘ₗ U_linear a := by
  ext x
  simp only [LinearMap.comp_apply, U_linear_apply]
  exact fundamental_formula a b x

end JordanAlgebra
