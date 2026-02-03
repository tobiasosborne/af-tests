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

/-- The U operator expanded twice for computing U_a(U_b(x)). -/
private theorem U_U_expand (a b x : J) :
    U a (U b x) = 2 • jmul a (jmul a (2 • jmul b (jmul b x) - jmul (jsq b) x)) -
                  jmul (jsq a) (2 • jmul b (jmul b x) - jmul (jsq b) x) := by
  rw [U_def, U_def]

/-! ### V Operator Identities -/

/-- The V operator in terms of L and commutator: V_{a,b} = L_{ab} + [L_a, L_b]. -/
theorem V_eq_L_add_opComm (a b : J) :
    V_linear a b = L (jmul a b) + ⟦L a, L b⟧ := by
  ext x
  simp only [V_linear_apply, triple_def, LinearMap.add_apply, L_apply, opComm_apply]
  abel

/-- Symmetrization: V_{a,b}(x) + V_{b,a}(x) = 2(a∘b)∘x. -/
theorem V_add_V_swap (a b x : J) :
    V_linear a b x + V_linear b a x = 2 • jmul (jmul a b) x := by
  simp only [V_linear_apply, triple_def, jmul_comm b a, two_smul]; abel

/-- V-L commutator: ⟦V_{a,b}, L_c⟧ = ⟦L_a, V_{b,c}⟧ + ⟦L_b, V_{c,a}⟧.
This is a key step toward the Jordan triple product identity (JTPI). -/
theorem V_opComm_L (a b c : J) :
    ⟦V_linear a b, L c⟧ = ⟦L a, V_linear b c⟧ + ⟦L b, V_linear c a⟧ := by
  -- Expand V in terms of L and opComm
  rw [V_eq_L_add_opComm a b, V_eq_L_add_opComm b c, V_eq_L_add_opComm c a]
  -- Distribute commutators over addition
  simp only [opComm_add_left, opComm_add_right]
  -- Apply Jacobi: ⟦⟦L_a, L_b⟧, L_c⟧ = ⟦L_a, ⟦L_b, L_c⟧⟧ - ⟦L_b, ⟦L_a, L_c⟧⟧
  rw [opComm_jacobi (L a) (L b) (L c)]
  -- Rewrite ⟦L_c, L_a⟧ = -⟦L_a, L_c⟧ and absorb negation
  rw [opComm_skew (L c) (L a), opComm_neg_right (L b) ⟦L a, L c⟧]
  -- Key identity: ⟦L_{ab}, L_c⟧ = ⟦L_a, L_{bc}⟧ + ⟦L_b, L_{ca}⟧
  have h := opComm_L_sum a b c
  rw [jmul_comm a c] at h
  rw [← h]; abel

/-! ### Jordan Triple Product Identity (JTPI) -/

/-- JTPI: V_{a, U_a(b)} = U_a ∘ V_{a,b}, i.e., {a, U_a(b), x} = U_a({a, b, x}).
This is the key stepping stone to the fundamental formula.

**Proof approach** (element-level):
- Expand U_a(b) = 2a(ab) - a²b in the middle of {a, -, x}
- Distribute to get 6 LHS terms and 6 RHS terms
- Apply Jordan identity a(a²y) = a²(ay) and operator_commutator_jsq
- The 12-term difference reduces to 0 by the linearized Jordan identity

**References**: McCrimmon "A Taste of Jordan Algebras", Thm 2.4.5;
Hanche-Olsen & Størmer "Jordan Operator Algebras", Thm 3.3.3. -/
theorem jtpi (a b x : J) :
    triple a (U a b) x = U a (triple a b x) := by
  sorry

/-- JTPI with outer symmetry: {x, U_a(b), a} = U_a({x, b, a}).
Follows from `jtpi` and `triple_comm_outer`. -/
theorem jtpi_outer (a b x : J) :
    triple x (U a b) a = U a (triple x b a) := by
  rw [triple_comm_outer x (U a b) a, jtpi, ← triple_comm_outer]

/-! ### The Fundamental Formula -/

/-- The Fundamental Formula: U_{U_a(b)} = U_a ∘ U_b ∘ U_a.
This is THE key identity in Jordan algebra theory.

**Status**: The standard proof uses Shirshov-Cohn (any 2-generated Jordan algebra
is special) or Macdonald's principle, then checks the identity in associative
algebras where it follows from `(aba)x(aba) = a(b(axa)b)a`. A direct element-level
proof is ~100 LOC of Jordan identity manipulation.

**Approach options**:
1. Direct computation: expand both sides, use Jordan identity + linearizations
2. Shirshov-Cohn: prove 2-generated ⇒ special, then use associativity
3. Operator identity: derive from JTPI via linearization argument
-/
theorem fundamental_formula (a b : J) :
    ∀ x, U (U a b) x = U a (U b (U a x)) := by
  intro x
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
