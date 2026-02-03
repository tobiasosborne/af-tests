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
in Jordan algebra theory (H-O 2.4.18, equation 2.41).

## Proof path (Hanche-Olsen & Størmer)

The FF is proved via Macdonald's theorem (H-O 2.4.13): any polynomial identity
in 3 variables (degree ≤1 in the third) that holds in special Jordan algebras
holds in all Jordan algebras. Since FF is trivially true in associative algebras,
Macdonald gives it for free.

Prerequisites along the H-O path:
* H-O 2.4.20: Triple product identities (2.42)-(2.44) — from `four_variable_identity`
* H-O 2.4.21: Power formulas (2.45)-(2.46) for U operator
* H-O 2.4.13: Macdonald's theorem itself

## Main results

* `V_eq_L_add_opComm` - V operator decomposition
* `V_opComm_L` - V-L commutator identity
* `fundamental_formula` - The main theorem (sorry, needs Macdonald)

## References

* Hanche-Olsen & Størmer, "Jordan Operator Algebras" (1984), §2.4.16–2.4.18
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
Follows from linearized Jordan identity (H-O 2.33). -/
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

/-! ### Triple Product Identities (H-O 2.4.20) -/

/-- H-O 2.4.20, identity (2.42):
`{a,b,c} ∘ d = {a∘d, b, c} + {a, b, c∘d} - {a, b∘d, c}`.
Proved from three instances of `four_variable_identity`. -/
theorem triple_product_242 (a b c d : J) :
    jmul (triple a b c) d =
    triple (jmul a d) b c + triple a b (jmul c d) - triple a (jmul b d) c := by
  simp only [triple_def, add_jmul, sub_jmul]
  have h1 := four_variable_identity d a b c
  have h2 := four_variable_identity d b c a
  have h3 := four_variable_identity d a c b
  simp only [jmul_comm d] at h1 h2 h3
  rw [jmul_comm (jmul b c) a, jmul_comm (jmul c d) a, jmul_comm (jmul b d) a,
      jmul_comm c (jmul a (jmul b d)),
      jmul_comm (jmul b c) (jmul a d), jmul_comm b a, jmul_comm (jmul c d) (jmul a b),
      jmul_comm c a] at h2
  rw [jmul_comm (jmul a c) b, jmul_comm (jmul c d) b, jmul_comm c (jmul (jmul a d) b),
      jmul_comm (jmul a c) (jmul b d), jmul_comm (jmul c d) (jmul a b), jmul_comm c b] at h3
  have e1 := sub_eq_zero.mpr h1
  have e2 := sub_eq_zero.mpr h2
  have e3 := sub_eq_zero.mpr h3
  apply sub_eq_zero.mp
  calc _
      = (jmul (jmul (jmul a b) c) d + jmul a (jmul (jmul b d) c) + jmul b (jmul (jmul a d) c) -
          (jmul (jmul a b) (jmul c d) + jmul (jmul b d) (jmul a c) + jmul (jmul a d) (jmul b c))) +
        (jmul (jmul a (jmul b c)) d + jmul b (jmul a (jmul c d)) + jmul (jmul a (jmul b d)) c -
          (jmul (jmul a d) (jmul b c) + jmul (jmul a b) (jmul c d) + jmul (jmul b d) (jmul a c))) -
        (jmul (jmul b (jmul a c)) d + jmul a (jmul b (jmul c d)) + jmul (jmul (jmul a d) b) c -
          (jmul (jmul b d) (jmul a c) + jmul (jmul a b) (jmul c d) + jmul (jmul a d) (jmul b c)))
          := by abel
    _ = 0 := by rw [e1, e2, e3]; abel

/-! ### The Fundamental Formula -/

/-- The Fundamental Formula: U_{U_a(b)} = U_a ∘ U_b ∘ U_a (H-O 2.4.18, eq. 2.41).

In any special Jordan algebra this is `(aba)x(aba) = a(b(axa)b)a`, which is
trivially true by associativity. Macdonald's theorem (H-O 2.4.13) then gives
it for all Jordan algebras. -/
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
