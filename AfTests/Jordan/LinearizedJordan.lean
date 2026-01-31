/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.OperatorIdentities

/-!
# Linearized Jordan Identities (Hanche-Olsen 2.33-2.35)

This file formalizes the key operator identities from Hanche-Olsen & Størmer
"Jordan Operator Algebras" Section 2.4.

## Main results

* `four_variable_identity` - Identity (2.34): the four-variable Jordan identity
* `operator_formula` - Identity (2.35): the operator composition formula

## References

* Hanche-Olsen & Størmer, "Jordan Operator Algebras" (1984), Section 2.4
-/

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-! ### Four-Variable Identity (2.34) -/

/-- The four-variable Jordan identity (Hanche-Olsen 2.34).
Derived by applying the linearized Jordan identity (2.33) to element d. -/
theorem four_variable_identity (a b c d : J) :
    jmul a (jmul (jmul b c) d) + jmul b (jmul (jmul c a) d) + jmul c (jmul (jmul a b) d) =
    jmul (jmul b c) (jmul a d) + jmul (jmul c a) (jmul b d) + jmul (jmul a b) (jmul c d) := by
  have h := linearized_jordan_operator a b c
  have hd := congrFun (congrArg DFunLike.coe h) d
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.zero_apply,
             opComm_apply, L_apply] at hd
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  have hsum : jmul a (jmul (jmul b c) d) - jmul (jmul b c) (jmul a d) +
              (jmul b (jmul (jmul c a) d) - jmul (jmul c a) (jmul b d)) +
              (jmul c (jmul (jmul a b) d) - jmul (jmul a b) (jmul c d)) = 0 := by
    have : (2 : ℕ) • (jmul a (jmul (jmul b c) d) - jmul (jmul b c) (jmul a d) +
                      (jmul b (jmul (jmul c a) d) - jmul (jmul c a) (jmul b d)) +
                      (jmul c (jmul (jmul a b) d) - jmul (jmul a b) (jmul c d))) = 0 := by
      have heq : (2 : ℕ) • (jmul a (jmul (jmul b c) d) - jmul (jmul b c) (jmul a d) +
                 (jmul b (jmul (jmul c a) d) - jmul (jmul c a) (jmul b d)) +
                 (jmul c (jmul (jmul a b) d) - jmul (jmul a b) (jmul c d))) =
                 jmul a (jmul (jmul b c) d) - jmul (jmul b c) (jmul a d) +
                 (jmul b (jmul (jmul c a) d) - jmul (jmul c a) (jmul b d)) +
                 (jmul c (jmul (jmul a b) d) - jmul (jmul a b) (jmul c d)) +
                 (jmul a (jmul (jmul b c) d) - jmul (jmul b c) (jmul a d) +
                 (jmul b (jmul (jmul c a) d) - jmul (jmul c a) (jmul b d)) +
                 (jmul c (jmul (jmul a b) d) - jmul (jmul a b) (jmul c d))) := by
        simp only [two_nsmul]
      rw [heq]; convert hd using 1; abel
    rwa [two_nsmul, ← two_smul ℝ, smul_eq_zero_iff_right h2] at this
  have hgoal : jmul a (jmul (jmul b c) d) + jmul b (jmul (jmul c a) d) +
               jmul c (jmul (jmul a b) d) -
               (jmul (jmul b c) (jmul a d) + jmul (jmul c a) (jmul b d) +
                jmul (jmul a b) (jmul c d)) = 0 := by
    have : jmul a (jmul (jmul b c) d) + jmul b (jmul (jmul c a) d) +
           jmul c (jmul (jmul a b) d) -
           (jmul (jmul b c) (jmul a d) + jmul (jmul c a) (jmul b d) +
            jmul (jmul a b) (jmul c d)) =
           jmul a (jmul (jmul b c) d) - jmul (jmul b c) (jmul a d) +
           (jmul b (jmul (jmul c a) d) - jmul (jmul c a) (jmul b d)) +
           (jmul c (jmul (jmul a b) d) - jmul (jmul a b) (jmul c d)) := by abel
    rw [this, hsum]
  exact sub_eq_zero.mp hgoal

/-- Element form of operator_formula (Hanche-Olsen 2.35).
a((bc)d) + b((ca)d) + c((ab)d) = (a(bc))d + b(a(cd)) + c(a(bd)) -/
theorem operator_formula_apply (a b c d : J) :
    jmul a (jmul (jmul b c) d) + jmul b (jmul (jmul c a) d) + jmul c (jmul (jmul a b) d) =
    jmul (jmul a (jmul b c)) d + jmul b (jmul a (jmul c d)) + jmul c (jmul a (jmul b d)) := by
  -- From four_variable_identity:
  -- a((bc)d) + b((ca)d) + c((ab)d) = (bc)(ad) + (ca)(bd) + (ab)(cd)
  have h1 := four_variable_identity a b c d
  -- From four_variable_identity with a↔d:
  -- d((bc)a) + b((cd)a) + c((db)a) = (bc)(da) + (cd)(ba) + (db)(ca)
  have h2 := four_variable_identity d b c a
  -- The RHS values are equal by commutativity
  have heq : jmul (jmul b c) (jmul d a) + jmul (jmul c d) (jmul b a) +
             jmul (jmul d b) (jmul c a) =
             jmul (jmul b c) (jmul a d) + jmul (jmul c a) (jmul b d) +
             jmul (jmul a b) (jmul c d) := by
    -- Apply commutativity: da→ad, db→bd, cd→dc, ba→ab, ca→ac
    conv_lhs =>
      rw [jmul_comm d a]  -- (bc)(da) → (bc)(ad)
      rw [jmul_comm c d]  -- (cd)(ba) → (dc)(ba)
      rw [jmul_comm b a]  -- (dc)(ba) → (dc)(ab)
      rw [jmul_comm d b]  -- (db)(ca) → (bd)(ca)
      rw [jmul_comm c a]  -- (bd)(ca) → (bd)(ac)
    -- Now have: (bc)(ad) + (dc)(ab) + (bd)(ac)
    -- Need: (bc)(ad) + (ca)(bd) + (ab)(cd)
    -- Use jmul_comm on outer products
    conv_lhs =>
      rw [jmul_comm (jmul d c) (jmul a b)]  -- (dc)(ab) → (ab)(dc)
      rw [jmul_comm d c]  -- (ab)(dc) → (ab)(cd)
      rw [jmul_comm (jmul b d) (jmul a c)]  -- (bd)(ac) → (ac)(bd)
      rw [jmul_comm a c]  -- (ac)(bd) → (ca)(bd)
    -- Now have: (bc)(ad) + (ab)(cd) + (ca)(bd) = goal (reordered)
    abel
  -- So LHS of h2 = LHS of h1
  have h3 : jmul d (jmul (jmul b c) a) + jmul b (jmul (jmul c d) a) +
            jmul c (jmul (jmul d b) a) =
            jmul a (jmul (jmul b c) d) + jmul b (jmul (jmul c a) d) +
            jmul c (jmul (jmul a b) d) := by
    rw [h2, heq, ← h1]
  -- Now use commutativity to transform LHS of h3 to the RHS we want
  calc jmul a (jmul (jmul b c) d) + jmul b (jmul (jmul c a) d) + jmul c (jmul (jmul a b) d)
      = jmul d (jmul (jmul b c) a) + jmul b (jmul (jmul c d) a) +
        jmul c (jmul (jmul d b) a) := h3.symm
    _ = jmul d (jmul a (jmul b c)) + jmul b (jmul a (jmul c d)) +
        jmul c (jmul a (jmul b d)) := by
          rw [jmul_comm (jmul b c) a]  -- (bc)a → a(bc)
          rw [jmul_comm (jmul c d) a]  -- (cd)a → a(cd)
          rw [jmul_comm (jmul d b) a, jmul_comm d b]  -- (db)a → (bd)a → a(bd)
    _ = jmul (jmul a (jmul b c)) d + jmul b (jmul a (jmul c d)) +
        jmul c (jmul a (jmul b d)) := by
          rw [jmul_comm d (jmul a (jmul b c))]

/-- The operator formula (Hanche-Olsen 2.35).
T_a T_{b∘c} + T_b T_{c∘a} + T_c T_{a∘b} = T_{a∘(b∘c)} + T_b T_a T_c + T_c T_a T_b -/
theorem operator_formula (a b c : J) :
    L a ∘ₗ L (jmul b c) + L b ∘ₗ L (jmul c a) + L c ∘ₗ L (jmul a b) =
    L (jmul a (jmul b c)) + L b ∘ₗ L a ∘ₗ L c + L c ∘ₗ L a ∘ₗ L b := by
  ext d
  simp only [LinearMap.add_apply, LinearMap.comp_apply, L_apply]
  exact operator_formula_apply a b c d

/-! ### Power Associativity -/

/-- The operators T_a and T_{a²} commute (identity 2.4.1). -/
theorem L_L_jsq_comm (a : J) : Commute (L a) (L (jsq a)) := by
  rw [Commute, SemiconjBy]
  ext x
  change L a (L (jsq a) x) = L (jsq a) (L a x)
  simp only [L_apply]
  calc jmul a (jmul (jsq a) x)
      = jmul a (jmul x (jsq a)) := by rw [jmul_comm (jsq a) x]
    _ = jmul (jmul a x) (jsq a) := (jordan_identity a x).symm
    _ = jmul (jsq a) (jmul a x) := jmul_comm _ _

end JordanAlgebra
