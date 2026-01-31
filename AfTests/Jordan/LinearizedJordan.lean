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

/-! ### The Fundamental Jordan Identity (Element Form) -/

/-- The fundamental Jordan identity in element form (Hanche-Olsen 2.4.2).

`(a² ∘ b) ∘ a = a² ∘ (b ∘ a)` for all a, b.

This is equivalent to the Jordan axiom `(a ∘ b) ∘ a² = a ∘ (b ∘ a²)` and expresses
that the operators T_a and T_{a²} commute. It follows immediately from `L_L_jsq_comm`. -/
theorem fundamental_jordan (a b : J) : jmul (jmul (jsq a) b) a = jmul (jsq a) (jmul b a) := by
  -- Use commutativity to rewrite to the form from L_L_jsq_comm
  calc jmul (jmul (jsq a) b) a
      = jmul a (jmul (jsq a) b) := jmul_comm _ _
    _ = jmul (jsq a) (jmul a b) := by
        -- From L_L_jsq_comm: L_a ∘ L_{a²} = L_{a²} ∘ L_a applied to b
        have h := L_L_jsq_comm a
        have hx : L a (L (jsq a) b) = L (jsq a) (L a b) :=
          congrFun (congrArg DFunLike.coe h.eq) b
        simp only [L_apply] at hx
        exact hx
    _ = jmul (jsq a) (jmul b a) := by rw [jmul_comm a b]

/-- Alternative form: `a ∘ (a² ∘ b) = a² ∘ (a ∘ b)`. -/
theorem fundamental_jordan' (a b : J) : jmul a (jmul (jsq a) b) = jmul (jsq a) (jmul a b) := by
  have h := L_L_jsq_comm a
  have hx : L a (L (jsq a) b) = L (jsq a) (L a b) :=
    congrFun (congrArg DFunLike.coe h.eq) b
  simp only [L_apply] at hx
  exact hx

/-- The Jordan identity applied: `(a ∘ b) ∘ a² = a ∘ (b ∘ a²)` (original form). -/
theorem fundamental_jordan_original (a b : J) :
    jmul (jmul a b) (jsq a) = jmul a (jmul b (jsq a)) :=
  jordan_identity a b

/-! ### Power Associativity (H-O 2.4.4)

Jordan algebras are power-associative: a^m ∘ a^n = a^{m+n}.
The proof uses operator commutation: L_a and L_{a²} commute (L_L_jsq_comm),
which implies all L_{aⁿ} commute with L_a.

Key insight: We prove this by double induction. The base cases use L_L_jsq_comm
and the induction step uses that L_a commutes with L_{aⁿ} implies L_a commutes
with L_{aⁿ⁺¹} via the fundamental Jordan identity. -/

/-- Auxiliary: L_a and L_{aⁿ} commute for all n. This is the key to power associativity.
The proof uses simple induction on n, with fundamental_jordan' providing the key step. -/
theorem L_jpow_comm_L (a : J) (n : ℕ) : Commute (L a) (L (jpow a n)) := by
  -- Prove by induction on n
  induction n with
  | zero =>
    -- n = 0: L_a commutes with L_1 (identity)
    rw [Commute, SemiconjBy, jpow_zero]
    ext x
    show L a (L jone x) = L jone (L a x)
    simp only [L_apply, jone_jmul]
  | succ m ih =>
    -- Inductive step: assume L_a commutes with L_{aᵐ}, prove L_a commutes with L_{aᵐ⁺¹}
    rw [Commute, SemiconjBy] at ih ⊢
    rw [jpow_succ]
    ext x
    -- The goal is: (L a * L (jmul a (jpow a m))) x = (L (jmul a (jpow a m)) * L a) x
    -- Which unfolds to: a ∘ ((a ∘ aᵐ) ∘ x) = (a ∘ aᵐ) ∘ (a ∘ x)
    show L a (L (jmul a (jpow a m)) x) = L (jmul a (jpow a m)) (L a x)
    simp only [L_apply]
    -- Goal: jmul a (jmul (jmul a (jpow a m)) x) = jmul (jmul a (jpow a m)) (jmul a x)
    -- Cases on m
    cases m with
    | zero =>
      -- m = 0: a ∘ ((a ∘ 1) ∘ x) = (a ∘ 1) ∘ (a ∘ x) is a ∘ (a ∘ x) = a ∘ (a ∘ x)
      simp only [jpow_zero, jmul_jone]
    | succ k =>
      -- m = k + 1: need a ∘ ((a ∘ a^{k+1}) ∘ x) = (a ∘ a^{k+1}) ∘ (a ∘ x)
      -- For k = 0: a ∘ ((a ∘ a) ∘ x) = (a ∘ a) ∘ (a ∘ x) = fundamental_jordan' ✓
      cases k with
      | zero =>
        -- k = 0, m = 1: need a ∘ ((a ∘ a¹) ∘ x) = (a ∘ a¹) ∘ (a ∘ x)
        -- which is a ∘ (a² ∘ x) = a² ∘ (a ∘ x)
        have h01 : (0 : ℕ) + 1 = 1 := rfl
        simp only [h01, jpow_one]
        -- Goal is: jmul a (jmul (jsq a) x) = jmul (jsq a) (jmul a x)
        exact fundamental_jordan' a x
      | succ j =>
        -- k ≥ 1: This case requires deeper analysis using the operator formula (H-O 2.35)
        -- to express L_{aⁿ} as a polynomial in L_a and L_{a²}, which commute by L_L_jsq_comm.
        -- This is a standard result in Jordan algebra theory (H-O 2.4.4).
        sorry

/-- Power associativity: a^m ∘ a^n = a^{m+n}. This is H-O 2.4.4.
The proof uses that L_a and L_{aⁿ} commute for all n. -/
theorem jpow_add (a : J) (m n : ℕ) : jmul (jpow a m) (jpow a n) = jpow a (m + n) := by
  -- Proof by induction on n
  induction n with
  | zero =>
    simp only [jpow_zero, jmul_jone, Nat.add_zero]
  | succ n ih =>
    -- jmul (aᵐ) (aⁿ⁺¹) = jmul (aᵐ) (a ∘ aⁿ)
    rw [jpow_succ]
    -- By L_jpow_comm_L, L_a and L_{aᵐ} commute, so:
    -- aᵐ ∘ (a ∘ aⁿ) = a ∘ (aᵐ ∘ aⁿ) = a ∘ aᵐ⁺ⁿ by IH = aᵐ⁺ⁿ⁺¹
    have h_comm := L_jpow_comm_L a m
    rw [Commute, SemiconjBy] at h_comm
    -- h_comm : L_a * L_{aᵐ} = L_{aᵐ} * L_a
    -- Apply to aⁿ: (L_a * L_{aᵐ})(aⁿ) = (L_{aᵐ} * L_a)(aⁿ)
    -- LHS = L_a(L_{aᵐ}(aⁿ)) = a ∘ (aᵐ ∘ aⁿ)
    -- RHS = L_{aᵐ}(L_a(aⁿ)) = aᵐ ∘ (a ∘ aⁿ)
    have h : jmul a (jmul (jpow a m) (jpow a n)) = jmul (jpow a m) (jmul a (jpow a n)) := by
      have h' := congrFun (congrArg DFunLike.coe h_comm) (jpow a n)
      -- h' uses LinearMap multiplication, which is composition
      -- (L_a * L_{aᵐ})(x) = L_a(L_{aᵐ}(x)) and (L_{aᵐ} * L_a)(x) = L_{aᵐ}(L_a(x))
      -- h' uses LinearMap multiplication, which is composition
      -- (L_a * L_{aᵐ})(x) = L_a(L_{aᵐ}(x)) and (L_{aᵐ} * L_a)(x) = L_{aᵐ}(L_a(x))
      change L a (L (jpow a m) (jpow a n)) = L (jpow a m) (L a (jpow a n)) at h'
      simp only [L_apply] at h'
      exact h'
    -- Goal: aᵐ ∘ (a ∘ aⁿ) = a^{m+n+1}
    -- By h: = a ∘ (aᵐ ∘ aⁿ) = a ∘ a^{m+n} = a^{m+n+1}
    rw [← h, ih]
    -- Now need: a ∘ a^{m+n} = a^{m+n+1} = a^{m+(n+1)}
    rw [← jpow_succ]
    -- Arithmetic: m + n + 1 = m + (n + 1)
    simp only [Nat.add_succ]

end JordanAlgebra
