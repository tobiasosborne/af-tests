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
The proof uses strong induction on n, with fundamental_jordan' providing the n=2 case
and operator_formula_apply providing the recursion for n≥3.

Key insight: From operator_formula_apply with b = a, c = a^{n-2}, d = x (for n ≥ 3):
  a^n ∘ x = 2(a ∘ (a^{n-1} ∘ x)) + a^{n-2} ∘ (a² ∘ x) - ...
where the omitted terms involve nested products.

Since L_a commutes with L_{a²} (by L_L_jsq_comm) and with L_{a^{n-1}}, L_{a^{n-2}} (by IH),
applying L_a to both sides gives the same result. -/
theorem L_jpow_comm_L (a : J) (n : ℕ) : Commute (L a) (L (jpow a n)) := by
  -- Prove by strong induction on n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    -- ih : ∀ m < n, Commute (L a) (L (jpow a m))
    match n with
    | 0 =>
      -- n = 0: L_a commutes with L_1 (trivial)
      rw [Commute, SemiconjBy, jpow_zero]
      ext x
      change L a (L jone x) = L jone (L a x)
      simp only [L_apply, jone_jmul]
    | 1 =>
      -- n = 1: L_a commutes with L_a (trivial)
      rw [Commute, SemiconjBy, jpow_one]
    | 2 =>
      -- n = 2: L_a commutes with L_{a²} by L_L_jsq_comm
      have h2 : jpow a 2 = jsq a := by
        calc jpow a 2 = jmul a (jpow a 1) := rfl
          _ = jmul a a := by rw [jpow_one]
          _ = jsq a := rfl
      rw [h2]
      exact L_L_jsq_comm a
    | n + 3 =>
      -- n ≥ 3: Use operator_formula_apply to derive recursion (element-level approach)
      -- We have IH for all k < n+3, in particular for n+1 and n+2
      have ih_nm1 : Commute (L a) (L (jpow a (n + 2))) := ih (n + 2) (by omega)
      have ih_nm2 : Commute (L a) (L (jpow a (n + 1))) := ih (n + 1) (by omega)
      have ih_jsq := L_L_jsq_comm a  -- L_a commutes with L_{a²}
      -- Convert commutativity to element form
      rw [Commute, SemiconjBy] at ih_nm1 ih_nm2 ih_jsq ⊢
      ext x
      change L a (L (jpow a (n + 3)) x) = L (jpow a (n + 3)) (L a x)
      simp only [L_apply]
      -- Goal: jmul a (jmul (jpow a (n+3)) x) = jmul (jpow a (n+3)) (jmul a x)
      -- Use operator_formula_apply with b = a, c = jpow a (n+1), d = x
      have h_op := operator_formula_apply a a (jpow a (n + 1)) x
      -- Simplify jmul terms in h_op
      have h_bc : jmul a (jpow a (n + 1)) = jpow a (n + 2) := jpow_succ a (n + 1)
      have h_ca : jmul (jpow a (n + 1)) a = jpow a (n + 2) := by
        rw [jmul_comm]; exact jpow_succ a (n + 1)
      have h_ab : jmul a a = jsq a := rfl
      simp only [h_bc, h_ca, h_ab] at h_op
      -- h_op : jmul a (jmul (jpow a (n+2)) x) + jmul a (jmul (jpow a (n+2)) x) +
      --        jmul (jpow a (n+1)) (jmul (jsq a) x) =
      --        jmul (jmul a (jpow a (n+2))) x + jmul a (jmul a (jmul (jpow a (n+1)) x)) +
      --        jmul (jpow a (n+1)) (jmul a (jmul a x))
      -- Extract element commutativity from operator commutativity
      have hc1 : ∀ y, jmul a (jmul (jpow a (n + 2)) y) = jmul (jpow a (n + 2)) (jmul a y) := by
        intro y
        have heq := congrFun (congrArg DFunLike.coe ih_nm1) y
        -- (L a * L (jpow ...)) y = (L ... * L a) y, where * is composition
        exact heq
      have hc2 : ∀ y, jmul a (jmul (jpow a (n + 1)) y) = jmul (jpow a (n + 1)) (jmul a y) := by
        intro y
        exact congrFun (congrArg DFunLike.coe ih_nm2) y
      have hc3 : ∀ y, jmul a (jmul (jsq a) y) = jmul (jsq a) (jmul a y) := by
        intro y
        exact congrFun (congrArg DFunLike.coe ih_jsq) y
      -- Apply jmul a to both sides of h_op and use commutativity to simplify
      have h_op' := operator_formula_apply a a (jpow a (n + 1)) (jmul a x)
      simp only [h_bc, h_ca, h_ab] at h_op'
      -- Rewrite using jpow a (n+3) = jmul a (jpow a (n+2))
      have h_n3 : jmul a (jpow a (n + 2)) = jpow a (n + 3) := jpow_succ a (n + 2)
      rw [h_n3] at h_op h_op'
      -- h_op: 2·(a ∘ (a^{n+2} ∘ x)) + (a^{n+1} ∘ (a² ∘ x)) =
      --       (a^{n+3} ∘ x) + (a ∘ (a ∘ (a^{n+1} ∘ x))) + (a^{n+1} ∘ (a ∘ (a ∘ x)))
      -- Rearrange to get: (a^{n+3} ∘ x) = 2·(...) + (...) - (...) - (...)
      have expr_x : jmul (jpow a (n + 3)) x =
          jmul a (jmul (jpow a (n + 2)) x) + jmul a (jmul (jpow a (n + 2)) x) +
          jmul (jpow a (n + 1)) (jmul (jsq a) x) -
          jmul a (jmul a (jmul (jpow a (n + 1)) x)) -
          jmul (jpow a (n + 1)) (jmul a (jmul a x)) := by
        -- From h_op we derive this by additive rearrangement
        have heq := h_op
        -- heq: LHS = RHS, where RHS = jpow + ... + ...
        -- Rearrange: jpow = LHS - ... - ...
        calc jmul (jpow a (n + 3)) x
            = jmul (jpow a (n + 3)) x + jmul a (jmul a (jmul (jpow a (n + 1)) x)) +
              jmul (jpow a (n + 1)) (jmul a (jmul a x)) -
              jmul a (jmul a (jmul (jpow a (n + 1)) x)) -
              jmul (jpow a (n + 1)) (jmul a (jmul a x)) := by abel
          _ = jmul a (jmul (jpow a (n + 2)) x) + jmul a (jmul (jpow a (n + 2)) x) +
              jmul (jpow a (n + 1)) (jmul (jsq a) x) -
              jmul a (jmul a (jmul (jpow a (n + 1)) x)) -
              jmul (jpow a (n + 1)) (jmul a (jmul a x)) := by rw [heq]
      have expr_ax : jmul (jpow a (n + 3)) (jmul a x) =
          jmul a (jmul (jpow a (n + 2)) (jmul a x)) + jmul a (jmul (jpow a (n + 2)) (jmul a x)) +
          jmul (jpow a (n + 1)) (jmul (jsq a) (jmul a x)) -
          jmul a (jmul a (jmul (jpow a (n + 1)) (jmul a x))) -
          jmul (jpow a (n + 1)) (jmul a (jmul a (jmul a x))) := by
        have heq := h_op'
        calc jmul (jpow a (n + 3)) (jmul a x)
            = jmul (jpow a (n + 3)) (jmul a x) + jmul a (jmul a (jmul (jpow a (n + 1)) (jmul a x))) +
              jmul (jpow a (n + 1)) (jmul a (jmul a (jmul a x))) -
              jmul a (jmul a (jmul (jpow a (n + 1)) (jmul a x))) -
              jmul (jpow a (n + 1)) (jmul a (jmul a (jmul a x))) := by abel
          _ = jmul a (jmul (jpow a (n + 2)) (jmul a x)) + jmul a (jmul (jpow a (n + 2)) (jmul a x)) +
              jmul (jpow a (n + 1)) (jmul (jsq a) (jmul a x)) -
              jmul a (jmul a (jmul (jpow a (n + 1)) (jmul a x))) -
              jmul (jpow a (n + 1)) (jmul a (jmul a (jmul a x))) := by rw [heq]
      -- Apply a to both sides of expr_x and use commutativity
      calc jmul a (jmul (jpow a (n + 3)) x)
          = jmul a (jmul a (jmul (jpow a (n + 2)) x) + jmul a (jmul (jpow a (n + 2)) x) +
                    jmul (jpow a (n + 1)) (jmul (jsq a) x) -
                    jmul a (jmul a (jmul (jpow a (n + 1)) x)) -
                    jmul (jpow a (n + 1)) (jmul a (jmul a x))) := by rw [expr_x]
        _ = jmul a (jmul a (jmul (jpow a (n + 2)) x)) + jmul a (jmul a (jmul (jpow a (n + 2)) x)) +
            jmul a (jmul (jpow a (n + 1)) (jmul (jsq a) x)) -
            jmul a (jmul a (jmul a (jmul (jpow a (n + 1)) x))) -
            jmul a (jmul (jpow a (n + 1)) (jmul a (jmul a x))) := by
          simp only [jmul_sub, jmul_add]
        _ = jmul a (jmul (jpow a (n + 2)) (jmul a x)) + jmul a (jmul (jpow a (n + 2)) (jmul a x)) +
            jmul (jpow a (n + 1)) (jmul (jsq a) (jmul a x)) -
            jmul a (jmul a (jmul (jpow a (n + 1)) (jmul a x))) -
            jmul (jpow a (n + 1)) (jmul a (jmul a (jmul a x))) := by
          -- Use commutativity hypotheses term by term
          -- Term 1&2: a ∘ (a ∘ (a^{n+2} ∘ x)) = a ∘ (a^{n+2} ∘ (a ∘ x)) by hc1
          have t1 : jmul a (jmul a (jmul (jpow a (n + 2)) x)) =
                    jmul a (jmul (jpow a (n + 2)) (jmul a x)) := by
            congr 1; exact hc1 x
          -- Term 3: a ∘ (a^{n+1} ∘ (a² ∘ x)) = a^{n+1} ∘ (a² ∘ (a ∘ x))
          have t3 : jmul a (jmul (jpow a (n + 1)) (jmul (jsq a) x)) =
                    jmul (jpow a (n + 1)) (jmul (jsq a) (jmul a x)) := by
            rw [hc2 (jmul (jsq a) x)]
            congr 1
            exact hc3 x
          -- Term 4: a ∘ (a ∘ (a ∘ (a^{n+1} ∘ x))) = a ∘ (a ∘ (a^{n+1} ∘ (a ∘ x)))
          have t4 : jmul a (jmul a (jmul a (jmul (jpow a (n + 1)) x))) =
                    jmul a (jmul a (jmul (jpow a (n + 1)) (jmul a x))) := by
            congr 2; exact hc2 x
          -- Term 5: a ∘ (a^{n+1} ∘ (a ∘ (a ∘ x))) = a^{n+1} ∘ (a ∘ (a ∘ (a ∘ x)))
          have t5 : jmul a (jmul (jpow a (n + 1)) (jmul a (jmul a x))) =
                    jmul (jpow a (n + 1)) (jmul a (jmul a (jmul a x))) := by
            exact hc2 (jmul a (jmul a x))
          rw [t1, t3, t4, t5]
        _ = jmul (jpow a (n + 3)) (jmul a x) := by rw [← expr_ax]

/-- All power L-operators mutually commute (H-O 2.4.5(ii)).
Commute (L (a^l)) (L (a^m)) for all l, m. Proof by strong induction on l. -/
theorem L_jpow_comm_all (a : J) (l m : ℕ) :
    Commute (L (jpow a l)) (L (jpow a m)) := by
  revert m
  induction l using Nat.strongRecOn with
  | _ l ih =>
    intro m
    match l with
    | 0 =>
      rw [Commute, SemiconjBy, jpow_zero]
      ext x; change L jone (L (jpow a m) x) = L (jpow a m) (L jone x)
      simp only [L_apply, jone_jmul]
    | 1 =>
      rw [jpow_one]
      exact L_jpow_comm_L a m
    | 2 =>
      rw [show jpow a 2 = jsq a from jpow_two a]
      -- Commute (L (a²)) (L (a^m)) by strong induction on m
      induction m using Nat.strongRecOn with
      | _ m ihm =>
        match m with
        | 0 =>
          rw [Commute, SemiconjBy, jpow_zero]
          ext x; change L (jsq a) (L jone x) = L jone (L (jsq a) x)
          simp only [L_apply, jone_jmul]
        | 1 =>
          rw [jpow_one]; exact (L_L_jsq_comm a).symm
        | (k + 2) =>
          -- Commute (L (a²)) (L (a^{k+2})) via operator_formula recursion
          have ihm_k1 : Commute (L (jsq a)) (L (jpow a (k + 1))) :=
            ihm (k + 1) (by omega)
          have ihm_k : Commute (L (jsq a)) (L (jpow a k)) :=
            ihm k (by omega)
          have ihm_a : Commute (L (jsq a)) (L a) := (L_L_jsq_comm a).symm
          rw [Commute, SemiconjBy] at ihm_k1 ihm_k ihm_a ⊢
          ext x
          change L (jsq a) (L (jpow a (k + 2)) x) = L (jpow a (k + 2)) (L (jsq a) x)
          simp only [L_apply]
          -- Element-level commutativity
          have hc1 : ∀ y, jmul (jsq a) (jmul (jpow a (k + 1)) y) =
              jmul (jpow a (k + 1)) (jmul (jsq a) y) := fun y =>
            congrFun (congrArg DFunLike.coe ihm_k1) y
          have hc2 : ∀ y, jmul (jsq a) (jmul (jpow a k) y) =
              jmul (jpow a k) (jmul (jsq a) y) := fun y =>
            congrFun (congrArg DFunLike.coe ihm_k) y
          have hc3 : ∀ y, jmul (jsq a) (jmul a y) = jmul a (jmul (jsq a) y) := fun y =>
            congrFun (congrArg DFunLike.coe ihm_a) y
          -- Operator formula: express a^{k+2} via recursion
          have h_op := operator_formula_apply a a (jpow a k) x
          have h_bc : jmul a (jpow a k) = jpow a (k + 1) := jpow_succ a k
          have h_ca : jmul (jpow a k) a = jpow a (k + 1) := by
            rw [jmul_comm]; exact jpow_succ a k
          have h_ab : jmul a a = jsq a := rfl
          simp only [h_bc, h_ca, h_ab] at h_op
          have h_k2 : jmul a (jpow a (k + 1)) = jpow a (k + 2) := jpow_succ a (k + 1)
          rw [h_k2] at h_op
          have expr_x : jmul (jpow a (k + 2)) x =
              jmul a (jmul (jpow a (k + 1)) x) + jmul a (jmul (jpow a (k + 1)) x) +
              jmul (jpow a k) (jmul (jsq a) x) -
              jmul a (jmul a (jmul (jpow a k) x)) -
              jmul (jpow a k) (jmul a (jmul a x)) := by
            calc jmul (jpow a (k + 2)) x
                = jmul (jpow a (k + 2)) x +
                  jmul a (jmul a (jmul (jpow a k) x)) +
                  jmul (jpow a k) (jmul a (jmul a x)) -
                  jmul a (jmul a (jmul (jpow a k) x)) -
                  jmul (jpow a k) (jmul a (jmul a x)) := by abel
              _ = _ := by rw [h_op]
          have h_op' := operator_formula_apply a a (jpow a k) (jmul (jsq a) x)
          simp only [h_bc, h_ca, h_ab] at h_op'
          rw [h_k2] at h_op'
          have expr_sqx : jmul (jpow a (k + 2)) (jmul (jsq a) x) =
              jmul a (jmul (jpow a (k + 1)) (jmul (jsq a) x)) +
              jmul a (jmul (jpow a (k + 1)) (jmul (jsq a) x)) +
              jmul (jpow a k) (jmul (jsq a) (jmul (jsq a) x)) -
              jmul a (jmul a (jmul (jpow a k) (jmul (jsq a) x))) -
              jmul (jpow a k) (jmul a (jmul a (jmul (jsq a) x))) := by
            calc jmul (jpow a (k + 2)) (jmul (jsq a) x)
                = jmul (jpow a (k + 2)) (jmul (jsq a) x) +
                  jmul a (jmul a (jmul (jpow a k) (jmul (jsq a) x))) +
                  jmul (jpow a k) (jmul a (jmul a (jmul (jsq a) x))) -
                  jmul a (jmul a (jmul (jpow a k) (jmul (jsq a) x))) -
                  jmul (jpow a k) (jmul a (jmul a (jmul (jsq a) x))) := by
                    abel
              _ = _ := by rw [h_op']
          calc jmul (jsq a) (jmul (jpow a (k + 2)) x)
              = jmul (jsq a) (jmul a (jmul (jpow a (k + 1)) x) +
                  jmul a (jmul (jpow a (k + 1)) x) +
                  jmul (jpow a k) (jmul (jsq a) x) -
                  jmul a (jmul a (jmul (jpow a k) x)) -
                  jmul (jpow a k) (jmul a (jmul a x))) := by rw [expr_x]
            _ = jmul (jsq a) (jmul a (jmul (jpow a (k + 1)) x)) +
                jmul (jsq a) (jmul a (jmul (jpow a (k + 1)) x)) +
                jmul (jsq a) (jmul (jpow a k) (jmul (jsq a) x)) -
                jmul (jsq a) (jmul a (jmul a (jmul (jpow a k) x))) -
                jmul (jsq a) (jmul (jpow a k) (jmul a (jmul a x))) := by
              simp only [jmul_sub, jmul_add]
            _ = jmul a (jmul (jpow a (k + 1)) (jmul (jsq a) x)) +
                jmul a (jmul (jpow a (k + 1)) (jmul (jsq a) x)) +
                jmul (jpow a k) (jmul (jsq a) (jmul (jsq a) x)) -
                jmul a (jmul a (jmul (jpow a k) (jmul (jsq a) x))) -
                jmul (jpow a k) (jmul a (jmul a (jmul (jsq a) x))) := by
              have t1 : jmul (jsq a) (jmul a (jmul (jpow a (k + 1)) x)) =
                  jmul a (jmul (jpow a (k + 1)) (jmul (jsq a) x)) := by
                rw [hc3 (jmul (jpow a (k + 1)) x), hc1 x]
              have t3 : jmul (jsq a) (jmul (jpow a k) (jmul (jsq a) x)) =
                  jmul (jpow a k) (jmul (jsq a) (jmul (jsq a) x)) :=
                hc2 (jmul (jsq a) x)
              have t4 : jmul (jsq a) (jmul a (jmul a (jmul (jpow a k) x))) =
                  jmul a (jmul a (jmul (jpow a k) (jmul (jsq a) x))) := by
                rw [hc3 (jmul a (jmul (jpow a k) x)), hc3 (jmul (jpow a k) x),
                    hc2 x]
              have t5 : jmul (jsq a) (jmul (jpow a k) (jmul a (jmul a x))) =
                  jmul (jpow a k) (jmul a (jmul a (jmul (jsq a) x))) := by
                rw [hc2 (jmul a (jmul a x)), hc3 (jmul a x), hc3 x]
              rw [t1, t3, t4, t5]
            _ = jmul (jpow a (k + 2)) (jmul (jsq a) x) := by rw [← expr_sqx]
    | (n + 3) =>
      -- Use operator_formula recursion: L(a^{n+3}) expressed via L_a, L(a^{n+2}), L(a^{n+1}), L(a²)
      -- All commute with L(a^m) by IH
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

/-- Powers of a single element form an associative algebra.
This is the key consequence of jpow_add (H-O 2.4.4) and proves H-O 2.5.5:
the subalgebra generated by a single element is associative.

Note: This is associativity for products of POWERS, not arbitrary elements.
The full Peirce 1-space is NOT associative in general. -/
theorem jpow_assoc (a : J) (m n p : ℕ) :
    jmul (jmul (jpow a m) (jpow a n)) (jpow a p) =
    jmul (jpow a m) (jmul (jpow a n) (jpow a p)) := by
  rw [jpow_add, jpow_add, jpow_add, jpow_add]
  ring_nf

end JordanAlgebra
