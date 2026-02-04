/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Quadratic
import AfTests.Jordan.OperatorIdentities
import AfTests.Jordan.LinearizedJordan

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

/-- H-O 2.4.20, identity (2.43):
`{a,b,c} ∘ d = {a, b∘c, d} - {a∘c, b, d} + {c, a∘b, d}`.
Proved from one instance of `four_variable_identity`. -/
theorem triple_product_243 (a b c d : J) :
    jmul (triple a b c) d =
    triple a (jmul b c) d - triple (jmul a c) b d + triple c (jmul a b) d := by
  simp only [triple_def, add_jmul, sub_jmul]
  have h1 := four_variable_identity a b c d
  rw [jmul_comm c a] at h1
  rw [jmul_comm (jmul a c) b, jmul_comm c (jmul a b)]
  have e1 := sub_eq_zero.mpr h1
  apply sub_eq_zero.mp
  calc _
      = -(jmul a (jmul (jmul b c) d) + jmul b (jmul (jmul a c) d) + jmul c (jmul (jmul a b) d) -
          (jmul (jmul b c) (jmul a d) + jmul (jmul a c) (jmul b d) + jmul (jmul a b) (jmul c d)))
          := by abel
    _ = 0 := by rw [e1, neg_zero]

/-- H-O 2.4.20, identity (2.44):
`{a,b,c} ∘ d + {d,b,c} ∘ a = {a, b∘c, d} + {a∘d, b, c}`.
Derived from (2.43) for the first term and (2.42) for the second. -/
theorem triple_product_244 (a b c d : J) :
    jmul (triple a b c) d + jmul (triple d b c) a =
    triple a (jmul b c) d + triple (jmul a d) b c := by
  rw [triple_product_243 a b c d, triple_product_242 d b c a]
  rw [jmul_comm d a, jmul_comm c a, jmul_comm b a]
  rw [triple_comm_outer d b (jmul a c), triple_comm_outer d (jmul a b) c]
  abel

/-! ### Power Formulas (H-O 2.4.21) -/

/-- Element-level consequence of `L_jpow_comm_all`:
`L_{a^l}(L_{a^m}(x)) = L_{a^m}(L_{a^l}(x))`. -/
private theorem jpow_jmul_comm (a : J) (l m : ℕ) (x : J) :
    jmul (jpow a l) (jmul (jpow a m) x) = jmul (jpow a m) (jmul (jpow a l) x) := by
  have h := L_jpow_comm_all a l m
  rw [Commute, SemiconjBy] at h
  have hx := congr_fun (congr_arg DFunLike.coe h) x
  simp only [L_apply] at hx
  exact hx

/-- H-O 2.4.21, equation (2.45): power formula for the bilinearized U operator.
`2·T_{a^l} U_{a^m, a^n}(x) = U_{a^{m+l}, a^n}(x) + U_{a^m, a^{n+l}}(x)`.
Here `U_{a^m, a^n}(x) = {a^m, x, a^n}` (triple product with x in the middle). -/
theorem power_formula_245 (a x : J) (l m n : ℕ) :
    2 • jmul (jpow a l) (triple (jpow a m) x (jpow a n)) =
    triple (jpow a (m + l)) x (jpow a n) + triple (jpow a m) x (jpow a (n + l)) := by
  -- From triple_product_242 with a^m, x, a^n, a^l:
  have h := triple_product_242 (jpow a m) x (jpow a n) (jpow a l)
  -- Simplify: jmul (jpow a m) (jpow a l) = jpow a (m+l), etc.
  rw [jpow_add a m l, jpow_add a n l] at h
  -- Orient: jmul_comm to get L_{a^l} on the outside
  rw [jmul_comm (triple (jpow a m) x (jpow a n)) (jpow a l)] at h
  rw [jmul_comm x (jpow a l)] at h
  -- L_{a^l} commutes with the bilinearized operator U_{a^m, a^n}
  have hcomm : jmul (jpow a l) (triple (jpow a m) x (jpow a n)) =
      triple (jpow a m) (jmul (jpow a l) x) (jpow a n) := by
    simp only [triple_def, jmul_add, jmul_sub]
    have t1 : jmul (jpow a l) (jmul (jmul (jpow a m) x) (jpow a n)) =
        jmul (jmul (jpow a m) (jmul (jpow a l) x)) (jpow a n) := by
      rw [jmul_comm (jmul (jpow a m) x) (jpow a n),
          jpow_jmul_comm a l n (jmul (jpow a m) x),
          jpow_jmul_comm a l m x,
          jmul_comm (jpow a n) (jmul (jpow a m) (jmul (jpow a l) x))]
    have t2 : jmul (jpow a l) (jmul (jpow a m) (jmul x (jpow a n))) =
        jmul (jpow a m) (jmul (jmul (jpow a l) x) (jpow a n)) := by
      rw [jpow_jmul_comm a l m (jmul x (jpow a n)),
          jmul_comm x (jpow a n),
          jpow_jmul_comm a l n x,
          jmul_comm (jpow a n) (jmul (jpow a l) x)]
    have t3 : jmul (jpow a l) (jmul x (jmul (jpow a m) (jpow a n))) =
        jmul (jmul (jpow a l) x) (jmul (jpow a m) (jpow a n)) := by
      rw [jpow_add a m n,
          jmul_comm x (jpow a (m + n)),
          jpow_jmul_comm a l (m + n) x,
          jmul_comm (jpow a (m + n)) (jmul (jpow a l) x)]
    rw [t1, t2, t3]
  -- h: A = B + C - D, hcomm: A = D, want: 2 • A = B + C
  rw [hcomm] at h
  rw [hcomm, two_smul]
  calc _ = (triple (jpow a (m + l)) x (jpow a n) + triple (jpow a m) x (jpow a (n + l)) -
      triple (jpow a m) (jmul (jpow a l) x) (jpow a n)) +
      triple (jpow a m) (jmul (jpow a l) x) (jpow a n) := by rw [← h]
    _ = _ := by abel

/-- H-O 2.4.21, equation (2.46): U_{a^{n+1}}(x) = U_a(U_{a^n}(x)).
Proved using (2.45) three times with 2-cancellation. -/
theorem U_jpow_succ (a x : J) (n : ℕ) :
    U (jpow a (n + 1)) x = U a (U (jpow a n) x) := by
  have cancel := smul_right_injective J (two_ne_zero (α := ℝ))
  -- Helper: convert nsmul cancellation to ℝ-smul cancellation
  have cancel2 : ∀ a b : J, (2 : ℕ) • a = b + b → a = b := by
    intro a b h; exact cancel (show (2 : ℝ) • a = (2 : ℝ) • b by
      rw [two_smul, two_smul, ← two_nsmul]; exact h)
  -- Step 1: (2.45)[l=1,m=n,n'=n] → jmul a (U_{a^n} x) = {a^n, x, a^{n+1}}
  have step1 : jmul a (U (jpow a n) x) =
      triple (jpow a n) x (jpow a (n + 1)) := by
    have h := power_formula_245 a x 1 n n
    rw [jpow_one, triple_self_right,
        triple_comm_outer (jpow a (n + 1)) x (jpow a n)] at h
    exact cancel2 _ _ h
  -- Step 3: (2.45)[l=2,m=n,n'=n] → jmul (jsq a) (U_{a^n} x) = {a^n, x, a^{n+2}}
  have step3 : jmul (jsq a) (U (jpow a n) x) =
      triple (jpow a n) x (jpow a (n + 2)) := by
    have h := power_formula_245 a x 2 n n
    rw [jpow_two, triple_self_right,
        triple_comm_outer (jpow a (n + 2)) x (jpow a n)] at h
    exact cancel2 _ _ h
  -- Step 2: (2.45)[l=1,m=n,n'=n+1], substitute steps 1 & 3
  have step2 := power_formula_245 a x 1 n (n + 1)
  rw [jpow_one, ← step1, triple_self_right, ← step3] at step2
  -- step2: 2 • jmul a (jmul a (U_{a^n} x)) = U_{a^{n+1}} x + jmul (jsq a) (U_{a^n} x)
  have hU : ∀ y : J, 2 • jmul a (jmul a y) = U a y + jmul (jsq a) y := by
    intro y; simp only [U_def]; abel
  rw [hU] at step2
  exact (add_right_cancel step2).symm

/-- H-O 2.4.21: U_{a^n} = (U_a)^n as iterated linear map composition.
Simple induction using `U_jpow_succ`. -/
theorem U_jpow (a : J) (n : ℕ) (x : J) :
    U (jpow a n) x = ((U_linear a) ^ n) x := by
  induction n with
  | zero =>
    rw [jpow_zero, pow_zero]
    exact U_one x
  | succ n ih =>
    rw [U_jpow_succ, ih, ← U_linear_apply, pow_succ']
    rfl

/-- H-O 2.4.21: U_{a^n} = (U_a)^n as a linear map equation. -/
theorem U_jpow_linear (a : J) (n : ℕ) :
    U_linear (jpow a n) = (U_linear a) ^ n := by
  ext x
  simp only [U_linear_apply]
  exact U_jpow a n x

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

/-- Powers: U_{a²} = U_a². Sorry-free via `U_jpow`. -/
theorem U_jpow_two (a : J) : ∀ x, U (jpow a 2) x = U a (U a x) := by
  intro x
  rw [U_jpow a 2 x, pow_succ, pow_succ, pow_zero]
  rfl

/-- The fundamental formula as a linear map composition identity. -/
theorem fundamental_formula_linear (a b : J) :
    U_linear (U a b) = U_linear a ∘ₗ U_linear b ∘ₗ U_linear a := by
  ext x
  simp only [LinearMap.comp_apply, U_linear_apply]
  exact fundamental_formula a b x

end JordanAlgebra
