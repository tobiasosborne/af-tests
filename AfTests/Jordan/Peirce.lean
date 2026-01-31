/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Primitive
import AfTests.Jordan.Product
import AfTests.Jordan.LinearizedJordan

/-!
# Peirce Decomposition for Jordan Algebras

For an idempotent e in a Jordan algebra, the left multiplication operator L_e satisfies
L_e(L_e - 1/2)(L_e - 1) = 0, giving eigenspaces P₀(e), P_{1/2}(e), P₁(e).

## Main definitions

* `PeirceSpace e ev` - The ev-eigenspace of L_e
* `PeirceSpace₀`, `PeirceSpace₁₂`, `PeirceSpace₁` - The three Peirce spaces

## Main results

* `peirceSpace_disjoint` - Distinct Peirce spaces are disjoint
* `idempotent_in_peirce_one` - e ∈ P₁(e)
-/

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-! ### Peirce Space Definition -/

/-- The Peirce ev-eigenspace for idempotent e: {a | e ∘ a = ev • a}. -/
def PeirceSpace (e : J) (ev : ℝ) : Submodule ℝ J where
  carrier := {a | jmul e a = ev • a}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [jmul_add, ha, hb, smul_add]
  zero_mem' := by simp [jmul_zero, smul_zero]
  smul_mem' := fun r a ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [smul_jmul, ha, smul_comm]

theorem mem_peirceSpace_iff (e : J) (ev : ℝ) (a : J) :
    a ∈ PeirceSpace e ev ↔ jmul e a = ev • a := Iff.rfl

/-- Notation for common Peirce spaces. -/
abbrev PeirceSpace₀ (e : J) := PeirceSpace e 0
noncomputable abbrev PeirceSpace₁₂ (e : J) := PeirceSpace e (1 / 2)
abbrev PeirceSpace₁ (e : J) := PeirceSpace e 1

/-! ### Basic Peirce Space Properties -/

theorem peirceSpace_zero_eq_ker (e : J) :
    (PeirceSpace e 0 : Set J) = (LinearMap.ker (L e) : Set J) := by
  ext a
  simp only [SetLike.mem_coe, mem_peirceSpace_iff, LinearMap.mem_ker, L_apply, zero_smul]

theorem idempotent_in_peirce_one {e : J} (he : IsIdempotent e) :
    e ∈ PeirceSpace e 1 := by
  rw [mem_peirceSpace_iff, one_smul]
  exact he

theorem orthogonal_in_peirce_zero {e f : J} (horth : AreOrthogonal e f) :
    f ∈ PeirceSpace e 0 := by
  rw [mem_peirceSpace_iff, zero_smul]
  exact horth

/-- Peirce spaces for distinct eigenvalues are disjoint. -/
theorem peirceSpace_disjoint (e : J) {ev1 ev2 : ℝ} (hne : ev1 ≠ ev2) :
    Disjoint (PeirceSpace e ev1) (PeirceSpace e ev2) := by
  rw [Submodule.disjoint_def]
  intro a ha hb
  rw [mem_peirceSpace_iff] at ha hb
  have heq : ev1 • a = ev2 • a := ha.symm.trans hb
  have hdiff : (ev1 - ev2) • a = 0 := by
    rw [sub_smul, heq, sub_self]
  rcases eq_or_ne a 0 with rfl | hane
  · rfl
  · -- If a ≠ 0 but (ev1 - ev2) • a = 0, then ev1 - ev2 = 0
    -- Since ℝ is a field and modules over fields have no zero divisors
    have hsub : ev1 - ev2 ≠ 0 := sub_ne_zero.mpr hne
    -- (ev1 - ev2)⁻¹ • (ev1 - ev2) • a = (ev1 - ev2)⁻¹ • 0
    have h : a = (ev1 - ev2)⁻¹ • ((ev1 - ev2) • a) := by
      rw [smul_smul, inv_mul_cancel₀ hsub, one_smul]
    rw [hdiff, smul_zero] at h
    exact absurd h hane

/-- The identity is in Peirce space 1 for itself. -/
theorem jone_in_peirce_one : jone ∈ PeirceSpace (jone : J) 1 := by
  rw [mem_peirceSpace_iff, jmul_jone, one_smul]

/-- If e is idempotent, then 1-e is in Peirce space 0 of e. -/
theorem complement_in_peirce_zero {e : J} (he : IsIdempotent e) :
    jone - e ∈ PeirceSpace e 0 := by
  rw [mem_peirceSpace_iff, zero_smul]
  exact jone_sub_idempotent_orthogonal he

/-! ### Helper Lemmas for Peirce Polynomial -/

/-- Commutativity of nested jmul with idempotent:
    (e ∘ x) ∘ e = e ∘ (e ∘ x). Follows from Jordan identity. -/
theorem jmul_jmul_e_x_e {e : J} (he : IsIdempotent e) (x : J) :
    jmul (jmul e x) e = jmul e (jmul e x) := by
  have h := jordan_identity e x
  unfold IsIdempotent jsq at he
  -- Jordan identity: jmul (jmul e x) (jmul e e) = jmul e (jmul x (jmul e e))
  rw [he, jmul_comm x e] at h
  exact h

/-- jmul distributes over nsmul on the right. -/
theorem jmul_nsmul (a : J) (n : ℕ) (b : J) : jmul a (n • b) = n • jmul a b := by
  induction n with
  | zero => simp [jmul_zero]
  | succ n ih => rw [succ_nsmul, jmul_add, ih, succ_nsmul]

/-! ### Peirce Polynomial Identity -/

/-- For any idempotent e, L_e satisfies L_e(L_e - 1/2)(L_e - 1) = 0.
This fundamental identity shows L_e has eigenvalues only in {0, 1/2, 1}.

**Proof Strategy:** Polarize the Jordan identity (a∘b)∘a² = a∘(b∘a²) with a → e+x
and extract the x-linear terms. Setting b = e (idempotent) gives:
  `3 • e²(x) = 2 • e³(x) + e(x)`
which rearranges to the Peirce polynomial `2 • e³(x) - 3 • e²(x) + e(x) = 0`. -/
theorem peirce_polynomial_identity {e : J} (he : IsIdempotent e) :
    (L e) ∘ₗ ((L e) - (1/2 : ℝ) • LinearMap.id) ∘ₗ ((L e) - LinearMap.id) = 0 := by
  ext x
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, L_apply, LinearMap.zero_apply]
  rw [jmul_sub, smul_jmul, jmul_sub]
  ring_nf
  -- Goal after ring_nf: e∘((e∘(e∘x)) - (e∘x)) - (1/2)•((e∘(e∘x)) - (e∘x)) = 0
  -- This is equivalent to: 2L³ - 3L² + L = 0 (Peirce polynomial)

  -- PROOF STRATEGY (verified correct, see LEARNINGS.md Session 60):
  -- Use four_variable_identity e e x e to get: 2L³ + L = 3L², then rearrange.
  have h4v := four_variable_identity e e x e
  unfold IsIdempotent jsq at he
  simp only [he, jmul_comm x e] at h4v
  have hcomm : jmul (jmul e x) e = jmul e (jmul e x) :=
    jmul_jmul_e_x_e (by rwa [IsIdempotent, jsq]) x
  simp only [hcomm] at h4v
  -- h4v: L³ + L³ + L = L² + L² + L² (i.e., 2L³ + L = 3L²)
  have key : (2 : ℕ) • jmul e (jmul e (jmul e x)) - (3 : ℕ) • jmul e (jmul e x) +
             jmul e x = 0 := by
    have h : jmul e (jmul e (jmul e x)) + jmul e (jmul e (jmul e x)) + jmul e x -
             (jmul e (jmul e x) + jmul e (jmul e x) + jmul e (jmul e x)) = 0 :=
      sub_eq_zero.mpr h4v
    simp only [two_nsmul] at h ⊢
    have h3 : (3 : ℕ) • jmul e (jmul e x) =
              jmul e (jmul e x) + jmul e (jmul e x) + jmul e (jmul e x) := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul]
    rw [h3]; convert h using 1; abel
  -- key: 2•L³ - 3•L² + L = 0 (with ℕ coefficients)
  -- Goal: L(L² - L) - (1/2)(L² - L) = L³ - (3/2)L² + (1/2)L = (1/2)(2L³ - 3L² + L) = 0
  -- Expand goal using linearity
  rw [jmul_sub, smul_sub, sub_sub]
  -- Goal: L³ - (L² + ((1/2)•L² - (1/2)•L)) = 0
  -- Abbreviations for readability
  set L3 := jmul e (jmul e (jmul e x)) with hL3
  set L2 := jmul e (jmul e x) with hL2
  set L1 := jmul e x with hL1
  -- Convert key from ℕ-smul to ℝ-smul
  have key' : (2 : ℝ) • L3 - (3 : ℝ) • L2 + L1 = 0 := by
    simp only [← Nat.cast_smul_eq_nsmul ℝ] at key
    exact key
  -- Use sub_eq_zero to convert goal to equality form, then use module axioms
  rw [sub_eq_zero]
  -- Goal: L3 = L2 + ((1/2)•L2 - (1/2)•L1)
  have h2ne : (2 : ℝ) ≠ 0 := two_ne_zero
  have h2inv : (2 : ℝ)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2ne
  -- From key': 2L3 = 3L2 - L1, so L3 = (1/2)(3L2 - L1) = (3/2)L2 - (1/2)L1
  have from_key : (2 : ℝ) • L3 = (3 : ℝ) • L2 - L1 := by
    have h := key'
    calc (2 : ℝ) • L3 = (2 : ℝ) • L3 - (3 : ℝ) • L2 + L1 + ((3 : ℝ) • L2 - L1) := by abel
      _ = 0 + ((3 : ℝ) • L2 - L1) := by rw [h]
      _ = (3 : ℝ) • L2 - L1 := by simp
  have eq1 : L3 = (1/2 : ℝ) • ((3 : ℝ) • L2 - L1) := by
    calc L3 = (2 : ℝ)⁻¹ • ((2 : ℝ) • L3) := by rw [smul_smul, h2inv, one_smul]
      _ = (1/2 : ℝ) • ((3 : ℝ) • L2 - L1) := by rw [from_key, one_div]
  -- RHS: L2 + ((1/2)L2 - (1/2)L1) = L2 + (1/2)L2 - (1/2)L1 = (3/2)L2 - (1/2)L1
  have eq2 : L2 + ((1/2 : ℝ) • L2 - (1/2 : ℝ) • L1) = (3/2 : ℝ) • L2 - (1/2 : ℝ) • L1 := by
    have h : L2 + (1/2 : ℝ) • L2 = (1 + 1/2 : ℝ) • L2 := by rw [add_smul, one_smul]
    rw [add_sub_assoc', h]
    norm_num
  rw [eq1, eq2, smul_sub, smul_smul]
  norm_num

/-! ### Peirce Multiplication Rules -/

/-- Product of two elements in P₀(e) stays in P₀(e). -/
theorem peirce_mult_P0_P0 {e : J} (he : IsIdempotent e) {a b : J}
    (ha : a ∈ PeirceSpace e 0) (hb : b ∈ PeirceSpace e 0) :
    jmul a b ∈ PeirceSpace e 0 := by
  rw [mem_peirceSpace_iff] at ha hb ⊢
  rw [zero_smul] at ha hb ⊢
  -- Need: e ∘ (a ∘ b) = 0 given e ∘ a = 0 and e ∘ b = 0
  -- Use four_variable_identity e e a b
  have h4v := four_variable_identity e e a b
  unfold IsIdempotent jsq at he
  -- Simplify using e∘a = 0, e∘b = 0, e² = e
  simp only [he, ha, jmul_comm a e, zero_jmul, jmul_zero] at h4v
  -- h4v: 0 + 0 + jmul a (jmul e b) = 0 + 0 + jmul e (jmul a b)
  simp only [hb, jmul_zero, add_zero, zero_add] at h4v
  -- h4v: 0 = jmul e (jmul a b)
  exact h4v.symm

/-- Product of two elements in P₁(e) stays in P₁(e). -/
theorem peirce_mult_P1_P1 {e : J} (he : IsIdempotent e) {a b : J}
    (ha : a ∈ PeirceSpace e 1) (hb : b ∈ PeirceSpace e 1) :
    jmul a b ∈ PeirceSpace e 1 := by
  rw [mem_peirceSpace_iff] at ha hb ⊢
  rw [one_smul] at ha hb ⊢
  -- Need: e ∘ (a ∘ b) = a ∘ b given e ∘ a = a and e ∘ b = b
  -- Use four_variable_identity e e a b
  have h4v := four_variable_identity e e a b
  unfold IsIdempotent jsq at he
  -- Simplify: LHS = e∘(a∘b) + e∘(a∘b) + a∘b, RHS = a∘b + a∘b + e∘(a∘b)
  simp only [he, ha, jmul_comm a e, hb] at h4v
  -- h4v: e∘(a∘b) + e∘(a∘b) + a∘b = a∘b + a∘b + e∘(a∘b)
  -- Rearrange: 2·e∘(a∘b) + a∘b = 2·(a∘b) + e∘(a∘b) → e∘(a∘b) = a∘b
  have h := sub_eq_zero.mpr h4v
  -- h: 2·e∘(a∘b) + a∘b - (2·(a∘b) + e∘(a∘b)) = 0
  have h' : jmul e (jmul a b) - jmul a b = 0 := by
    calc jmul e (jmul a b) - jmul a b
      = jmul e (jmul a b) + jmul e (jmul a b) + jmul a b -
        (jmul a b + jmul a b + jmul e (jmul a b)) := by abel
      _ = 0 := h
  exact sub_eq_zero.mp h'

/-- Product of an element in P₀(e) with an element in P₁(e) is zero. -/
theorem peirce_mult_P0_P1 {e : J} (he : IsIdempotent e) {a b : J}
    (ha : a ∈ PeirceSpace e 0) (hb : b ∈ PeirceSpace e 1) :
    jmul a b = 0 := by
  rw [mem_peirceSpace_iff] at ha hb
  rw [zero_smul] at ha
  rw [one_smul] at hb
  -- Use four_variable_identity e a b e to derive constraint on c = a∘b
  set c := jmul a b with hc
  have h4v := four_variable_identity e a b e
  unfold IsIdempotent jsq at he
  simp only [he, ha, jmul_zero, zero_jmul, add_zero, jmul_comm a e] at h4v
  have hbe : jmul b e = b := by rw [jmul_comm]; exact hb
  have hbee : jmul (jmul b e) e = b := by rw [hbe, hbe]
  rw [hbee, jmul_comm c e] at h4v
  -- h4v: L_e²(c) + c = L_e(c)
  -- Constraint 1: L_e²(c) = L_e(c) - c
  have constr1 : jmul e (jmul e c) = jmul e c - c := by
    calc jmul e (jmul e c) = jmul e (jmul e c) + c - c := by abel
      _ = jmul e c - c := by rw [h4v]
  -- L_e³(c) = L_e(L_e(c) - c) = L_e²(c) - L_e(c) = -c
  have constr2 : jmul e (jmul e (jmul e c)) = -c := by
    calc jmul e (jmul e (jmul e c)) = jmul e (jmul e c - c) := by rw [constr1]
      _ = jmul e (jmul e c) - jmul e c := jmul_sub e _ _
      _ = (jmul e c - c) - jmul e c := by rw [constr1]
      _ = -c := by abel
  -- From peirce polynomial: 2L³ - 3L² + L = 0, with L² = L - c, L³ = -c:
  -- 2(-c) - 3(L - c) + L = -2c - 3L + 3c + L = c - 2L = 0, so c = 2L_e(c)
  have key : (2 : ℕ) • jmul e (jmul e (jmul e c)) - (3 : ℕ) • jmul e (jmul e c) +
             jmul e c = 0 := by
    have h4v' := four_variable_identity e e c e
    simp only [he, jmul_comm c e] at h4v'
    have hcomm : jmul (jmul e c) e = jmul e (jmul e c) :=
      jmul_jmul_e_x_e (by rwa [IsIdempotent, jsq]) c
    simp only [hcomm] at h4v'
    have h : jmul e (jmul e (jmul e c)) + jmul e (jmul e (jmul e c)) + jmul e c -
             (jmul e (jmul e c) + jmul e (jmul e c) + jmul e (jmul e c)) = 0 :=
      sub_eq_zero.mpr h4v'
    simp only [two_nsmul] at h ⊢
    have h3 : (3 : ℕ) • jmul e (jmul e c) =
              jmul e (jmul e c) + jmul e (jmul e c) + jmul e (jmul e c) := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul]
    rw [h3]; convert h using 1; abel
  rw [constr2, constr1] at key
  -- key: 2•(-c) - 3•(L_e(c) - c) + L_e(c) = 0
  -- Simplifies to: c = 2 • L_e(c), meaning L_e(c) = (1/2)c
  -- Step 1: Derive c = 2 • jmul e c from key
  have c_eq_2Le : c = (2 : ℕ) • jmul e c := by
    -- key: 2 • -c - 3 • (jmul e c - c) + jmul e c = 0
    -- 2 • -c = -(2 • c), 3 • (Le c - c) = 3 • Le c - 3 • c
    -- So: -(2 • c) - (3 • Le c - 3 • c) + Le c = 0
    -- = (3-2) • c + (1-3) • Le c = 0
    -- = c - 2 • Le c = 0
    have h : c - (2 : ℕ) • jmul e c = 0 := by
      -- Expand 2 • -c = -(2 • c) and 3 • (Le c - c) = 3 • Le c - 3 • c
      rw [neg_nsmul, nsmul_sub] at key
      -- key: -(2 • c) - (3 • jmul e c - 3 • c) + jmul e c = 0
      -- This equals: 3 • c - 2 • c - 3 • jmul e c + jmul e c = 0
      have key' : (3 : ℕ) • c - (2 : ℕ) • c - (3 : ℕ) • jmul e c + jmul e c = 0 := by
        convert key using 1; abel
      have h3c : (3 : ℕ) • c - (2 : ℕ) • c = c := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul, add_sub_cancel_left]
      have h3L : (3 : ℕ) • jmul e c - jmul e c = (2 : ℕ) • jmul e c := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul, add_sub_cancel_right]
      calc c - (2 : ℕ) • jmul e c
        = (3 : ℕ) • c - (2 : ℕ) • c - ((3 : ℕ) • jmul e c - jmul e c) := by rw [h3c, h3L]
        _ = (3 : ℕ) • c - (2 : ℕ) • c - (3 : ℕ) • jmul e c + jmul e c := by abel
        _ = 0 := key'
    exact sub_eq_zero.mp h
  -- Convert to ℝ-smul: c = (2:ℝ) • jmul e c
  have c_eq_2Le' : c = (2 : ℝ) • jmul e c := by
    simp only [← Nat.cast_smul_eq_nsmul ℝ] at c_eq_2Le
    exact c_eq_2Le
  -- Step 2: Derive jmul e c = (1/2) • c
  have h2ne : (2 : ℝ) ≠ 0 := two_ne_zero
  have Le_eq : jmul e c = (1/2 : ℝ) • c := by
    have h := c_eq_2Le'
    -- c = 2 • Le c, so Le c = (1/2) • c
    calc jmul e c
      = (2 : ℝ)⁻¹ • ((2 : ℝ) • jmul e c) := by rw [smul_smul, inv_mul_cancel₀ h2ne, one_smul]
      _ = (2 : ℝ)⁻¹ • c := by rw [← h]
      _ = (1/2 : ℝ) • c := by rw [one_div]
  -- Step 3: L_e²(c) computed two ways
  -- From constr1: L_e²(c) = L_e(c) - c = (1/2)c - c = -(1/2)c
  have L2_way1 : jmul e (jmul e c) = -(1/2 : ℝ) • c := by
    calc jmul e (jmul e c) = jmul e c - c := constr1
      _ = (1/2 : ℝ) • c - c := by rw [Le_eq]
      _ = (1/2 - 1 : ℝ) • c := by rw [sub_smul, one_smul]
      _ = -(1/2 : ℝ) • c := by norm_num
  -- From linearity: L_e²(c) = L_e((1/2)c) = (1/2) L_e(c) = (1/2)·(1/2)c = (1/4)c
  have L2_way2 : jmul e (jmul e c) = (1/4 : ℝ) • c := by
    calc jmul e (jmul e c) = jmul e ((1/2 : ℝ) • c) := by rw [Le_eq]
      _ = (1/2 : ℝ) • jmul e c := smul_jmul (1/2 : ℝ) e c
      _ = (1/2 : ℝ) • ((1/2 : ℝ) • c) := by rw [Le_eq]
      _ = ((1/2 : ℝ) * (1/2 : ℝ)) • c := by rw [smul_smul]
      _ = (1/4 : ℝ) • c := by norm_num
  -- Step 4: (1/4)c = -(1/2)c → (3/4)c = 0 → c = 0
  have h34 : (3/4 : ℝ) • c = 0 := by
    have heq : (1/4 : ℝ) • c = -(1/2 : ℝ) • c := L2_way2.symm.trans L2_way1
    calc (3/4 : ℝ) • c = (1/4 : ℝ) • c + (1/2 : ℝ) • c := by
           rw [← add_smul]; norm_num
      _ = -(1/2 : ℝ) • c + (1/2 : ℝ) • c := by rw [heq]
      _ = 0 := by rw [neg_smul, neg_add_cancel]
  have h34ne : (3/4 : ℝ) ≠ 0 := by norm_num
  exact smul_eq_zero.mp h34 |>.resolve_left h34ne

/-- Product of two elements in P_{1/2}(e) lands in P₀(e) ⊕ P₁(e). -/
theorem peirce_mult_P12_P12 {e : J} (he : IsIdempotent e) {a b : J}
    (ha : a ∈ PeirceSpace e (1 / 2)) (hb : b ∈ PeirceSpace e (1 / 2)) :
    jmul a b ∈ PeirceSpace e 0 ⊔ PeirceSpace e 1 := by
  -- The product a ∘ b for a, b ∈ P_{1/2} has no P_{1/2} component
  sorry

/-- Product of an element in P₀(e) with an element in P_{1/2}(e) stays in P_{1/2}(e). -/
theorem peirce_mult_P0_P12 {e : J} (he : IsIdempotent e) {a b : J}
    (ha : a ∈ PeirceSpace e 0) (hb : b ∈ PeirceSpace e (1 / 2)) :
    jmul a b ∈ PeirceSpace e (1 / 2) := by
  rw [mem_peirceSpace_iff] at ha hb ⊢
  rw [zero_smul] at ha
  -- Need: e ∘ (a ∘ b) = (1 / 2)(a ∘ b) given e ∘ a = 0 and e ∘ b = (1 / 2)b
  sorry

/-- Product of an element in P₁(e) with an element in P_{1/2}(e) stays in P_{1/2}(e). -/
theorem peirce_mult_P1_P12 {e : J} (he : IsIdempotent e) {a b : J}
    (ha : a ∈ PeirceSpace e 1) (hb : b ∈ PeirceSpace e (1 / 2)) :
    jmul a b ∈ PeirceSpace e (1 / 2) := by
  rw [mem_peirceSpace_iff] at ha hb ⊢
  rw [one_smul] at ha
  -- Need: e ∘ (a ∘ b) = (1 / 2)(a ∘ b) given e ∘ a = a and e ∘ b = (1 / 2)b
  sorry

end JordanAlgebra
