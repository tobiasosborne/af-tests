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
  -- Strategy: Show L_e²(c) = L_e(c), then decompose c = (c - L_e(c)) + L_e(c)
  -- where (c - L_e(c)) ∈ P₀ and L_e(c) ∈ P₁
  rw [mem_peirceSpace_iff] at ha hb
  set c := jmul a b with hc_def
  unfold IsIdempotent jsq at he
  -- Derived eigenvalue properties
  have hae : jmul a e = (1/2 : ℝ) • a := by rw [jmul_comm]; exact ha
  have hbe : jmul b e = (1/2 : ℝ) • b := by rw [jmul_comm]; exact hb
  -- Step 1: Derive L_e²(c) = L_e(c) using four_variable_identity e a b e
  -- The identity gives:
  -- e∘((a∘b)∘e) + a∘((b∘e)∘e) + b∘((e∘a)∘e) = (a∘b)∘e² + (b∘e)∘(a∘e) + (e∘a)∘(b∘e)
  have h4v := four_variable_identity e a b e
  -- Simplify step by step
  -- (e∘a)∘e = (1/2)a ∘ e = (1/2)(a∘e) = (1/4)a
  have heae : jmul (jmul e a) e = (1/4 : ℝ) • a := by
    rw [ha, jmul_smul, hae, smul_smul]; norm_num
  -- (b∘e)∘e = (1/2)b ∘ e = (1/4)b
  have hbee : jmul (jmul b e) e = (1/4 : ℝ) • b := by
    rw [hbe, jmul_smul, hbe, smul_smul]; norm_num
  -- (a∘b)∘e = e∘c (by commutativity)
  have hce : jmul c e = jmul e c := jmul_comm c e
  -- Cross products
  have h_cross1 : jmul (jmul b e) (jmul a e) = (1/4 : ℝ) • c := by
    rw [hbe, hae, jmul_smul, smul_jmul, smul_smul, jmul_comm b a, ← hc_def]
    norm_num
  have h_cross2 : jmul (jmul e a) (jmul b e) = (1/4 : ℝ) • c := by
    rw [ha, hbe, jmul_smul, smul_jmul, smul_smul, ← hc_def]
    norm_num
  -- Rewrite h4v
  rw [he, hbee, heae, hce, h_cross1, h_cross2, smul_jmul, smul_jmul] at h4v
  -- h4v: e∘(e∘c) + (1/4)(a∘b) + (1/4)(b∘a) = e∘c + (1/4)c + (1/4)c
  have hba : jmul b a = c := jmul_comm b a
  rw [hba, ← hc_def] at h4v
  -- h4v: e∘(e∘c) + (1/4)c + (1/4)c = e∘c + (1/4)c + (1/4)c
  have key : jmul e (jmul e c) = jmul e c := by
    have h := sub_eq_zero.mpr h4v
    have h' : jmul e (jmul e c) - jmul e c = 0 := by
      calc jmul e (jmul e c) - jmul e c
        = jmul e (jmul e c) + (1/4 : ℝ) • c + (1/4 : ℝ) • c -
          (jmul e c + (1/4 : ℝ) • c + (1/4 : ℝ) • c) := by abel
        _ = 0 := h
    exact sub_eq_zero.mp h'
  -- Step 2: Decompose c = (c - L_e(c)) + L_e(c)
  rw [Submodule.mem_sup]
  refine ⟨c - jmul e c, ?_, jmul e c, ?_, ?_⟩
  -- (c - L_e(c)) ∈ P₀: L_e(c - L_e(c)) = L_e(c) - L_e²(c) = 0
  · rw [mem_peirceSpace_iff, zero_smul, jmul_sub, key, sub_self]
  -- L_e(c) ∈ P₁: L_e(L_e(c)) = L_e²(c) = L_e(c)
  · rw [mem_peirceSpace_iff, one_smul]; exact key
  -- c = (c - L_e(c)) + L_e(c)
  · abel

/-- Product of an element in P₀(e) with an element in P_{1/2}(e) stays in P_{1/2}(e). -/
theorem peirce_mult_P0_P12 {e : J} (he : IsIdempotent e) {a b : J}
    (ha : a ∈ PeirceSpace e 0) (hb : b ∈ PeirceSpace e (1 / 2)) :
    jmul a b ∈ PeirceSpace e (1 / 2) := by
  rw [mem_peirceSpace_iff] at ha hb ⊢
  rw [zero_smul] at ha
  -- Need: e ∘ (a ∘ b) = (1/2)(a ∘ b) given e ∘ a = 0 and e ∘ b = (1/2)b
  -- Use four_variable_identity a e e b
  have h4v := four_variable_identity a e e b
  unfold IsIdempotent jsq at he
  -- Simplify using e∘a = 0, e² = e, e∘b = (1/2)b
  have hae : jmul a e = 0 := by rw [jmul_comm]; exact ha
  simp only [he, ha, hae, jmul_zero, zero_jmul, add_zero] at h4v
  -- h4v: a ∘ (e ∘ b) = e ∘ (a ∘ b)
  -- LHS = a ∘ ((1/2)b) = (1/2)(a ∘ b)
  rw [hb, smul_jmul] at h4v
  exact h4v.symm

/-- Product of an element in P₁(e) with an element in P_{1/2}(e) stays in P_{1/2}(e). -/
theorem peirce_mult_P1_P12 {e : J} (he : IsIdempotent e) {a b : J}
    (ha : a ∈ PeirceSpace e 1) (hb : b ∈ PeirceSpace e (1 / 2)) :
    jmul a b ∈ PeirceSpace e (1 / 2) := by
  rw [mem_peirceSpace_iff] at ha hb ⊢
  rw [one_smul] at ha
  -- Need: e ∘ (a ∘ b) = (1/2)(a ∘ b) given e ∘ a = a and e ∘ b = (1/2)b
  -- Use four_variable_identity a e e b
  have h4v := four_variable_identity a e e b
  unfold IsIdempotent jsq at he
  have hae : jmul a e = a := by rw [jmul_comm]; exact ha
  simp only [he, ha, hae] at h4v
  -- h4v: a ∘ (e ∘ b) + e ∘ (a ∘ b) + e ∘ (a ∘ b) = e ∘ (a ∘ b) + a ∘ (e ∘ b) + a ∘ (e ∘ b)
  -- Simplify using e ∘ b = (1/2)b
  rw [hb, smul_jmul] at h4v
  -- h4v: (1/2)(a∘b) + e∘(a∘b) + e∘(a∘b) = e∘(a∘b) + (1/2)(a∘b) + (1/2)(a∘b)
  -- Rearrange: 2·e∘(a∘b) = e∘(a∘b) + (1/2)(a∘b), so e∘(a∘b) = (1/2)(a∘b)
  set c := jmul a b with hc
  have h : jmul e c = (1/2 : ℝ) • c := by
    have h' := sub_eq_zero.mpr h4v
    -- h': (1/2)c + 2·Le(c) - (Le(c) + c) = 0, so Le(c) = (1/2)c
    have calc1 : jmul e c - (1/2 : ℝ) • c = 0 := by
      calc jmul e c - (1/2 : ℝ) • c
        = (1/2 : ℝ) • c + jmul e c + jmul e c -
          (jmul e c + (1/2 : ℝ) • c + (1/2 : ℝ) • c) := by abel
        _ = 0 := h'
    exact sub_eq_zero.mp calc1
  exact h

/-! ### Peirce Projection Operators -/

/-- Projection onto P₀(e): π₀ = 2(L_e - 1/2)(L_e - 1) = 2L² - 3L + 1.
    This is the Lagrange interpolation polynomial for eigenvalue 0. -/
def peirceProj₀ (e : J) : J →ₗ[ℝ] J :=
  (2 : ℝ) • (L e ∘ₗ L e) - (3 : ℝ) • L e + LinearMap.id

/-- Projection onto P_{1/2}(e): π_{1/2} = -4L(L - 1) = -4L² + 4L.
    This is the Lagrange interpolation polynomial for eigenvalue 1/2. -/
def peirceProj₁₂ (e : J) : J →ₗ[ℝ] J :=
  -(4 : ℝ) • (L e ∘ₗ L e) + (4 : ℝ) • L e

/-- Projection onto P₁(e): π₁ = 2L(L - 1/2) = 2L² - L.
    This is the Lagrange interpolation polynomial for eigenvalue 1. -/
def peirceProj₁ (e : J) : J →ₗ[ℝ] J :=
  (2 : ℝ) • (L e ∘ₗ L e) - L e

/-- The three Peirce projections sum to the identity. -/
theorem peirceProj_sum (e : J) :
    peirceProj₀ e + peirceProj₁₂ e + peirceProj₁ e = LinearMap.id := by
  ext x
  simp only [LinearMap.add_apply, peirceProj₀, peirceProj₁₂, peirceProj₁,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.id_apply, LinearMap.neg_apply, L_apply]
  -- Goal: (2L² - 3L + 1)x + (-4L² + 4L)x + (2L² - L)x = x
  -- = (2 - 4 + 2)L²x + (-3 + 4 - 1)Lx + x = 0·L²x + 0·Lx + x = x
  -- Use module axioms: coefficients are 0, 0, 1
  have h1 : (2 : ℝ) + (-4) + 2 = 0 := by norm_num
  have h2 : (-3 : ℝ) + 4 + (-1) = 0 := by norm_num
  calc (2 : ℝ) • jmul e (jmul e x) - (3 : ℝ) • jmul e x + x +
       (-(4 : ℝ) • jmul e (jmul e x) + (4 : ℝ) • jmul e x) +
       ((2 : ℝ) • jmul e (jmul e x) - jmul e x)
    = ((2 : ℝ) + (-4) + 2) • jmul e (jmul e x) + ((-3 : ℝ) + 4 + (-1)) • jmul e x + x := by
        rw [neg_smul]; module
    _ = (0 : ℝ) • jmul e (jmul e x) + (0 : ℝ) • jmul e x + x := by rw [h1, h2]
    _ = x := by simp [zero_smul]

/-- π₀ maps into P₀(e). -/
theorem peirceProj₀_mem {e : J} (he : IsIdempotent e) (x : J) :
    peirceProj₀ e x ∈ PeirceSpace e 0 := by
  rw [mem_peirceSpace_iff, zero_smul]
  simp only [peirceProj₀, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply, L_apply]
  -- Need: L_e((2L² - 3L + 1)x) = 0, i.e., 2L³ - 3L² + L = 0
  rw [jmul_add, jmul_sub, smul_jmul, smul_jmul]
  -- Use Peirce polynomial from four_variable_identity
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
  simp only [← Nat.cast_smul_eq_nsmul ℝ] at key
  exact key

/-- π_{1/2} maps into P_{1/2}(e). -/
theorem peirceProj₁₂_mem {e : J} (he : IsIdempotent e) (x : J) :
    peirceProj₁₂ e x ∈ PeirceSpace e (1 / 2) := by
  rw [mem_peirceSpace_iff]
  simp only [peirceProj₁₂, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, L_apply]
  -- Need: L_e((-4L² + 4L)x) = (1/2)·((-4L² + 4L)x)
  -- I.e., -4L³ + 4L² = (1/2)(-4L² + 4L) = -2L² + 2L
  rw [jmul_add, smul_jmul, smul_jmul]
  -- Goal: (-4)•L³x + 4•L²x = (1/2)•((-4)•L²x + 4•Lx)
  have h4v := four_variable_identity e e x e
  unfold IsIdempotent jsq at he
  simp only [he, jmul_comm x e] at h4v
  have hcomm : jmul (jmul e x) e = jmul e (jmul e x) :=
    jmul_jmul_e_x_e (by rwa [IsIdempotent, jsq]) x
  simp only [hcomm] at h4v
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
  simp only [← Nat.cast_smul_eq_nsmul ℝ] at key
  -- From key: 2L³ = 3L² - L, so 4L³ = 6L² - 2L, so -4L³ = -6L² + 2L
  have h2L3 : (2 : ℝ) • jmul e (jmul e (jmul e x)) = (3 : ℝ) • jmul e (jmul e x) - jmul e x := by
    have h' : (2 : ℝ) • jmul e (jmul e (jmul e x)) - (3 : ℝ) • jmul e (jmul e x) + jmul e x = 0 := key
    calc (2 : ℝ) • jmul e (jmul e (jmul e x))
      = (2 : ℝ) • jmul e (jmul e (jmul e x)) - (3 : ℝ) • jmul e (jmul e x) + jmul e x +
        ((3 : ℝ) • jmul e (jmul e x) - jmul e x) := by abel
      _ = 0 + ((3 : ℝ) • jmul e (jmul e x) - jmul e x) := by rw [h']
      _ = (3 : ℝ) • jmul e (jmul e x) - jmul e x := by simp
  have from_key : (-4 : ℝ) • jmul e (jmul e (jmul e x)) = (-6 : ℝ) • jmul e (jmul e x) +
                  (2 : ℝ) • jmul e x := by
    calc (-4 : ℝ) • jmul e (jmul e (jmul e x))
      = (-2 : ℝ) • ((2 : ℝ) • jmul e (jmul e (jmul e x))) := by rw [smul_smul]; norm_num
      _ = (-2 : ℝ) • ((3 : ℝ) • jmul e (jmul e x) - jmul e x) := by rw [h2L3]
      _ = (-6 : ℝ) • jmul e (jmul e x) + (2 : ℝ) • jmul e x := by
          rw [smul_sub, smul_smul]; simp only [neg_mul, neg_neg]; norm_num
  -- Now: -4L³ + 4L² = (-6L² + 2L) + 4L² = -2L² + 2L = (1/2)(-4L² + 4L)
  calc (-4 : ℝ) • jmul e (jmul e (jmul e x)) + (4 : ℝ) • jmul e (jmul e x)
    = ((-6 : ℝ) • jmul e (jmul e x) + (2 : ℝ) • jmul e x) + (4 : ℝ) • jmul e (jmul e x) := by
        rw [from_key]
    _ = (-2 : ℝ) • jmul e (jmul e x) + (2 : ℝ) • jmul e x := by module
    _ = (1/2 : ℝ) • ((-4 : ℝ) • jmul e (jmul e x) + (4 : ℝ) • jmul e x) := by
        simp only [smul_add, smul_smul]; norm_num

/-- π₁ maps into P₁(e). -/
theorem peirceProj₁_mem {e : J} (he : IsIdempotent e) (x : J) :
    peirceProj₁ e x ∈ PeirceSpace e 1 := by
  rw [mem_peirceSpace_iff, one_smul]
  simp only [peirceProj₁, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, L_apply]
  -- Need: L_e((2L² - L)x) = (2L² - L)x
  -- I.e., 2L³ - L² = 2L² - L, i.e., 2L³ - 3L² + L = 0 ✓
  rw [jmul_sub, smul_jmul]
  have h4v := four_variable_identity e e x e
  unfold IsIdempotent jsq at he
  simp only [he, jmul_comm x e] at h4v
  have hcomm : jmul (jmul e x) e = jmul e (jmul e x) :=
    jmul_jmul_e_x_e (by rwa [IsIdempotent, jsq]) x
  simp only [hcomm] at h4v
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
  simp only [← Nat.cast_smul_eq_nsmul ℝ] at key
  -- From key: 2L³ = 3L² - L
  -- Need: 2L³ - L² = 2L² - L
  -- Subst: (3L² - L) - L² = 2L² - L ✓
  have from_key : (2 : ℝ) • jmul e (jmul e (jmul e x)) =
                  (3 : ℝ) • jmul e (jmul e x) - jmul e x := by
    have h' : (2 : ℝ) • jmul e (jmul e (jmul e x)) - (3 : ℝ) • jmul e (jmul e x) + jmul e x = 0 := key
    calc (2 : ℝ) • jmul e (jmul e (jmul e x))
      = (2 : ℝ) • jmul e (jmul e (jmul e x)) - (3 : ℝ) • jmul e (jmul e x) + jmul e x +
        ((3 : ℝ) • jmul e (jmul e x) - jmul e x) := by abel
      _ = 0 + ((3 : ℝ) • jmul e (jmul e x) - jmul e x) := by rw [h']
      _ = (3 : ℝ) • jmul e (jmul e x) - jmul e x := by simp
  calc (2 : ℝ) • jmul e (jmul e (jmul e x)) - jmul e (jmul e x)
    = ((3 : ℝ) • jmul e (jmul e x) - jmul e x) - jmul e (jmul e x) := by rw [from_key]
    _ = (2 : ℝ) • jmul e (jmul e x) - jmul e x := by module

/-! ### Peirce Decomposition Theorem -/

/-- Every element decomposes uniquely into Peirce components. -/
theorem peirce_decomposition {e : J} (he : IsIdempotent e) (a : J) :
    ∃ (a₀ a₁₂ a₁ : J),
      a₀ ∈ PeirceSpace e 0 ∧
      a₁₂ ∈ PeirceSpace e (1/2) ∧
      a₁ ∈ PeirceSpace e 1 ∧
      a = a₀ + a₁₂ + a₁ := by
  refine ⟨peirceProj₀ e a, peirceProj₁₂ e a, peirceProj₁ e a,
          peirceProj₀_mem he a, peirceProj₁₂_mem he a, peirceProj₁_mem he a, ?_⟩
  -- a = π₀(a) + π_{1/2}(a) + π₁(a) follows from peirceProj_sum
  have h := peirceProj_sum e
  calc a = LinearMap.id a := rfl
    _ = (peirceProj₀ e + peirceProj₁₂ e + peirceProj₁ e) a := by rw [← h]
    _ = peirceProj₀ e a + peirceProj₁₂ e a + peirceProj₁ e a := by
        simp only [LinearMap.add_apply]

/-- The supremum of the three Peirce spaces is the whole algebra. -/
theorem peirceSpace_iSup_eq_top {e : J} (he : IsIdempotent e) :
    PeirceSpace e 0 ⊔ PeirceSpace e (1/2) ⊔ PeirceSpace e 1 = ⊤ := by
  rw [eq_top_iff]
  intro a _
  obtain ⟨a₀, a₁₂, a₁, ha₀, ha₁₂, ha₁, hsum⟩ := peirce_decomposition he a
  rw [hsum]
  apply Submodule.add_mem
  apply Submodule.add_mem
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left ha₀)
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right ha₁₂)
  · exact Submodule.mem_sup_right ha₁

/-- The three Peirce spaces form an internal direct sum.
    This captures both uniqueness of decomposition and spanning.

    Note: The independence (iSupIndep) proof requires showing that each Peirce space
    intersects trivially with the sum of the others. This follows from eigenvalue
    distinctness (0, 1/2, 1 are pairwise distinct) combined with `peirceSpace_disjoint`. -/
theorem peirce_direct_sum {e : J} (he : IsIdempotent e) :
    DirectSum.IsInternal ![PeirceSpace e 0, PeirceSpace e (1/2), PeirceSpace e 1] := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · -- Independence: prove iSupIndep
    -- The strategy: show each space has trivial intersection with the sum of others
    -- using that eigenvalues 0, 1/2, 1 are pairwise distinct and L_e is a linear operator
    rw [iSupIndep_def]
    intro i
    -- For Fin 3, we check each case
    fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · -- Case i = 0: show Disjoint P₀ (P_{1/2} ⊔ P₁)
      rw [Submodule.disjoint_def]
      intro x hx0 hxsup
      -- hx0 : x ∈ ![P₀, P_{1/2}, P₁] 0 = x ∈ P₀
      -- x ∈ P₀ means L_e(x) = 0
      have hx0' : jmul e x = 0 := by
        have : x ∈ PeirceSpace e 0 := hx0
        rw [mem_peirceSpace_iff, zero_smul] at this
        exact this
      -- x is in the sup of P_{1/2} and P₁ over j ≠ 0
      -- The sup over j ≠ 0 in Fin 3 is P_{1/2} ⊔ P₁
      have hsup : ⨆ (j : Fin 3) (_ : j ≠ (0 : Fin 3)), (![PeirceSpace e 0, PeirceSpace e (1 / 2),
          PeirceSpace e 1]) j = PeirceSpace e (1/2) ⊔ PeirceSpace e 1 := by
        apply le_antisymm
        · apply iSup_le
          intro j; apply iSup_le; intro hj
          fin_cases j
          · exact absurd rfl hj
          · exact le_sup_left
          · exact le_sup_right
        · apply sup_le
          · calc PeirceSpace e (1/2) = (![PeirceSpace e 0, PeirceSpace e (1/2),
                PeirceSpace e 1]) 1 := rfl
              _ ≤ ⨆ (j : Fin 3) (_ : j ≠ 0), _ := le_biSup _ (by decide : (1 : Fin 3) ≠ 0)
          · calc PeirceSpace e 1 = (![PeirceSpace e 0, PeirceSpace e (1/2),
                PeirceSpace e 1]) 2 := rfl
              _ ≤ ⨆ (j : Fin 3) (_ : j ≠ 0), _ := le_biSup _ (by decide : (2 : Fin 3) ≠ 0)
      simp only [Fin.mk_zero] at hxsup
      rw [hsup, Submodule.mem_sup] at hxsup
      obtain ⟨y, hy, z, hz, hsum⟩ := hxsup
      rw [mem_peirceSpace_iff] at hy hz
      rw [one_smul] at hz
      -- x = y + z with L_e(y) = (1/2)y, L_e(z) = z
      -- Also L_e(x) = 0, so L_e(y + z) = (1/2)y + z = 0
      have h1 : (1/2 : ℝ) • y + z = 0 := by
        calc (1/2 : ℝ) • y + z = jmul e y + jmul e z := by rw [hy, hz]
          _ = jmul e (y + z) := by rw [← jmul_add]
          _ = jmul e x := by rw [hsum]
          _ = 0 := hx0'
      -- Apply L_e again: L_e²(x) = 0, and L_e²(y + z) = (1/4)y + z
      have hLe2_x : jmul e (jmul e x) = 0 := by rw [hx0', jmul_zero]
      have h2 : (1/4 : ℝ) • y + z = 0 := by
        have hLe2_yz : jmul e (jmul e (y + z)) = (1/4 : ℝ) • y + z := by
          calc jmul e (jmul e (y + z)) = jmul e (jmul e y + jmul e z) := by rw [jmul_add]
            _ = jmul e ((1/2 : ℝ) • y + z) := by rw [hy, hz]
            _ = jmul e ((1/2 : ℝ) • y) + jmul e z := by rw [jmul_add]
            _ = (1/2 : ℝ) • jmul e y + jmul e z := by rw [smul_jmul]
            _ = (1/2 : ℝ) • ((1/2 : ℝ) • y) + z := by rw [hy, hz]
            _ = (1/4 : ℝ) • y + z := by rw [smul_smul]; norm_num
        calc (1/4 : ℝ) • y + z = jmul e (jmul e (y + z)) := hLe2_yz.symm
          _ = jmul e (jmul e x) := by rw [hsum]
          _ = 0 := hLe2_x
      -- From h1: (1/2)y + z = 0 and h2: (1/4)y + z = 0
      -- Subtract: (1/4)y = 0, so y = 0
      have hy0 : y = 0 := by
        have hdiff : (1/4 : ℝ) • y = 0 := by
          have : (1/2 : ℝ) • y + z - ((1/4 : ℝ) • y + z) = 0 - 0 := by rw [h1, h2]
          simp only [sub_zero, add_sub_add_right_eq_sub] at this
          have : ((1/2 : ℝ) - (1/4 : ℝ)) • y = 0 := by rw [sub_smul]; exact this
          simp only [show (1/2 : ℝ) - 1/4 = 1/4 by norm_num] at this
          exact this
        have h14 : (1/4 : ℝ) ≠ 0 := by norm_num
        exact (smul_eq_zero_iff_right h14).mp hdiff
      -- Then z = 0 from h1
      have hz0 : z = 0 := by simp only [hy0, smul_zero, zero_add] at h1; exact h1
      -- Therefore x = 0
      rw [← hsum, hy0, hz0, add_zero]
    · -- Case i = 1: show Disjoint P_{1/2} (P₀ ⊔ P₁)
      rw [Submodule.disjoint_def]
      intro x hx12 hxsup
      -- hx12 : x ∈ P_{1/2}, convert to L_e(x) = (1/2)x
      have hx12' : jmul e x = (1/2 : ℝ) • x := by
        have : x ∈ PeirceSpace e (1/2) := hx12
        rw [mem_peirceSpace_iff] at this
        exact this
      have hsup : ⨆ (j : Fin 3) (_ : j ≠ (1 : Fin 3)), (![PeirceSpace e 0, PeirceSpace e (1 / 2),
          PeirceSpace e 1]) j = PeirceSpace e 0 ⊔ PeirceSpace e 1 := by
        apply le_antisymm
        · apply iSup_le; intro j; apply iSup_le; intro hj
          fin_cases j
          · exact le_sup_left
          · exact absurd rfl hj
          · exact le_sup_right
        · apply sup_le
          · calc PeirceSpace e 0 = (![PeirceSpace e 0, PeirceSpace e (1/2),
                PeirceSpace e 1]) 0 := rfl
              _ ≤ ⨆ (j : Fin 3) (_ : j ≠ 1), _ := le_biSup _ (by decide : (0 : Fin 3) ≠ 1)
          · calc PeirceSpace e 1 = (![PeirceSpace e 0, PeirceSpace e (1/2),
                PeirceSpace e 1]) 2 := rfl
              _ ≤ ⨆ (j : Fin 3) (_ : j ≠ 1), _ := le_biSup _ (by decide : (2 : Fin 3) ≠ 1)
      simp only [Fin.mk_one] at hxsup
      rw [hsup, Submodule.mem_sup] at hxsup
      obtain ⟨y, hy, z, hz, hsum⟩ := hxsup
      rw [mem_peirceSpace_iff, zero_smul] at hy
      rw [mem_peirceSpace_iff, one_smul] at hz
      -- x = y + z with L_e(y) = 0, L_e(z) = z
      -- L_e(x) = (1/2)x, so L_e(y + z) = 0 + z = z
      -- But L_e(x) = (1/2)(y + z), so z = (1/2)y + (1/2)z
      have h1 : z = (1/2 : ℝ) • y + (1/2 : ℝ) • z := by
        calc z = 0 + z := by rw [zero_add]
          _ = jmul e y + jmul e z := by rw [hy, hz]
          _ = jmul e (y + z) := by rw [← jmul_add]
          _ = jmul e x := by rw [hsum]
          _ = (1/2 : ℝ) • x := hx12'
          _ = (1/2 : ℝ) • (y + z) := by rw [hsum]
          _ = (1/2 : ℝ) • y + (1/2 : ℝ) • z := by rw [smul_add]
      -- From h1: z - (1/2)z = (1/2)y, so (1/2)z = (1/2)y
      have h2 : (1/2 : ℝ) • z = (1/2 : ℝ) • y := by
        have hsub : z - (1/2 : ℝ) • z = (1/2 : ℝ) • y := by
          calc z - (1/2 : ℝ) • z = (1/2 : ℝ) • y + (1/2 : ℝ) • z - (1/2 : ℝ) • z := by rw [← h1]
            _ = (1/2 : ℝ) • y := by abel
        have hsub' : (1 - 1/2 : ℝ) • z = (1/2 : ℝ) • y := by
          rw [sub_smul, one_smul]; exact hsub
        simp only [show (1 - 1/2 : ℝ) = 1/2 by norm_num] at hsub'
        exact hsub'
      -- So z = y (multiply by 2)
      have hzy : z = y := by
        have h12 : (1/2 : ℝ) ≠ 0 := by norm_num
        exact (smul_right_injective J h12 h2.symm).symm
      -- But z ∈ P₁ and y ∈ P₀, and P₀ ∩ P₁ = {0}
      -- y ∈ P₀ means L_e(y) = 0, z = y so L_e(z) = 0, but also L_e(z) = z
      -- Hence z = 0
      have hz0 : z = 0 := by
        have : jmul e z = 0 := by rw [hzy, hy]
        rw [hz] at this
        exact this
      have hy0 : y = 0 := hzy ▸ hz0
      rw [← hsum, hy0, hz0, add_zero]
    · -- Case i = 2: show Disjoint P₁ (P₀ ⊔ P_{1/2})
      rw [Submodule.disjoint_def]
      intro x hx1 hxsup
      -- hx1 : x ∈ P₁, convert to L_e(x) = x
      have hx1' : jmul e x = x := by
        have : x ∈ PeirceSpace e 1 := hx1
        rw [mem_peirceSpace_iff, one_smul] at this
        exact this
      have hsup : ⨆ (j : Fin 3) (_ : j ≠ (2 : Fin 3)), (![PeirceSpace e 0, PeirceSpace e (1 / 2),
          PeirceSpace e 1]) j = PeirceSpace e 0 ⊔ PeirceSpace e (1/2) := by
        apply le_antisymm
        · apply iSup_le; intro j; apply iSup_le; intro hj
          fin_cases j
          · exact le_sup_left
          · exact le_sup_right
          · exact absurd rfl hj
        · apply sup_le
          · calc PeirceSpace e 0 = (![PeirceSpace e 0, PeirceSpace e (1/2),
                PeirceSpace e 1]) 0 := rfl
              _ ≤ ⨆ (j : Fin 3) (_ : j ≠ 2), _ := le_biSup _ (by decide : (0 : Fin 3) ≠ 2)
          · calc PeirceSpace e (1/2) = (![PeirceSpace e 0, PeirceSpace e (1/2),
                PeirceSpace e 1]) 1 := rfl
              _ ≤ ⨆ (j : Fin 3) (_ : j ≠ 2), _ := le_biSup _ (by decide : (1 : Fin 3) ≠ 2)
      simp only [show (⟨2, by decide⟩ : Fin 3) = (2 : Fin 3) from rfl] at hxsup
      rw [hsup, Submodule.mem_sup] at hxsup
      obtain ⟨y, hy, z, hz, hsum⟩ := hxsup
      rw [mem_peirceSpace_iff, zero_smul] at hy
      rw [mem_peirceSpace_iff] at hz
      -- x ∈ P₁: L_e(x) = x
      -- y ∈ P₀: L_e(y) = 0
      -- z ∈ P_{1/2}: L_e(z) = (1/2)z
      -- x = y + z, so L_e(x) = 0 + (1/2)z = (1/2)z
      -- But L_e(x) = x = y + z, so y + z = (1/2)z
      have h1 : y + z = (1/2 : ℝ) • z := by
        calc y + z = x := hsum
          _ = jmul e x := hx1'.symm
          _ = jmul e (y + z) := by rw [← hsum]
          _ = jmul e y + jmul e z := jmul_add e y z
          _ = 0 + (1/2 : ℝ) • z := by rw [hy, hz]
          _ = (1/2 : ℝ) • z := zero_add _
      -- So y = (1/2)z - z = -(1/2)z
      have hy_eq : y = -(1/2 : ℝ) • z := by
        have hcalc : y = (1/2 : ℝ) • z - z := by
          calc y = y + z - z := by abel
            _ = (1/2 : ℝ) • z - z := by rw [h1]
        rw [hcalc, sub_eq_add_neg, ← neg_one_smul ℝ z, ← add_smul]
        norm_num
      -- Apply L_e to x again: L_e²(x) = L_e(x) = x (since x ∈ P₁)
      -- L_e²(y + z) = L_e(0 + (1/2)z) = (1/2)L_e(z) = (1/4)z
      have hLe2 : jmul e (jmul e (y + z)) = (1/4 : ℝ) • z := by
        calc jmul e (jmul e (y + z)) = jmul e (0 + (1/2 : ℝ) • z) := by rw [jmul_add, hy, hz]
          _ = jmul e ((1/2 : ℝ) • z) := by rw [zero_add]
          _ = (1/2 : ℝ) • jmul e z := smul_jmul (1/2) e z
          _ = (1/2 : ℝ) • ((1/2 : ℝ) • z) := by rw [hz]
          _ = (1/4 : ℝ) • z := by rw [smul_smul]; norm_num
      -- But L_e²(x) = x = y + z, so y + z = (1/4)z
      have h2 : y + z = (1/4 : ℝ) • z := by
        calc y + z = x := hsum
          _ = jmul e x := hx1'.symm
          _ = jmul e (jmul e x) := congrArg (jmul e) hx1'.symm
          _ = jmul e (jmul e (y + z)) := by rw [← hsum]
          _ = (1/4 : ℝ) • z := hLe2
      -- From h1: y + z = (1/2)z and h2: y + z = (1/4)z
      -- So (1/2)z = (1/4)z, hence (1/4)z = 0, so z = 0
      have hz0 : z = 0 := by
        have : (1/2 : ℝ) • z = (1/4 : ℝ) • z := by rw [← h1, h2]
        have hdiff : (1/4 : ℝ) • z = 0 := by
          have hsub : (1/2 : ℝ) • z - (1/4 : ℝ) • z = 0 := by rw [this, sub_self]
          rw [← sub_smul] at hsub
          simp only [show (1/2 : ℝ) - 1/4 = 1/4 by norm_num] at hsub
          exact hsub
        have h14 : (1/4 : ℝ) ≠ 0 := by norm_num
        exact (smul_eq_zero_iff_right h14).mp hdiff
      have hy0 : y = 0 := by simp only [hy_eq, hz0, smul_zero, neg_zero]
      rw [← hsum, hy0, hz0, add_zero]
  · -- Spanning: prove iSup = ⊤
    -- The iSup over Fin 3 equals the three-way sup
    set f := ![PeirceSpace e 0, PeirceSpace e (1/2), PeirceSpace e 1] with hf
    have h : ⨆ i, f i = PeirceSpace e 0 ⊔ PeirceSpace e (1/2) ⊔ PeirceSpace e 1 := by
      apply le_antisymm
      · apply iSup_le
        intro i
        fin_cases i <;> simp only [hf]
        · exact le_sup_of_le_left le_sup_left
        · exact le_sup_of_le_left le_sup_right
        · exact le_sup_right
      · apply sup_le <;> [apply sup_le; skip]
        · exact le_iSup f 0
        · exact le_iSup f 1
        · exact le_iSup f 2
    rw [h]
    exact peirceSpace_iSup_eq_top he

end JordanAlgebra
