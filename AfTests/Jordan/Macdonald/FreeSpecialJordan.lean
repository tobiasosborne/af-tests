/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Macdonald.FreeJordan
import Mathlib.Algebra.Algebra.Basic

/-!
# Free Special Jordan Algebra on Two Generators

Macdonald Step 6: Define evaluation of free Jordan algebra elements in associative
algebras via the symmetrized (Jordan) product `a ∘ b = ½(ab + ba)`, giving the
canonical surjection `FJ{x,y} → FS{x,y}`.

## Main definitions

* `FreeMagma.evalJordan` - Evaluate a magma word in an associative algebra using ∘
* `FreeNAAlg.evalJordanFun` - Linear extension to `FreeNAAlg`
* `FreeJordanAlg.evalAssoc` - The lift to the free Jordan algebra (via `Quotient.lift`)

## Main results

* `FreeNAAlg.evalJordan_congr` - `JordanCong f g → evalJordanFun a b f = evalJordanFun a b g`
-/

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-! ### Evaluation of FreeMagma in an associative algebra -/

/-- Evaluate a `FreeMagma` word in an associative algebra `A` using the Jordan
    (symmetrized) product: `m₁ * m₂ ↦ ½(v₁v₂ + v₂v₁)`. -/
noncomputable def FreeMagma.evalJordan (a b : A) : FreeMagma → A
  | .gen i => if i = 0 then a else b
  | .one => 1
  | .mul m₁ m₂ =>
    (1/2 : ℝ) • (evalJordan a b m₁ * evalJordan a b m₂ +
                  evalJordan a b m₂ * evalJordan a b m₁)

@[simp] theorem FreeMagma.evalJordan_gen0 (a b : A) :
    FreeMagma.evalJordan a b (.gen 0) = a := by
  simp [evalJordan]

@[simp] theorem FreeMagma.evalJordan_gen1 (a b : A) :
    FreeMagma.evalJordan a b (.gen 1) = b := by
  simp [evalJordan]

@[simp] theorem FreeMagma.evalJordan_one (a b : A) :
    FreeMagma.evalJordan a b .one = 1 := rfl

@[simp] theorem FreeMagma.evalJordan_mul' (a b : A) (m₁ m₂ : FreeMagma) :
    FreeMagma.evalJordan a b (.mul m₁ m₂) =
    (1/2 : ℝ) • (evalJordan a b m₁ * evalJordan a b m₂ +
                  evalJordan a b m₂ * evalJordan a b m₁) := rfl

/-- `unitMul` evaluates to the symmetrized product, same as `mul`. -/
theorem FreeMagma.evalJordan_unitMul (a b : A) (m₁ m₂ : FreeMagma) :
    FreeMagma.evalJordan a b (m₁.unitMul m₂) =
    (1/2 : ℝ) • (evalJordan a b m₁ * evalJordan a b m₂ +
                  evalJordan a b m₂ * evalJordan a b m₁) := by
  -- When one side is .one, unitMul simplifies but we need ½(1*v+v*1) = v
  -- When neither is .one, unitMul = mul so it's rfl
  cases m₁ with
  | one =>
    simp only [unitMul, evalJordan_one, one_mul, mul_one]
    rw [← two_smul ℝ (evalJordan a b m₂)]
    simp [smul_smul]
  | gen i =>
    cases m₂ with
    | one =>
      simp only [unitMul, one_mul, mul_one, evalJordan]
      rw [← two_smul ℝ]
      simp [smul_smul]
    | gen j => rfl
    | mul _ _ => rfl
  | mul _ _ =>
    cases m₂ with
    | one =>
      simp only [unitMul, evalJordan_one, one_mul, mul_one, evalJordan_mul']
      rw [← two_smul ℝ]
      simp [smul_smul]
    | gen j => rfl
    | mul _ _ => rfl

/-! ### Linear extension to FreeNAAlg -/

/-- Evaluate a `FreeNAAlg` element in an associative algebra using the Jordan product.
    Linearly extends `FreeMagma.evalJordan`. -/
noncomputable def FreeNAAlg.evalJordanFun (a b : A) (f : FreeNAAlg) : A :=
  f.sum fun m r => r • FreeMagma.evalJordan a b m

@[simp] theorem FreeNAAlg.evalJordanFun_ι (a b : A) (m : FreeMagma) :
    evalJordanFun a b (FreeNAAlg.ι m) = FreeMagma.evalJordan a b m := by
  unfold evalJordanFun ι
  rw [Finsupp.sum_single_index (by simp)]
  simp

theorem FreeNAAlg.evalJordanFun_zero (a b : A) :
    evalJordanFun a b 0 = 0 := by
  unfold evalJordanFun
  simp [Finsupp.sum]

theorem FreeNAAlg.evalJordanFun_add (a b : A) (f g : FreeNAAlg) :
    evalJordanFun a b (f + g) = evalJordanFun a b f + evalJordanFun a b g := by
  unfold evalJordanFun
  rw [Finsupp.sum_add_index (by intro i; simp) (by intro i _ r s; rw [add_smul])]

theorem FreeNAAlg.evalJordanFun_smul (a b : A) (r : ℝ) (f : FreeNAAlg) :
    evalJordanFun a b (r • f) = r • evalJordanFun a b f := by
  unfold evalJordanFun
  rw [Finsupp.sum_smul_index (by intro i; simp)]
  simp_rw [Finsupp.sum, Finset.smul_sum, smul_smul]

theorem FreeNAAlg.evalJordanFun_neg (a b : A) (f : FreeNAAlg) :
    evalJordanFun a b (-f) = -evalJordanFun a b f := by
  rw [show -f = (-1 : ℝ) • f from by simp, evalJordanFun_smul, neg_one_smul]

/-- `evalJordanFun` respects `FreeNAAlg.mul` — it sends `mul f g` to
    `½(eval f * eval g + eval g * eval f)`. -/
theorem FreeNAAlg.evalJordanFun_mul (a b : A) (f g : FreeNAAlg) :
    evalJordanFun a b (FreeNAAlg.mul f g) =
    (1/2 : ℝ) • (evalJordanFun a b f * evalJordanFun a b g +
                  evalJordanFun a b g * evalJordanFun a b f) := by
  -- Proof strategy (tested, nearly complete):
  -- 1. Use `refine Finsupp.induction_linear f` (NOT `apply f.induction_linear`)
  -- 2. Zero case: `simp [FreeNAAlg.mul, Finsupp.sum, FreeNAAlg.evalJordanFun]`
  -- 3. Add case: rw [add_mul, evalJordanFun_add, ih₁, ih₂], then
  --    conv_rhs to distribute `mul_add`/`add_mul` inside `•`,
  --    then `← smul_add; congr 1; rw [add_add_add_comm]`
  -- 4. Single case: rewrite single as r•ι, use smul_mul/mul_smul,
  --    then inner induction on g with same pattern.
  --    Base: evalJordanFun_mul_ι (helper for ι on left)
  -- Key issue: `conv_rhs` enters `•` but `mul_add`/`add_mul` are A-level
  --   not FreeNAAlg-level, so pattern matching fails.
  --   Fix: rewrite RHS `mul_add`/`add_mul` before entering `smul`.
  sorry

/-! ### JordanCong respects evaluation -/

/-- If `f` and `g` are Jordan-congruent, they evaluate to the same element
    in any associative algebra. -/
theorem FreeNAAlg.evalJordan_congr (a b : A) {f g : FreeNAAlg}
    (h : JordanCong f g) : evalJordanFun a b f = evalJordanFun a b g := by
  induction h with
  | comm f₁ f₂ =>
    simp only [evalJordanFun_mul]
    congr 1; exact add_comm _ _
  | jordan f₁ f₂ =>
    -- (a∘b)∘a² = a∘(b∘a²) in any associative algebra.
    -- After evalJordanFun_mul expands, both sides reduce to
    -- ¼(aba² + ba³ + a³b + a²ba) by associativity.
    -- Proof: expand all ½•(... + ...) factors, clear denominators,
    -- then the equality holds by ring in a (possibly non-comm) algebra.
    simp only [evalJordanFun_mul]
    sorry
  | add_left _ _ c _ ih =>
    simp only [evalJordanFun_add]; rw [ih]
  | add_right _ _ c _ ih =>
    simp only [evalJordanFun_add]; rw [ih]
  | smul_compat r _ _ _ ih =>
    simp only [evalJordanFun_smul]; rw [ih]
  | mul_left _ _ c _ ih =>
    simp only [evalJordanFun_mul]; rw [ih]
  | mul_right _ _ c _ ih =>
    simp only [evalJordanFun_mul]; rw [ih]
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ### Lift to FreeJordanAlg -/

/-- Evaluate a free Jordan algebra element in an associative algebra `A`,
    sending the generators `x ↦ a` and `y ↦ b`, with multiplication interpreted
    as the symmetrized product `½(ab + ba)`.

    This is the canonical map `FJ{x,y} → A` whose image is `FS{x,y}`. -/
noncomputable def FreeJordanAlg.evalAssoc (a b : A) : FreeJordanAlg → A :=
  Quotient.lift (FreeNAAlg.evalJordanFun a b)
    (fun _ _ h => FreeNAAlg.evalJordan_congr a b h)

@[simp] theorem FreeJordanAlg.evalAssoc_mk (a b : A) (f : FreeNAAlg) :
    evalAssoc a b (mk f) = FreeNAAlg.evalJordanFun a b f := rfl

@[simp] theorem FreeJordanAlg.evalAssoc_x (a b : A) :
    evalAssoc a b FreeJordanAlg.x = a := by
  unfold x; simp [FreeNAAlg.x]

@[simp] theorem FreeJordanAlg.evalAssoc_y (a b : A) :
    evalAssoc a b FreeJordanAlg.y = b := by
  unfold y; simp [FreeNAAlg.y]

theorem FreeJordanAlg.evalAssoc_add (a b : A) (u v : FreeJordanAlg) :
    evalAssoc a b (u + v) = evalAssoc a b u + evalAssoc a b v := by
  induction u using Quotient.ind; induction v using Quotient.ind
  exact FreeNAAlg.evalJordanFun_add a b _ _

theorem FreeJordanAlg.evalAssoc_smul (a b : A) (r : ℝ) (u : FreeJordanAlg) :
    evalAssoc a b (r • u) = r • evalAssoc a b u := by
  induction u using Quotient.ind
  exact FreeNAAlg.evalJordanFun_smul a b r _

theorem FreeJordanAlg.evalAssoc_mul (a b : A) (u v : FreeJordanAlg) :
    evalAssoc a b (FreeJordanAlg.mul u v) =
    (1/2 : ℝ) • (evalAssoc a b u * evalAssoc a b v +
                  evalAssoc a b v * evalAssoc a b u) := by
  induction u using Quotient.ind; induction v using Quotient.ind
  exact FreeNAAlg.evalJordanFun_mul a b _ _
