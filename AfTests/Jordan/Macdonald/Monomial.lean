/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Basic

/-!
# Monomial Representation for Macdonald's Theorem

Infrastructure for the M_{p,q} monomials used in H-O §2.4.22-2.4.24.

Every element of the free associative algebra A{x,y} can be written as an
ℝ-linear combination of monomials x^p · y^q · x^r · .... For Macdonald's
theorem, the key objects are the "alternating" monomials M_{p,q} defined by:

- M_{0,0} = 1
- M_{p+1,q} = x · M_{p,q}   (left multiply by x)
- M_{p,q+1} = M_{p,q} · y   (right multiply by y)

The simplest M_{p,q} are just x^p · y^q (a block of x's followed by y's).

## Main definitions

* `MacGen` — The two generators {x, y} of the free associative algebra
* `AssocWord` — Words in the free monoid on {x, y}
* `M_word` — The word representation of M_{p,q}
* `JordanAlgebra.M_eval` — Evaluation of M_{p,q} in a Jordan algebra

## Main results

* `macdonald_induction` — Simple induction on (p,q) pairs
* `macdonald_strong_induction` — Strong induction by total degree p + q
* `M_eval_right_zero` — M_{p,0}(a,b) = a^p
* `M_eval_left_zero` — M_{0,q}(a,b) = b^q
* `M_word_length` — |M_{p,q}| = p + q

## References

* Hanche-Olsen & Størmer, "Jordan Operator Algebras", §2.4.22-2.4.24
-/

/-! ### Generators and Words -/

/-- The two generators of the free associative algebra on {x, y}. -/
inductive MacGen : Type where
  | x : MacGen
  | y : MacGen
  deriving DecidableEq, Repr

/-- Words in the free monoid on two generators. Each word represents a
monomial in the free associative algebra A{x,y}. -/
abbrev AssocWord := List MacGen

/-- The word representation of M_{p,q}: x^p followed by y^q.
    M_{0,0} = [] (empty word = 1)
    M_{p+1,q} = x :: M_{p,q}
    M_{p,q+1} = M_{p,q} ++ [y] -/
def M_word : ℕ → ℕ → AssocWord
  | 0, 0 => []
  | p + 1, q => MacGen.x :: M_word p q
  | 0, q + 1 => M_word 0 q ++ [MacGen.y]

/-- The length of M_{p,q} equals its total degree p + q. -/
theorem M_word_length (p q : ℕ) : (M_word p q).length = p + q := by
  induction p with
  | zero =>
    induction q with
    | zero => simp [M_word]
    | succ q ih => simp [M_word, List.length_append]; omega
  | succ p ih => simp [M_word, ih]; omega

/-! ### Induction Principles -/

/-- Total degree of a monomial index pair (p, q). -/
def monoDeg : ℕ × ℕ → ℕ := fun pq => pq.1 + pq.2

/-- Simple induction on (p,q) pairs: prove P(0,0), then show the x-step
    P(p,q) → P(p+1,q) and y-step P(p,q) → P(p,q+1). -/
theorem macdonald_induction {P : ℕ → ℕ → Prop}
    (base : P 0 0)
    (step_x : ∀ p q, P p q → P (p + 1) q)
    (step_y : ∀ p q, P p q → P p (q + 1))
    : ∀ p q, P p q := by
  intro p
  induction p with
  | zero =>
    intro q
    induction q with
    | zero => exact base
    | succ q ih => exact step_y 0 q ih
  | succ p ih =>
    intro q
    exact step_x p q (ih q)

/-- Strong induction on total degree: assume P holds for all (p',q') with
    p' + q' < p + q. This is the induction principle used in H-O 2.4.24. -/
theorem macdonald_strong_induction {P : ℕ → ℕ → Prop}
    (h : ∀ p q, (∀ p' q', p' + q' < p + q → P p' q') → P p q)
    : ∀ p q, P p q := by
  intro p q
  have key : ∀ n, ∀ p q, p + q = n → P p q := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro p q hpq
      exact h p q (fun p' q' hlt => ih (p' + q') (hpq ▸ hlt) p' q' rfl)
  exact key (p + q) p q rfl

/-! ### Evaluation in a Jordan Algebra -/

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

/-- Evaluation of the monomial M_{p,q} in a Jordan algebra via
    substitution x ↦ a, y ↦ b, using Jordan products.

    M_{0,0}(a,b) = 1
    M_{p+1,q}(a,b) = a ∘ M_{p,q}(a,b)   (left Jordan multiply by a)
    M_{p,q+1}(a,b) = M_{p,q}(a,b) ∘ b   (right Jordan multiply by b)

    Note: In a Jordan algebra, right multiplication equals left multiplication
    (commutativity), so the x-step and y-step are both left multiplications.
    The distinction matters in the free associative algebra. -/
def M_eval (a b : J) : ℕ → ℕ → J
  | 0, 0 => jone
  | p + 1, q => jmul a (M_eval a b p q)
  | 0, q + 1 => jmul (M_eval a b 0 q) b

/-! #### Unfolding lemmas -/

@[simp] theorem M_eval_zero_zero (a b : J) : M_eval a b 0 0 = jone := by
  simp [M_eval]

@[simp] theorem M_eval_succ_left (a b : J) (p q : ℕ) :
    M_eval a b (p + 1) q = jmul a (M_eval a b p q) := by
  simp [M_eval]

@[simp] theorem M_eval_zero_succ (a b : J) (q : ℕ) :
    M_eval a b 0 (q + 1) = jmul (M_eval a b 0 q) b := by
  simp [M_eval]

/-! #### Special cases -/

theorem M_eval_one_zero (a b : J) : M_eval a b 1 0 = a := by
  simp [jmul_jone]

theorem M_eval_zero_one (a b : J) : M_eval a b 0 1 = b := by
  simp [jone_jmul]

/-- M_{p,0}(a,b) = a^p: left-only monomials are powers of a. -/
theorem M_eval_right_zero (a b : J) (p : ℕ) : M_eval a b p 0 = jpow a p := by
  induction p with
  | zero => simp
  | succ p ih => simp [jpow_succ, ih]

/-- M_{0,q}(a,b) = b^q: right-only monomials are powers of b. -/
theorem M_eval_left_zero (a b : J) (q : ℕ) : M_eval a b 0 q = jpow b q := by
  induction q with
  | zero => simp
  | succ q ih => simp [ih, jmul_comm, jpow_succ]

end JordanAlgebra
