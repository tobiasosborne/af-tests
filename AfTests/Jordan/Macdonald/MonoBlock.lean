/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import AfTests.Jordan.Macdonald.Monomial

/-!
# Alternating-Block Monomials in FA{x,y}

Monomials in the free associative algebra FA{x,y} in alternating block form,
used in the construction of M_{p,q} operators (H-O 2.4.24).

A monomial x^{i₁}y^{j₁}x^{i₂}... is stored as alternating blocks where each
block records its exponent (≥1). The empty product is `one`.

## Main definitions

* `FreeAssocMono` — alternating block representation of monomials
* `FreeAssocMono.weight` — number of alternating blocks (H-O's w(p))
* `FreeAssocMono.inX` — monomial starts with x or is 1
* `FreeAssocMono.inY` — monomial starts with y or is 1
* `FreeAssocMono.degree` — total degree of monomial

## References

* Hanche-Olsen & Størmer, "Jordan Operator Algebras", §2.4.24
-/

/-- Monomial in FA{x,y} in alternating-block form.
    - `one` is the identity 1
    - `xCons i rest` represents x^(i+1) · rest, where rest ∈ Y (starts with y or is 1)
    - `yCons j rest` represents y^(j+1) · rest, where rest ∈ X (starts with x or is 1) -/
inductive FreeAssocMono : Type where
  | one : FreeAssocMono
  | xCons (i : ℕ) (rest : FreeAssocMono) : FreeAssocMono
  | yCons (j : ℕ) (rest : FreeAssocMono) : FreeAssocMono
  deriving DecidableEq, Repr

namespace FreeAssocMono

/-! ### Weight (number of alternating blocks) -/

/-- Weight of a monomial = number of alternating blocks. -/
def weight : FreeAssocMono → ℕ
  | one => 0
  | xCons _ rest => rest.weight + 1
  | yCons _ rest => rest.weight + 1

@[simp] theorem weight_one : weight one = 0 := rfl
@[simp] theorem weight_xCons (i : ℕ) (r : FreeAssocMono) :
    weight (xCons i r) = r.weight + 1 := rfl
@[simp] theorem weight_yCons (j : ℕ) (r : FreeAssocMono) :
    weight (yCons j r) = r.weight + 1 := rfl

/-! ### Total degree -/

/-- Total degree of a monomial (sum of all exponents). -/
def degree : FreeAssocMono → ℕ
  | one => 0
  | xCons i rest => (i + 1) + rest.degree
  | yCons j rest => (j + 1) + rest.degree

@[simp] theorem degree_one : degree one = 0 := rfl

/-! ### Classification predicates -/

/-- True if monomial starts with x. -/
def startsWithX : FreeAssocMono → Bool
  | xCons _ _ => true
  | _ => false

/-- True if monomial starts with y. -/
def startsWithY : FreeAssocMono → Bool
  | yCons _ _ => true
  | _ => false

/-- p ∈ X₀ means p starts with x (H-O notation). -/
def inX0 : FreeAssocMono → Prop := fun p => p.startsWithX = true

/-- p ∈ Y₀ means p starts with y (H-O notation). -/
def inY0 : FreeAssocMono → Prop := fun p => p.startsWithY = true

/-- p ∈ X = X₀ ∪ {1} means p starts with x or is 1. -/
def inX : FreeAssocMono → Prop := fun p => p = one ∨ p.inX0

/-- p ∈ Y = Y₀ ∪ {1} means p starts with y or is 1. -/
def inY : FreeAssocMono → Prop := fun p => p = one ∨ p.inY0

instance : DecidablePred inX0 := fun p => by
  unfold inX0; exact Bool.decEq _ _

instance : DecidablePred inY0 := fun p => by
  unfold inY0; exact Bool.decEq _ _

/-! ### Well-formedness -/

/-- A monomial is well-formed if x-blocks and y-blocks strictly alternate. -/
def WF : FreeAssocMono → Prop
  | one => True
  | xCons _ rest => rest.inY ∧ rest.WF
  | yCons _ rest => rest.inX ∧ rest.WF

/-! ### Convenient constructors for pure powers -/

/-- x^(k+1) as a monomial. -/
def xPow (k : ℕ) : FreeAssocMono := xCons k one

/-- y^(l+1) as a monomial. -/
def yPow (l : ℕ) : FreeAssocMono := yCons l one

@[simp] theorem weight_xPow (k : ℕ) : weight (xPow k) = 1 := rfl
@[simp] theorem weight_yPow (l : ℕ) : weight (yPow l) = 1 := rfl

@[simp] theorem xPow_inX0 (k : ℕ) : inX0 (xPow k) := rfl
@[simp] theorem yPow_inY0 (l : ℕ) : inY0 (yPow l) := rfl

/-! ### Prepend operations -/

/-- Prepend x^(k+1) to a monomial in Y, giving a monomial in X₀. -/
def prependX (k : ℕ) (p : FreeAssocMono) : FreeAssocMono :=
  match p with
  | xCons i rest => xCons (k + 1 + i) rest  -- merge x-blocks
  | _ => xCons k p  -- p ∈ Y, just prepend

/-- Prepend y^(l+1) to a monomial in X, giving a monomial in Y₀. -/
def prependY (l : ℕ) (p : FreeAssocMono) : FreeAssocMono :=
  match p with
  | yCons j rest => yCons (l + 1 + j) rest  -- merge y-blocks
  | _ => yCons l p  -- p ∈ X, just prepend

theorem prependX_inX0 (k : ℕ) (p : FreeAssocMono) :
    inX0 (prependX k p) := by
  unfold prependX inX0 startsWithX
  cases p <;> simp

theorem prependY_inY0 (l : ℕ) (p : FreeAssocMono) :
    inY0 (prependY l p) := by
  unfold prependY inY0 startsWithY
  cases p <;> simp

/-- For well-formed p ∈ Y, prependX doesn't merge blocks. -/
theorem prependX_of_inY {p : FreeAssocMono} (hp : p.inY) :
    prependX k p = xCons k p := by
  cases p with
  | one => rfl
  | xCons i r =>
    exfalso
    cases hp with
    | inl h => exact FreeAssocMono.noConfusion h
    | inr h => exact absurd h (by simp [inY0, startsWithY])
  | yCons j r => rfl

/-- For well-formed p ∈ X, prependY doesn't merge blocks. -/
theorem prependY_of_inX {p : FreeAssocMono} (hp : p.inX) :
    prependY l p = yCons l p := by
  cases p with
  | one => rfl
  | xCons i r => rfl
  | yCons j r =>
    exfalso
    cases hp with
    | inl h => exact FreeAssocMono.noConfusion h
    | inr h => exact absurd h (by simp [inX0, startsWithX])

/-! ### Classification lemmas -/

theorem xCons_inX0 (i : ℕ) (r : FreeAssocMono) : inX0 (xCons i r) := rfl

theorem yCons_inY0 (j : ℕ) (r : FreeAssocMono) : inY0 (yCons j r) := rfl

theorem one_inX : inX one := Or.inl rfl

theorem one_inY : inY one := Or.inl rfl

theorem xCons_inX (i : ℕ) (r : FreeAssocMono) : inX (xCons i r) :=
  Or.inr (xCons_inX0 i r)

theorem yCons_inY (j : ℕ) (r : FreeAssocMono) : inY (yCons j r) :=
  Or.inr (yCons_inY0 j r)

/-! ### Weight of prepend operations -/

theorem weight_prependX_of_inY {p : FreeAssocMono} (hp : p.inY) (k : ℕ) :
    (prependX k p).weight = p.weight + 1 := by
  rw [prependX_of_inY hp, weight_xCons]

theorem weight_prependY_of_inX {p : FreeAssocMono} (hp : p.inX) (l : ℕ) :
    (prependY l p).weight = p.weight + 1 := by
  rw [prependY_of_inX hp, weight_yCons]

theorem weight_prependX_of_inX0 {p : FreeAssocMono} (hp : p.inX0) (k : ℕ) :
    (prependX k p).weight = p.weight := by
  cases p with
  | one => exact absurd hp (by simp [inX0, startsWithX])
  | xCons i rest => simp [prependX, weight]
  | yCons j rest => exact absurd hp (by simp [inX0, startsWithX])

theorem weight_prependY_of_inY0 {p : FreeAssocMono} (hp : p.inY0) (l : ℕ) :
    (prependY l p).weight = p.weight := by
  cases p with
  | one => exact absurd hp (by simp [inY0, startsWithY])
  | xCons i rest => exact absurd hp (by simp [inY0, startsWithY])
  | yCons j rest => simp [prependY, weight]

/-! ### Rest classification for well-formed monomials -/

theorem rest_inY_of_xCons (i : ℕ) (r : FreeAssocMono) (h : WF (xCons i r)) :
    r.inY := h.1

theorem rest_inX_of_yCons (j : ℕ) (r : FreeAssocMono) (h : WF (yCons j r)) :
    r.inX := h.1

end FreeAssocMono
