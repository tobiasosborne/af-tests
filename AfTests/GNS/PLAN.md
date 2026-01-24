# GNS Construction: Detailed Implementation Plan

## Overview

The **Gelfand-Naimark-Segal (GNS) construction** is a fundamental theorem in functional analysis that constructs a Hilbert space representation from a state on a C*-algebra. Given a C*-algebra `A` and a state `φ : A → ℂ`, the GNS construction produces:

1. A Hilbert space `H_φ`
2. A *-representation `π_φ : A → B(H_φ)`
3. A cyclic vector `Ω_φ ∈ H_φ`

Such that `φ(a) = ⟨Ω_φ, π_φ(a) Ω_φ⟩` for all `a ∈ A`.

---

## Mathlib Infrastructure Available

### Can Use Directly (No New Code Needed)

| Component | Mathlib Location | Usage |
|-----------|------------------|-------|
| `CStarAlgebra A` | `Analysis.CStarAlgebra.Classes` | Base typeclass |
| `PositiveLinearMap R E₁ E₂` | `Algebra.Order.Module.PositiveLinearMap` | Positive maps |
| `PositiveLinearMap.exists_norm_apply_le` | `Analysis.CStarAlgebra.PositiveLinearMap` | Auto-boundedness |
| `StarAlgHom R A B` | `Algebra.Star.StarAlgHom` | *-homomorphisms |
| `InnerProductSpace 𝕜 E` | `Analysis.InnerProductSpace.Basic` | Pre-Hilbert spaces |
| `UniformSpace.Completion` | `Topology.UniformSpace.Completion` | Completion |
| `UniformSpace.Completion.innerProductSpace` | `Analysis.InnerProductSpace.Completion` | Hilbert completion |
| `ContinuousLinearMap 𝕜 E F` | `Analysis.Normed.Operator.ContinuousLinearMap` | Bounded operators |
| `ContinuousLinearMap.adjoint` | `Analysis.InnerProductSpace.Adjoint` | Adjoint operators |
| `QuotientAddGroup` | `GroupTheory.QuotientGroup.Basic` | Quotient groups |
| `SeparationQuotient` | `Analysis.InnerProductSpace.Completion` | Quotient pattern |
| `StarOrderedRing` | `Algebra.Order.Star.Basic` | Positivity |
| `IsSelfAdjoint` | `Algebra.Star.SelfAdjoint` | Self-adjoint elements |

### Must Build (This Implementation)

| Component | Description |
|-----------|-------------|
| `State A` | Positive linear functional with norm 1 |
| `gnsNullSpace φ` | Left ideal `{a : φ(a*a) = 0}` |
| `gnsQuotient φ` | Quotient `A / gnsNullSpace φ` |
| `gnsInner φ` | Inner product `⟨[a], [b]⟩ = φ(b*a)` |
| `gnsHilbertSpace φ` | Completion of quotient |
| `gnsCyclicVector φ` | The vector `[1]` |
| `gnsRep φ` | Representation `π_φ(a)[b] = [ab]` |

---

## File Structure

```
AfTests/GNS/
├── PLAN.md                          # This file
├── State/
│   ├── Basic.lean                   # State definition
│   ├── Positivity.lean              # Positivity properties
│   └── CauchySchwarz.lean           # Cauchy-Schwarz for states
├── NullSpace/
│   ├── Basic.lean                   # Null space definition
│   ├── LeftIdeal.lean               # Left ideal property
│   └── Quotient.lean                # Quotient construction
├── PreHilbert/
│   ├── InnerProduct.lean            # Inner product definition
│   ├── Positive.lean                # Positive definiteness
│   └── Seminorm.lean                # Seminorm properties
├── HilbertSpace/
│   ├── Completion.lean              # Hilbert space completion
│   └── CyclicVector.lean            # Cyclic vector
├── Representation/
│   ├── PreRep.lean                  # Pre-representation on quotient
│   ├── Bounded.lean                 # Boundedness proof
│   ├── Extension.lean               # Extension to completion
│   └── Star.lean                    # *-representation property
└── Main/
    ├── VectorState.lean             # φ(a) = ⟨Ω, π(a)Ω⟩
    ├── Uniqueness.lean              # Uniqueness up to unitary
    └── Theorem.lean                 # Main GNS theorem
```

---

## Phase 1: States on C*-Algebras

### File: `State/Basic.lean` (Target: 40-60 LOC)

**Mathematical Content:**
A state on a C*-algebra `A` is a positive linear functional `φ : A → ℂ` with `φ(1) = 1`.

**Definitions:**
```lean
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Classes

/-- A state on a C*-algebra is a positive linear functional with φ(1) = 1. -/
structure State (A : Type*) [CStarAlgebra A] where
  toPositiveLinearMap : A →ₚ[ℂ] ℂ
  map_one : toPositiveLinearMap 1 = 1

namespace State
variable {A : Type*} [CStarAlgebra A] (φ : State A)

instance : FunLike (State A) A ℂ := ...
instance : PositiveLinearMapClass (State A) ℂ A ℂ := ...

/-- States are continuous (inherited from positive linear maps). -/
theorem continuous : Continuous φ := ...

/-- The norm of a state is 1. -/
theorem norm_eq_one : ‖φ.toPositiveLinearMap‖ = 1 := ...

end State
```

**Key Lemmas:**
1. `State.continuous` - Automatic from `PositiveLinearMap.exists_norm_apply_le`
2. `State.norm_eq_one` - Uses `map_one` and positivity
3. `State.apply_nonneg_of_star_mul_self` - `φ(a*a) ≥ 0`

**Proof Strategy:**
- Positivity: Inherits from `PositiveLinearMap`
- Continuity: Mathlib proves positive maps on C*-algebras are bounded
- Norm: Use `φ(1) = 1` and `‖φ‖ = sup{|φ(a)| : ‖a‖ ≤ 1}`

---

### File: `State/Positivity.lean` (Target: 40-60 LOC)

**Mathematical Content:**
States preserve self-adjointness and satisfy `φ(a*) = conj(φ(a))`.

**Key Lemmas:**
```lean
/-- φ(a*) = conj(φ(a)) for any state. -/
theorem map_star (a : A) : φ (star a) = conj (φ a) := ...

/-- φ(a) is real when a is self-adjoint. -/
theorem apply_real_of_isSelfAdjoint (ha : IsSelfAdjoint a) :
    φ a = (φ a).re := ...

/-- φ(a*a) is a non-negative real. -/
theorem apply_star_mul_self_nonneg (a : A) :
    0 ≤ (φ (star a * a)).re := ...

/-- φ(a*a) = 0 implies a*a positive part is zero. -/
theorem apply_star_mul_self_eq_zero_iff (a : A) :
    φ (star a * a) = 0 ↔ φ (star a * a) = 0 := ...
```

**Proof Strategy:**
- `map_star`: Mathlib's `PositiveLinearMap` on C*-algebras is automatically star-preserving
- Real values: Self-adjoint elements map to self-adjoint (real) values
- Non-negativity: `a*a` is positive, positive maps preserve positivity

---

### File: `State/CauchySchwarz.lean` (Target: 50-70 LOC)

**Mathematical Content:**
The Cauchy-Schwarz inequality for states: `|φ(b*a)|² ≤ φ(a*a) · φ(b*b)`.

**Key Lemma:**
```lean
/-- Cauchy-Schwarz inequality for states. -/
theorem cauchy_schwarz (a b : A) :
    ‖φ (star b * a)‖^2 ≤ (φ (star a * a)).re * (φ (star b * b)).re := by
  -- Define f(t) = φ((a + tb)*(a + tb)) ≥ 0 for all t ∈ ℝ
  -- Expand and use quadratic discriminant ≤ 0
  ...
```

**Proof Strategy:**
1. For any `t : ℝ`, define `c = a + t • b`
2. Then `φ(c*c) ≥ 0` (positivity)
3. Expand: `φ(a*a) + 2t·Re(φ(b*a)) + t²·φ(b*b) ≥ 0`
4. Quadratic in `t` with non-negative values implies discriminant ≤ 0
5. This gives `4·|Re(φ(b*a))|² ≤ 4·φ(a*a)·φ(b*b)`
6. Repeat with `i·t` to get imaginary part, combine

---

## Phase 2: GNS Null Space

### File: `NullSpace/Basic.lean` (Target: 50-70 LOC)

**Mathematical Content:**
The GNS null space is `N_φ = {a ∈ A : φ(a*a) = 0}`.

**Definitions:**
```lean
/-- The GNS null space: elements a where φ(a*a) = 0. -/
def gnsNullSpace (φ : State A) : AddSubgroup A where
  carrier := {a : A | φ (star a * a) = 0}
  zero_mem' := by simp [star_zero, zero_mul, map_zero]
  add_mem' := ...  -- Uses Cauchy-Schwarz
  neg_mem' := by simp [star_neg, neg_mul_neg]
```

**Key Lemmas:**
```lean
theorem mem_gnsNullSpace_iff (a : A) :
    a ∈ gnsNullSpace φ ↔ φ (star a * a) = 0 := Iff.rfl

theorem zero_mem : (0 : A) ∈ gnsNullSpace φ := ...

theorem add_mem (ha : a ∈ gnsNullSpace φ) (hb : b ∈ gnsNullSpace φ) :
    a + b ∈ gnsNullSpace φ := by
  -- |φ((a+b)*(a+b))| ≤ |φ(a*a)| + 2|φ(b*a)| + |φ(b*b)|
  -- By Cauchy-Schwarz: |φ(b*a)|² ≤ φ(a*a)·φ(b*b) = 0
  ...

theorem neg_mem (ha : a ∈ gnsNullSpace φ) : -a ∈ gnsNullSpace φ := ...

theorem smul_mem (c : ℂ) (ha : a ∈ gnsNullSpace φ) :
    c • a ∈ gnsNullSpace φ := ...
```

**Proof Strategy:**
- `zero_mem`: Direct computation
- `neg_mem`: `(-a)*(-a) = a*a`
- `add_mem`: Expand `(a+b)*(a+b)`, use Cauchy-Schwarz to show cross terms vanish
- `smul_mem`: `(ca)*(ca) = |c|²·a*a`

---

### File: `NullSpace/LeftIdeal.lean` (Target: 50-70 LOC)

**Mathematical Content:**
`N_φ` is a left ideal: if `a ∈ N_φ` then `ba ∈ N_φ` for all `b`.

**Key Lemmas:**
```lean
/-- The null space is closed under left multiplication. -/
theorem mul_mem_left (b : A) (ha : a ∈ gnsNullSpace φ) :
    b * a ∈ gnsNullSpace φ := by
  -- φ((ba)*(ba)) = φ(a* b* b a)
  -- By Cauchy-Schwarz: |φ(a* b* b a)|² ≤ φ(a*a) · φ((b*ba)*(b*ba))
  -- Since φ(a*a) = 0, we get φ((ba)*(ba)) = 0
  ...

/-- The null space as a submodule (left ideal). -/
def gnsNullIdeal (φ : State A) : Submodule ℂ A where
  carrier := gnsNullSpace φ
  add_mem' := gnsNullSpace.add_mem φ
  zero_mem' := gnsNullSpace.zero_mem φ
  smul_mem' := gnsNullSpace.smul_mem φ

/-- The null ideal is a left ideal of A. -/
theorem gnsNullIdeal.mul_mem_left (b : A) (ha : a ∈ gnsNullIdeal φ) :
    b * a ∈ gnsNullIdeal φ := mul_mem_left φ b ha
```

**Proof Strategy:**
For `b * a ∈ N_φ`:
1. Need `φ((ba)*(ba)) = 0`
2. Compute `(ba)* = a* b*`, so `(ba)*(ba) = a* b* b a`
3. Apply Cauchy-Schwarz: `|φ(a* · b*ba)|² ≤ φ(a*a) · φ((b*ba)*(b*ba))`
4. Since `a ∈ N_φ`, we have `φ(a*a) = 0`, so LHS = 0

---

### File: `NullSpace/Quotient.lean` (Target: 60-80 LOC)

**Mathematical Content:**
The quotient `A / N_φ` as a ℂ-module with well-defined left A-action.

**Definitions:**
```lean
/-- The GNS quotient space A / N_φ. -/
abbrev gnsQuotient (φ : State A) := A ⧸ gnsNullIdeal φ

/-- Quotient map. -/
def gnsQuotientMk (φ : State A) : A →ₗ[ℂ] gnsQuotient φ :=
  Submodule.mkQ (gnsNullIdeal φ)

/-- Left action of A on the quotient: a • [b] = [ab]. -/
def gnsLeftAction (φ : State A) (a : A) : gnsQuotient φ →ₗ[ℂ] gnsQuotient φ :=
  Submodule.liftQ (gnsNullIdeal φ)
    ((gnsQuotientMk φ).comp (LinearMap.lmul ℂ A a))
    (fun x hx => by
      -- Need: ab ∈ N_φ when b ∈ N_φ
      exact Submodule.Quotient.mk_eq_zero.mpr (mul_mem_left φ a hx))
```

**Key Lemmas:**
```lean
theorem gnsLeftAction_mk (a b : A) :
    gnsLeftAction φ a (gnsQuotientMk φ b) = gnsQuotientMk φ (a * b) := ...

theorem gnsLeftAction_mul (a b : A) :
    gnsLeftAction φ (a * b) = gnsLeftAction φ a ∘ₗ gnsLeftAction φ b := ...

theorem gnsLeftAction_one : gnsLeftAction φ 1 = LinearMap.id := ...

theorem gnsLeftAction_add (a b : A) :
    gnsLeftAction φ (a + b) = gnsLeftAction φ a + gnsLeftAction φ b := ...
```

---

## Phase 3: Pre-Hilbert Space Structure

### File: `PreHilbert/InnerProduct.lean` (Target: 70-90 LOC)

**Mathematical Content:**
Define inner product `⟨[a], [b]⟩ = φ(b*a)` on the quotient.

**Definitions:**
```lean
/-- Inner product on the GNS quotient: ⟨[a], [b]⟩ = φ(b*a). -/
def gnsInner (φ : State A) : gnsQuotient φ → gnsQuotient φ → ℂ :=
  Quotient.lift₂
    (fun a b => φ (star b * a))
    (fun a₁ a₂ b₁ b₂ ha hb => by
      -- Need: φ(b₁*a₁) = φ(b₂*a₂) when a₁ - a₂ ∈ N_φ and b₁ - b₂ ∈ N_φ
      -- Equivalently: φ(b₁*a₁) - φ(b₂*a₂) = 0
      -- = φ(b₁*a₁ - b₂*a₂) = φ(b₁*(a₁-a₂) + (b₁-b₂)*a₂)
      -- Both terms vanish by Cauchy-Schwarz
      ...)
```

**Key Lemmas:**
```lean
theorem gnsInner_mk (a b : A) :
    gnsInner φ (gnsQuotientMk φ a) (gnsQuotientMk φ b) = φ (star b * a) := rfl

/-- Inner product is conjugate-symmetric. -/
theorem gnsInner_conj_symm (x y : gnsQuotient φ) :
    gnsInner φ y x = conj (gnsInner φ x y) := by
  induction x, y using Quotient.inductionOn₂
  simp [gnsInner_mk, ← map_star]
  -- φ(a*b) = conj(φ(b*a)) by star-preservation

/-- Inner product is linear in the first argument. -/
theorem gnsInner_add_left (x y z : gnsQuotient φ) :
    gnsInner φ (x + y) z = gnsInner φ x z + gnsInner φ y z := ...

theorem gnsInner_smul_left (c : ℂ) (x y : gnsQuotient φ) :
    gnsInner φ (c • x) y = c * gnsInner φ x y := ...
```

**Well-Definedness Proof Strategy:**
Need to show: if `a₁ - a₂ ∈ N_φ` and `b₁ - b₂ ∈ N_φ`, then `φ(b₁*a₁) = φ(b₂*a₂)`.

1. Write `φ(b₁*a₁) - φ(b₂*a₂) = φ(b₁*a₁ - b₂*a₂)`
2. Add/subtract: `= φ(b₁*(a₁-a₂)) + φ((b₁-b₂)*a₂)`
3. First term: By Cauchy-Schwarz, `|φ(b₁*(a₁-a₂))|² ≤ φ((a₁-a₂)*(a₁-a₂)) · φ(b₁*b₁) = 0`
4. Second term: Similarly vanishes
5. Therefore difference is 0

---

### File: `PreHilbert/Positive.lean` (Target: 60-80 LOC)

**Mathematical Content:**
The inner product is positive definite on the quotient.

**Key Lemmas:**
```lean
/-- Inner product with self is non-negative real. -/
theorem gnsInner_self_nonneg (x : gnsQuotient φ) :
    0 ≤ (gnsInner φ x x).re := by
  induction x using Quotient.inductionOn
  simp [gnsInner_mk]
  exact φ.apply_star_mul_self_nonneg _

/-- Inner product with self is zero iff element is zero. -/
theorem gnsInner_self_eq_zero_iff (x : gnsQuotient φ) :
    gnsInner φ x x = 0 ↔ x = 0 := by
  induction x using Quotient.inductionOn with | h a =>
  simp [gnsInner_mk]
  constructor
  · intro h
    -- φ(a*a) = 0 means a ∈ N_φ, so [a] = 0
    exact Submodule.Quotient.mk_eq_zero.mpr h
  · intro h
    -- [a] = 0 means a ∈ N_φ, so φ(a*a) = 0
    exact (Submodule.Quotient.mk_eq_zero.mp h)

/-- Inner product is real for self. -/
theorem gnsInner_self_re (x : gnsQuotient φ) :
    (gnsInner φ x x).re = gnsInner φ x x := by
  induction x using Quotient.inductionOn
  simp [gnsInner_mk, φ.apply_real_of_isSelfAdjoint (IsSelfAdjoint.star_mul_self _)]
```

---

### File: `PreHilbert/Seminorm.lean` (Target: 60-80 LOC)

**Mathematical Content:**
Define the norm `‖[a]‖ = √(φ(a*a))` and prove basic properties.

**Definitions:**
```lean
/-- The GNS norm on the quotient. -/
noncomputable def gnsNorm (φ : State A) (x : gnsQuotient φ) : ℝ :=
  Real.sqrt (gnsInner φ x x).re

/-- The InnerProductSpace instance on the GNS quotient. -/
noncomputable instance gnsQuotient.innerProductSpace (φ : State A) :
    InnerProductSpace ℂ (gnsQuotient φ) where
  inner := gnsInner φ
  norm_sq_eq_re_inner := fun x => by simp [gnsNorm]
  conj_inner_symm := gnsInner_conj_symm φ
  add_left := gnsInner_add_left φ
  smul_left := gnsInner_smul_left φ
```

**Key Lemmas:**
```lean
theorem gnsNorm_mk (a : A) :
    ‖gnsQuotientMk φ a‖ = Real.sqrt (φ (star a * a)).re := rfl

/-- The GNS norm is bounded by the C*-algebra norm. -/
theorem gnsNorm_le_norm (a : A) : ‖gnsQuotientMk φ a‖ ≤ ‖a‖ := by
  -- φ(a*a) ≤ ‖φ‖ · ‖a*a‖ = ‖a‖² (since ‖φ‖ = 1 and C*-identity)
  ...

/-- Left action is bounded: ‖a • [b]‖ ≤ ‖a‖ · ‖[b]‖. -/
theorem gnsLeftAction_norm_le (a : A) (x : gnsQuotient φ) :
    ‖gnsLeftAction φ a x‖ ≤ ‖a‖ * ‖x‖ := by
  -- ‖[ab]‖² = φ((ab)*(ab)) = φ(b* a* a b)
  -- Use: a*a ≤ ‖a‖² · 1 in C*-algebra order
  -- Then φ(b* a* a b) ≤ ‖a‖² · φ(b*b) = ‖a‖² · ‖[b]‖²
  ...
```

---

## Phase 4: GNS Hilbert Space

### File: `HilbertSpace/Completion.lean` (Target: 50-70 LOC)

**Mathematical Content:**
Complete the pre-Hilbert space to get a Hilbert space.

**Definitions:**
```lean
/-- The GNS Hilbert space: completion of A/N_φ. -/
def gnsHilbertSpace (φ : State A) : Type* :=
  UniformSpace.Completion (gnsQuotient φ)

/-- The GNS Hilbert space is a Hilbert space. -/
noncomputable instance (φ : State A) : InnerProductSpace ℂ (gnsHilbertSpace φ) :=
  UniformSpace.Completion.innerProductSpace ℂ (gnsQuotient φ)

instance (φ : State A) : CompleteSpace (gnsHilbertSpace φ) :=
  UniformSpace.Completion.completeSpace (gnsQuotient φ)

/-- Canonical embedding of quotient into Hilbert space. -/
def gnsEmbed (φ : State A) : gnsQuotient φ →L[ℂ] gnsHilbertSpace φ :=
  UniformSpace.Completion.toComplₗᵢ.toContinuousLinearMap

/-- Canonical embedding of A into Hilbert space. -/
def gnsEmbedA (φ : State A) : A →ₗ[ℂ] gnsHilbertSpace φ :=
  (gnsEmbed φ).toLinearMap.comp (gnsQuotientMk φ)
```

**Key Lemmas:**
```lean
theorem gnsEmbed_isometry : Isometry (gnsEmbed φ) :=
  UniformSpace.Completion.toComplₗᵢ.isometry

theorem gnsEmbed_denseRange : DenseRange (gnsEmbed φ) :=
  UniformSpace.Completion.denseRange_coe

theorem gnsHilbertSpace.inner_embed (x y : gnsQuotient φ) :
    ⟪gnsEmbed φ x, gnsEmbed φ y⟫ = ⟪x, y⟫ :=
  UniformSpace.Completion.inner_coe x y
```

---

### File: `HilbertSpace/CyclicVector.lean` (Target: 50-70 LOC)

**Mathematical Content:**
The cyclic vector `Ω_φ = [1]` and its properties.

**Definitions:**
```lean
/-- The GNS cyclic vector: [1] in the Hilbert space. -/
def gnsCyclicVector (φ : State A) : gnsHilbertSpace φ :=
  gnsEmbed φ (gnsQuotientMk φ 1)

notation "Ω_" φ => gnsCyclicVector φ
```

**Key Lemmas:**
```lean
/-- The cyclic vector has norm 1. -/
theorem gnsCyclicVector_norm : ‖Ω_ φ‖ = 1 := by
  simp [gnsCyclicVector, gnsEmbed_isometry.norm_map]
  simp [gnsNorm_mk, star_one, one_mul, φ.map_one]
  exact Real.sqrt_one

/-- Inner product of cyclic vector with itself. -/
theorem gnsCyclicVector_inner_self : ⟪Ω_ φ, Ω_ φ⟫ = 1 := by
  rw [← inner_self_eq_norm_sq_to_K, gnsCyclicVector_norm, one_pow]

/-- The orbit π(A)Ω is dense in H_φ. -/
theorem gnsCyclicVector_span_dense :
    DenseRange (fun a : A => gnsRep φ a (Ω_ φ)) := by
  -- gnsRep φ a (Ω_φ) = [a·1] = [a]
  -- Range is gnsEmbed φ '' (range gnsQuotientMk)
  -- This is dense by gnsEmbed_denseRange and surjectivity of quotient map
  ...
```

---

## Phase 5: GNS Representation

### File: `Representation/PreRep.lean` (Target: 60-80 LOC)

**Mathematical Content:**
Define the pre-representation `π(a)[b] = [ab]` on the quotient.

**Definitions:**
```lean
/-- Pre-representation on the quotient: π(a)[b] = [ab]. -/
def gnsPreRep (φ : State A) (a : A) : gnsQuotient φ →ₗ[ℂ] gnsQuotient φ :=
  gnsLeftAction φ a
```

**Key Lemmas:**
```lean
theorem gnsPreRep_mk (a b : A) :
    gnsPreRep φ a (gnsQuotientMk φ b) = gnsQuotientMk φ (a * b) :=
  gnsLeftAction_mk φ a b

/-- Pre-representation is multiplicative. -/
theorem gnsPreRep_mul (a b : A) :
    gnsPreRep φ (a * b) = gnsPreRep φ a ∘ₗ gnsPreRep φ b :=
  gnsLeftAction_mul φ a b

/-- Pre-representation preserves identity. -/
theorem gnsPreRep_one : gnsPreRep φ 1 = LinearMap.id :=
  gnsLeftAction_one φ

/-- Pre-representation is additive. -/
theorem gnsPreRep_add (a b : A) :
    gnsPreRep φ (a + b) = gnsPreRep φ a + gnsPreRep φ b :=
  gnsLeftAction_add φ a b

/-- Pre-representation respects scalar multiplication. -/
theorem gnsPreRep_smul (c : ℂ) (a : A) :
    gnsPreRep φ (c • a) = c • gnsPreRep φ a := ...
```

---

### File: `Representation/Bounded.lean` (Target: 60-80 LOC)

**Mathematical Content:**
Prove the pre-representation is bounded with `‖π(a)‖ ≤ ‖a‖`.

**Key Lemmas:**
```lean
/-- The pre-representation is bounded. -/
theorem gnsPreRep_norm_le (a : A) (x : gnsQuotient φ) :
    ‖gnsPreRep φ a x‖ ≤ ‖a‖ * ‖x‖ :=
  gnsLeftAction_norm_le φ a x

/-- The pre-representation as a continuous linear map. -/
noncomputable def gnsPreRepCLM (φ : State A) (a : A) :
    gnsQuotient φ →L[ℂ] gnsQuotient φ :=
  (gnsPreRep φ a).mkContinuous ‖a‖ (gnsPreRep_norm_le φ a)

theorem gnsPreRepCLM_norm_le (a : A) : ‖gnsPreRepCLM φ a‖ ≤ ‖a‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg a) _
```

**Proof Strategy for Boundedness:**
1. Need: `‖[ab]‖ ≤ ‖a‖ · ‖[b]‖`
2. Compute: `‖[ab]‖² = ⟨[ab], [ab]⟩ = φ((ab)*(ab)) = φ(b* a* a b)`
3. Key inequality: In C*-algebras, `a*a ≤ ‖a‖² · 1` (spectral theory)
4. Positivity of φ: `φ(b* a* a b) ≤ φ(b* · ‖a‖² · 1 · b) = ‖a‖² · φ(b*b)`
5. Therefore: `‖[ab]‖² ≤ ‖a‖² · ‖[b]‖²`

---

### File: `Representation/Extension.lean` (Target: 60-80 LOC)

**Mathematical Content:**
Extend the representation to the completion.

**Definitions:**
```lean
/-- The GNS representation on the Hilbert space. -/
noncomputable def gnsRep (φ : State A) (a : A) :
    gnsHilbertSpace φ →L[ℂ] gnsHilbertSpace φ :=
  (gnsPreRepCLM φ a).extend (gnsEmbed φ) (gnsEmbed φ)
    gnsEmbed_uniformInducing gnsEmbed_denseRange
```

**Key Lemmas:**
```lean
/-- Extension agrees with pre-representation on dense subspace. -/
theorem gnsRep_embed (a : A) (x : gnsQuotient φ) :
    gnsRep φ a (gnsEmbed φ x) = gnsEmbed φ (gnsPreRep φ a x) := ...

/-- GNS representation on cyclic vector. -/
theorem gnsRep_cyclicVector (a : A) :
    gnsRep φ a (Ω_ φ) = gnsEmbed φ (gnsQuotientMk φ a) := by
  simp [gnsCyclicVector, gnsRep_embed, gnsPreRep_mk, mul_one]

/-- GNS representation is multiplicative. -/
theorem gnsRep_mul (a b : A) : gnsRep φ (a * b) = gnsRep φ a ∘L gnsRep φ b := by
  ext x
  -- By density, suffices to check on gnsEmbed φ y
  -- gnsRep φ (ab) (gnsEmbed φ y) = gnsEmbed φ [aby]
  -- gnsRep φ a (gnsRep φ b (gnsEmbed φ y)) = gnsRep φ a (gnsEmbed φ [by]) = gnsEmbed φ [aby]
  ...

theorem gnsRep_one : gnsRep φ 1 = ContinuousLinearMap.id ℂ _ := ...

theorem gnsRep_add (a b : A) : gnsRep φ (a + b) = gnsRep φ a + gnsRep φ b := ...

theorem gnsRep_norm_le (a : A) : ‖gnsRep φ a‖ ≤ ‖a‖ := ...
```

---

### File: `Representation/Star.lean` (Target: 70-90 LOC)

**Mathematical Content:**
Prove `π(a*) = π(a)*` (adjoint property).

**Key Lemmas:**
```lean
/-- The GNS representation preserves the star operation. -/
theorem gnsRep_star (a : A) : gnsRep φ (star a) = (gnsRep φ a).adjoint := by
  -- Suffices to show ⟨π(a*)x, y⟩ = ⟨x, π(a)y⟩ for all x, y
  -- By density, check on gnsEmbed φ [b], gnsEmbed φ [c]
  -- ⟨π(a*)[b], [c]⟩ = ⟨[a*b], [c]⟩ = φ(c* a* b)
  -- ⟨[b], π(a)[c]⟩ = ⟨[b], [ac]⟩ = φ((ac)* b) = φ(c* a* b) ✓
  ext x
  ...

/-- The GNS representation as a *-algebra homomorphism. -/
noncomputable def gnsStarAlgHom (φ : State A) :
    A →⋆ₐ[ℂ] (gnsHilbertSpace φ →L[ℂ] gnsHilbertSpace φ) where
  toFun := gnsRep φ
  map_one' := gnsRep_one φ
  map_mul' := gnsRep_mul φ
  map_zero' := by simp [gnsRep, gnsPreRepCLM, gnsPreRep, gnsLeftAction]
  map_add' := gnsRep_add φ
  commutes' := fun c => by simp [Algebra.algebraMap_eq_smul_one, gnsRep_smul, gnsRep_one]
  map_star' := gnsRep_star φ
```

---

## Phase 6: Main GNS Theorems

### File: `Main/VectorState.lean` (Target: 50-70 LOC)

**Mathematical Content:**
The fundamental identity `φ(a) = ⟨Ω_φ, π_φ(a) Ω_φ⟩`.

**Key Theorem:**
```lean
/-- The GNS vector state identity: φ(a) = ⟨Ω_φ, π_φ(a) Ω_φ⟩. -/
theorem gns_vector_state (a : A) : φ a = ⟪Ω_ φ, gnsRep φ a (Ω_ φ)⟫ := by
  -- ⟨Ω_φ, π(a)Ω_φ⟩ = ⟨[1], [a·1]⟩ = ⟨[1], [a]⟩ = φ(1* · a) = φ(a)
  simp [gnsCyclicVector, gnsRep_cyclicVector]
  simp [gnsHilbertSpace.inner_embed, gnsInner_mk]
  simp [star_one, one_mul]

/-- The GNS representation recovers the original state. -/
theorem gns_state_recovery :
    (fun a => ⟪Ω_ φ, gnsRep φ a (Ω_ φ)⟫) = φ :=
  funext (gns_vector_state φ)
```

---

### File: `Main/Uniqueness.lean` (Target: 70-90 LOC)

**Mathematical Content:**
Any cyclic representation giving the same vector state is unitarily equivalent.

**Key Theorem:**
```lean
/-- GNS uniqueness: cyclic representations are unitarily equivalent. -/
theorem gns_uniqueness
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hξ_norm : ‖ξ‖ = 1)
    (hξ_cyclic : DenseRange (fun a => π a ξ))
    (hξ_state : ∀ a, ⟪ξ, π a ξ⟫ = φ a) :
    ∃ U : gnsHilbertSpace φ ≃ₗᵢ[ℂ] H,
      U (Ω_ φ) = ξ ∧
      ∀ a, U ∘L gnsRep φ a = π a ∘L U := by
  -- Define U₀ : A/N_φ → H by U₀[a] = π(a)ξ
  -- U₀ is well-defined: [a] = [b] → π(a)ξ = π(b)ξ
  -- U₀ is isometric: ‖U₀[a]‖ = ‖π(a)ξ‖ = √⟨ξ, π(a*a)ξ⟩ = √φ(a*a) = ‖[a]‖
  -- U₀ extends to isometry U : H_φ → H
  -- U is surjective by cyclicity of ξ
  -- Intertwining: U(π_φ(a)·) = π(a)(U·) by density
  ...

/-- The unitary intertwiner between cyclic representations. -/
noncomputable def gnsUnitary
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hξ_norm : ‖ξ‖ = 1)
    (hξ_cyclic : DenseRange (fun a => π a ξ))
    (hξ_state : ∀ a, ⟪ξ, π a ξ⟫ = φ a) :
    gnsHilbertSpace φ ≃ₗᵢ[ℂ] H := ...
```

---

### File: `Main/Theorem.lean` (Target: 40-60 LOC)

**Mathematical Content:**
The main GNS construction theorem combining all results.

**Main Theorem:**
```lean
/-- The Gelfand-Naimark-Segal Construction.

Given a state φ on a C*-algebra A, there exists:
1. A Hilbert space H_φ
2. A *-representation π_φ : A → B(H_φ)
3. A cyclic unit vector Ω_φ ∈ H_φ

Such that φ(a) = ⟨Ω_φ, π_φ(a) Ω_φ⟩ for all a ∈ A.

Moreover, any other cyclic representation with this property is unitarily equivalent.
-/
theorem gns_construction (A : Type*) [CStarAlgebra A] (φ : State A) :
    ∃ (H : Type*) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H),
    ∃ (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H),
      ‖Ω‖ = 1 ∧
      (∀ a, φ a = ⟪Ω, π a Ω⟫) ∧
      DenseRange (fun a => π a Ω) :=
  ⟨gnsHilbertSpace φ, inferInstance, inferInstance, inferInstance,
   gnsStarAlgHom φ, Ω_ φ,
   gnsCyclicVector_norm φ, gns_vector_state φ, gnsCyclicVector_span_dense φ⟩

/-- GNS representation is injective (faithful) when the state is faithful. -/
theorem gns_faithful (hφ : ∀ a, φ (star a * a) = 0 → a = 0) :
    Function.Injective (gnsStarAlgHom φ) := ...
```

---

## Estimated Effort

| Phase | Files | LOC | Difficulty |
|-------|-------|-----|------------|
| 1. States | 3 | 150-180 | Medium |
| 2. Null Space | 3 | 160-200 | Medium |
| 3. Pre-Hilbert | 3 | 190-250 | Medium-Hard |
| 4. Hilbert Space | 2 | 100-140 | Easy (mathlib does work) |
| 5. Representation | 4 | 250-330 | Hard |
| 6. Main Theorems | 3 | 160-220 | Medium |

**Total: 18 files, ~1000-1300 LOC**

---

## Dependencies

```
State/Basic ─────────────────────────────────┐
    │                                        │
    ▼                                        │
State/Positivity                             │
    │                                        │
    ▼                                        │
State/CauchySchwarz                          │
    │                                        │
    ▼                                        │
NullSpace/Basic ◄────────────────────────────┘
    │
    ▼
NullSpace/LeftIdeal
    │
    ▼
NullSpace/Quotient
    │
    ├──────────────────────┐
    ▼                      ▼
PreHilbert/InnerProduct    PreHilbert/Seminorm
    │                      │
    └─────────┬────────────┘
              ▼
      PreHilbert/Positive
              │
              ▼
    HilbertSpace/Completion
              │
              ├─────────────────────────────┐
              ▼                             ▼
    HilbertSpace/CyclicVector    Representation/PreRep
              │                             │
              │                             ▼
              │                  Representation/Bounded
              │                             │
              │                             ▼
              │                  Representation/Extension
              │                             │
              └──────────┬──────────────────┘
                         ▼
              Representation/Star
                         │
                         ▼
               Main/VectorState
                         │
                         ▼
               Main/Uniqueness
                         │
                         ▼
                 Main/Theorem
```

---

## Getting Started

1. **Create directory structure:**
   ```bash
   mkdir -p AfTests/GNS/{State,NullSpace,PreHilbert,HilbertSpace,Representation,Main}
   ```

2. **Start with `State/Basic.lean`** - foundational, minimal dependencies

3. **Test mathlib imports early:**
   ```lean
   import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
   import Mathlib.Analysis.CStarAlgebra.Classes
   import Mathlib.Algebra.Order.Module.PositiveLinearMap
   #check CStarAlgebra
   #check PositiveLinearMap
   ```

4. **Use `sorry` liberally in Phase 1** to establish API, then fill in proofs
