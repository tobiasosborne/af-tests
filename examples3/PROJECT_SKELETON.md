# Project Skeleton: Idel Positive Maps Formalization

> Proposed Lean 4 project structure for formalizing the Idel thesis

---

## 1. Project Layout

```
IdelPositiveMaps/
├── lakefile.lean
├── lean-toolchain
├── IdelPositiveMaps.lean              # Root import file
│
├── IdelPositiveMaps/
│   │
│   ├── Basic/                         # Core definitions (~400 LOC)
│   │   ├── PositiveMap.lean           # Positive linear maps
│   │   ├── TracePreserving.lean       # Trace-preserving property
│   │   ├── Unital.lean                # Unital maps
│   │   ├── Schwarz.lean               # Schwarz inequalities
│   │   ├── Kadison.lean               # Kadison inequality
│   │   └── Decomposable.lean          # (Co)positive, decomposable
│   │
│   ├── NormalForm/                    # Chapter 1 (~500 LOC)
│   │   ├── FullyIndecomposable.lean   # Key definition
│   │   ├── KernelReducing.lean        # Strictly kernel-reducing
│   │   ├── MenonOperator.lean         # The Menon iteration
│   │   ├── DoublyStochastic.lean      # DS map characterization
│   │   └── Theorem.lean               # Main normal form results
│   │
│   ├── Jordan/                        # Jordan algebra theory (~1200 LOC)
│   │   ├── Basic.lean                 # Extend mathlib IsJordan
│   │   ├── Product.lean               # Jordan product (A*B)
│   │   ├── FormallyReal.lean          # Σxᵢ² ≠ 0 property
│   │   ├── Simple.lean                # Simple Jordan algebras
│   │   ├── Semisimple.lean            # Direct sum structure
│   │   ├── SpinFactor/
│   │   │   ├── Def.lean               # ℝ1 + V with inner product
│   │   │   ├── SpinSystem.lean        # Generating systems
│   │   │   └── Properties.lean        # FormallyReal instance
│   │   ├── HermitianMatrices.lean     # (M_d(K))_h as JA
│   │   ├── Reversible.lean            # Reversibility condition
│   │   ├── Envelope.lean              # Enveloping C*-algebra
│   │   └── Classification.lean        # Thm 2.13 (JvNW)
│   │
│   ├── Representation/                # Chapter 3 (~1500 LOC)
│   │   ├── Basic.lean                 # Jordan representations
│   │   ├── Faithful.lean              # Embeddings
│   │   ├── Universal/
│   │   │   ├── Def.lean               # Universal envelope
│   │   │   ├── Existence.lean         # Construction
│   │   │   └── Properties.lean        # Universal property
│   │   ├── Embedding/
│   │   │   ├── RealHermitian.lean     # (M_d(ℝ))_h → M_d(ℂ)
│   │   │   ├── ComplexHermitian.lean  # (M_d(ℂ))_h → M_d(ℂ)
│   │   │   ├── Quaternion.lean        # (M_d(ℍ))_h → M_{2d}(ℂ)
│   │   │   └── SpinFactor.lean        # V_k → M_{2^n}(ℂ)
│   │   ├── SkolemNoether.lean         # Automorphisms are inner
│   │   ├── ArtinWedderburn.lean       # Semisimple decomposition
│   │   └── ClassificationComplex.lean # Thm 3.3
│   │
│   ├── Projection/                    # Chapter 4 (~1200 LOC)
│   │   ├── Basic.lean                 # Positive projections
│   │   ├── Existence.lean             # Existence theorem
│   │   ├── Uniqueness.lean            # Trace-preserving unique
│   │   ├── DirectSum.lean             # Projections on ⊕
│   │   ├── SpinFactor/
│   │   │   ├── Theory.lean            # Section 4.3
│   │   │   └── Construction.lean      # Section 4.4
│   │   ├── Reversible/
│   │   │   ├── Theory.lean            # Section 4.5
│   │   │   └── Construction.lean      # Section 4.6
│   │   └── Characterization.lean      # Chapter 5 results
│   │
│   ├── FixedPoint/                    # Chapters 2, 6 (~700 LOC)
│   │   ├── Basic.lean                 # F_T definition
│   │   ├── Properties.lean            # Lemma 2.7
│   │   ├── JordanStructure.lean       # Thm 2.26 (F_{T*} is JA)
│   │   ├── TracePreserving.lean       # Chapter 6.1
│   │   └── PeripheralSpectrum.lean    # Chapter 6.2
│   │
│   └── Appendix/                      # Technical lemmas (~300 LOC)
│       ├── SpectralProjections.lean   # Appendix A.1
│       └── OmittedProofs.lean         # Appendix A.2
│
├── docs/
│   ├── README.md                      # Project overview
│   ├── ARCHITECTURE.md                # Design decisions
│   ├── LEARNINGS.md                   # Discoveries & gotchas
│   └── chapters/
│       ├── ch1_normal_form.md
│       ├── ch2_fixed_points.md
│       ├── ch3_representations.md
│       ├── ch4_projections.md
│       ├── ch5_characterization.md
│       └── ch6_peripheral.md
│
└── test/
    └── IdelPositiveMaps/
        ├── JordanTest.lean            # Jordan algebra tests
        ├── SpinFactorTest.lean        # Spin factor examples
        └── ProjectionTest.lean        # Projection examples
```

---

## 2. Lakefile

```lean
-- lakefile.lean
import Lake
open Lake DSL

package «IdelPositiveMaps» where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"

@[default_target]
lean_lib «IdelPositiveMaps» where
  globs := #[.submodules `IdelPositiveMaps]

lean_lib «test» where
  globs := #[.submodules `test]
```

---

## 3. Lean Toolchain

```
-- lean-toolchain
leanprover/lean4:v4.15.0
```

---

## 4. Root Import File

```lean
-- IdelPositiveMaps.lean
import IdelPositiveMaps.Basic.PositiveMap
import IdelPositiveMaps.Basic.TracePreserving
import IdelPositiveMaps.Basic.Schwarz

import IdelPositiveMaps.Jordan.Basic
import IdelPositiveMaps.Jordan.FormallyReal
import IdelPositiveMaps.Jordan.SpinFactor.Def
import IdelPositiveMaps.Jordan.Classification

import IdelPositiveMaps.Representation.Basic
import IdelPositiveMaps.Representation.Universal.Def
import IdelPositiveMaps.Representation.SkolemNoether
import IdelPositiveMaps.Representation.ClassificationComplex

import IdelPositiveMaps.Projection.Basic
import IdelPositiveMaps.Projection.Existence
import IdelPositiveMaps.Projection.SpinFactor.Construction
import IdelPositiveMaps.Projection.Reversible.Construction

import IdelPositiveMaps.FixedPoint.Basic
import IdelPositiveMaps.FixedPoint.JordanStructure
import IdelPositiveMaps.FixedPoint.PeripheralSpectrum

import IdelPositiveMaps.NormalForm.Theorem
```

---

## 5. Key File Stubs

### 5.1 Basic/PositiveMap.lean

```lean
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Positive Linear Maps on Matrix Algebras

This file defines positive linear maps between matrix algebras and
establishes their basic properties.

## Main definitions

* `Matrix.IsPositiveMap`: A linear map that preserves positive semidefiniteness
* `Matrix.IsUnital`: A map satisfying T(1) = 1
* `Matrix.IsTracePreserving`: A map satisfying tr(T(A)) = tr(A)
* `Matrix.IsDoublyStochastic`: Unital and trace-preserving

## Main results

* Positive maps are Hermitian-preserving
* Composition of positive maps is positive

## References

* [Idel, On the structure of positive maps, Chapter 2]
-/

namespace Matrix

variable {n : Type*} [DecidableEq n] [Fintype n]

/-- A linear map between matrix algebras is positive if it preserves
    positive semidefiniteness. -/
def IsPositiveMap (T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) : Prop :=
  ∀ A : Matrix n n ℂ, A.PosSemidef → (T A).PosSemidef

/-- A positive map preserves Hermitian matrices. -/
theorem IsPositiveMap.isHermitian_of_isHermitian {T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hT : IsPositiveMap T) {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (T A).IsHermitian := by
  sorry -- Decompose A = A⁺ - A⁻ into positive parts

/-- A linear map is unital if T(1) = 1. -/
def IsUnital (T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) : Prop :=
  T 1 = 1

/-- A linear map is trace-preserving if tr(T(A)) = tr(A). -/
def IsTracePreserving (T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) : Prop :=
  ∀ A, trace (T A) = trace A

/-- A map is doubly stochastic if it is both unital and trace-preserving. -/
def IsDoublyStochastic (T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) : Prop :=
  IsUnital T ∧ IsTracePreserving T

end Matrix
```

### 5.2 Jordan/Basic.lean

```lean
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Mathlib.Algebra.Jordan.Basic
import Mathlib.Algebra.Star.SelfAdjoint

/-!
# Jordan Algebras: Extended Theory

This file extends mathlib's `IsJordan` with additional structure theory
needed for the classification of fixed point spaces.

## Main definitions

* `JordanAlgebra`: A bundled Jordan algebra structure
* `jordanProd`: The Jordan product A * B = (AB + BA) / 2
* `JordanSubalgebra`: A subalgebra closed under Jordan product

## Main results

* `JordanAlgebra.instOfMatrix`: Matrices form a Jordan algebra
* `selfAdjoint_jordanProd_selfAdjoint`: SA * SA is self-adjoint

## References

* [Idel, On the structure of positive maps, Section 2.1]
* [Hanche-Olsen & Størmer, Jordan Operator Algebras]
-/

variable {R : Type*} [CommRing R] [Algebra ℝ R]

/-- The Jordan product of two elements: A * B = (AB + BA) / 2 -/
def jordanProd {A : Type*} [Ring A] [Algebra R A] (a b : A) : A :=
  (1/2 : R) • (a * b + b * a)

notation:70 a " ∘ᴶ " b => jordanProd a b

/-- A Jordan algebra is a commutative algebra satisfying the Jordan identity. -/
class JordanAlgebra (J : Type*) extends AddCommGroup J, Module ℝ J where
  jordanMul : J → J → J
  jordanMul_comm : ∀ a b, jordanMul a b = jordanMul b a
  jordan_identity : ∀ a b, jordanMul (jordanMul a b) (jordanMul a a) =
                           jordanMul a (jordanMul b (jordanMul a a))
  one : J
  one_jordanMul : ∀ a, jordanMul one a = a

namespace JordanAlgebra

variable {J : Type*} [JordanAlgebra J]

instance : One J := ⟨JordanAlgebra.one⟩

/-- Jordan multiplication is bilinear. -/
theorem jordanMul_add_left (a b c : J) :
    jordanMul (a + b) c = jordanMul a c + jordanMul b c := by
  sorry

end JordanAlgebra
```

### 5.3 Jordan/SpinFactor/Def.lean

```lean
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import IdelPositiveMaps.Jordan.Basic

/-!
# Spin Factors

This file defines spin factors, one of the five types of simple formally
real Jordan algebras.

## Main definitions

* `SpinFactor V`: The spin factor ℝ·1 ⊕ V for inner product space V
* `SpinFactor.jordanMul`: The Jordan product (α,v) * (β,w) = (αβ + ⟨v,w⟩, αw + βv)

## Main results

* `SpinFactor.instJordanAlgebra`: Spin factors are Jordan algebras
* `SpinFactor.instFormallyReal`: Spin factors are formally real

## References

* [Idel, On the structure of positive maps, Definition 2.14]
* [Hanche-Olsen & Størmer, Jordan Operator Algebras, Chapter 6]
-/

/-- A spin factor is ℝ ⊕ V where V is a real inner product space,
    with Jordan product (α,v) * (β,w) = (αβ + ⟨v,w⟩, αw + βv). -/
structure SpinFactor (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  scalar : ℝ
  vector : V

namespace SpinFactor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

instance : AddCommGroup (SpinFactor V) where
  add := fun ⟨a, v⟩ ⟨b, w⟩ => ⟨a + b, v + w⟩
  zero := ⟨0, 0⟩
  neg := fun ⟨a, v⟩ => ⟨-a, -v⟩
  add_assoc := by intros; ext <;> simp [add_assoc]
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_comm := by intros; ext <;> simp [add_comm]
  add_left_neg := by intros; ext <;> simp

instance : Module ℝ (SpinFactor V) where
  smul := fun r ⟨a, v⟩ => ⟨r * a, r • v⟩
  one_smul := by intros; ext <;> simp
  mul_smul := by intros; ext <;> simp [mul_assoc, mul_smul]
  smul_zero := by intros; ext <;> simp
  smul_add := by intros; ext <;> simp [mul_add, smul_add]
  add_smul := by intros; ext <;> simp [add_mul, add_smul]
  zero_smul := by intros; ext <;> simp

/-- The Jordan product on a spin factor. -/
def jordanMul (x y : SpinFactor V) : SpinFactor V :=
  ⟨x.scalar * y.scalar + inner x.vector y.vector,
   x.scalar • y.vector + y.scalar • x.vector⟩

instance : JordanAlgebra (SpinFactor V) where
  jordanMul := jordanMul
  jordanMul_comm := by
    intro ⟨a, v⟩ ⟨b, w⟩
    simp only [jordanMul]
    ext
    · ring
    · simp [add_comm]
  jordan_identity := by
    intro ⟨a, v⟩ ⟨b, w⟩
    sorry -- Main Jordan identity verification
  one := ⟨1, 0⟩
  one_jordanMul := by
    intro ⟨a, v⟩
    simp [jordanMul, inner_zero_right]

/-- The dimension of a spin factor V_n is n + 1. -/
def dim (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℕ :=
  FiniteDimensional.finrank ℝ V + 1

end SpinFactor
```

### 5.4 FixedPoint/JordanStructure.lean

```lean
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import IdelPositiveMaps.Basic.Schwarz
import IdelPositiveMaps.Jordan.Basic

/-!
# Fixed Point Spaces are Jordan Algebras

This file proves the main structure theorem: the fixed point space of the
adjoint of a positive unital map is a Jordan algebra.

## Main results

* `FixedPointSpace.instJordanAlgebra`: F_{T*} is a Jordan algebra
* `FixedPointSpace.instFormallyReal`: (F_{T*})_h is formally real

## References

* [Idel, On the structure of positive maps, Theorem 2.26]
-/

variable {n : Type*} [DecidableEq n] [Fintype n]

/-- The fixed point space of a linear map. -/
def FixedPointSpace (T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) : Submodule ℂ (Matrix n n ℂ) where
  carrier := {A | T A = A}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at *
    rw [ha, hb]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, map_smul] at *
    rw [ha]

namespace FixedPointSpace

variable {T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}

/-- Fixed point space is †-closed. -/
theorem conjTranspose_mem (hT : Matrix.IsPositiveMap T) {A : FixedPointSpace T} :
    Aᴴ ∈ FixedPointSpace T := by
  sorry -- Uses that positive maps are Hermitian-preserving

/-- If T has a full-rank fixed point, then F_{T*} is a Jordan algebra. -/
theorem instJordanAlgebra (hT : Matrix.IsPositiveMap T) (hUnital : Matrix.IsUnital T)
    (hFullRank : ∃ ρ : Matrix n n ℂ, ρ.PosSemidef ∧ ρ.rank = Fintype.card n ∧ T ρ = ρ) :
    JordanAlgebra (FixedPointSpace (LinearMap.adjoint T)) where
  jordanMul := fun A B => ⟨jordanProd A.1 B.1, by sorry⟩
  jordanMul_comm := by sorry
  jordan_identity := by sorry
  one := ⟨1, by sorry⟩
  one_jordanMul := by sorry

end FixedPointSpace
```

---

## 6. Development Checklist

### Phase 1: Setup & Basics (Day 1)
- [ ] Initialize lake project
- [ ] Configure mathlib dependency
- [ ] Create file structure
- [ ] Implement Basic/PositiveMap.lean
- [ ] Implement Basic/Schwarz.lean
- [ ] Implement Jordan/Basic.lean

### Phase 2: Jordan Theory (Day 1-2)
- [ ] Implement Jordan/FormallyReal.lean
- [ ] Implement Jordan/SpinFactor/Def.lean
- [ ] Implement Jordan/Reversible.lean
- [ ] Implement Jordan/Classification.lean (structure)

### Phase 3: Representations (Day 2-3)
- [ ] Implement Representation/Basic.lean
- [ ] Implement Representation/Universal/Def.lean
- [ ] Implement Representation/Embedding/Quaternion.lean
- [ ] Implement Representation/Embedding/SpinFactor.lean
- [ ] Implement Representation/SkolemNoether.lean
- [ ] Implement Representation/ArtinWedderburn.lean

### Phase 4: Projections (Day 3-4)
- [ ] Implement Projection/Basic.lean
- [ ] Implement Projection/Existence.lean
- [ ] Implement Projection/SpinFactor/*.lean
- [ ] Implement Projection/Reversible/*.lean

### Phase 5: Fixed Points & Normal Forms (Day 4-5)
- [ ] Implement FixedPoint/JordanStructure.lean
- [ ] Implement FixedPoint/PeripheralSpectrum.lean
- [ ] Implement NormalForm/*.lean

### Phase 6: Integration (Day 5-6)
- [ ] Complete all sorries
- [ ] Add docstrings
- [ ] Write tests
- [ ] Documentation

---

## 7. Mathlib Imports by File

| File | Key Mathlib Imports |
|------|---------------------|
| Basic/PositiveMap | `Matrix.PosDef`, `CStarAlgebra.Matrix` |
| Basic/Schwarz | `InnerProductSpace.Basic` |
| Jordan/Basic | `Algebra.Jordan.Basic`, `Star.SelfAdjoint` |
| Jordan/SpinFactor | `InnerProductSpace.Basic` |
| Jordan/Classification | `Algebra.Quaternion` |
| Representation/Universal | `Algebra.FreeAlgebra` |
| Representation/SpinEmbed | `CliffordAlgebra.Basic` |
| Projection/Basic | `LinearAlgebra.Projection` |
| FixedPoint/Basic | `Order.FixedPoints` |

---

*Project skeleton for Idel thesis formalization.*
