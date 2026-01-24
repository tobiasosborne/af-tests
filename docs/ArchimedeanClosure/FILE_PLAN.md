# Archimedean Closure: Detailed File Plan

Each file ≤ 50 LOC as per project guidelines.

---

## Directory Structure

```
AfTests/ArchimedeanClosure/
├── Algebra/
│   ├── FreeStarAlgebra.lean      (50 LOC)
│   ├── QuadraticModule.lean      (50 LOC)
│   └── Archimedean.lean          (40 LOC)
├── State/
│   ├── MPositiveState.lean       (50 LOC)
│   ├── MPositiveStateProps.lean  (30 LOC)
│   └── NonEmptiness.lean         (40 LOC)
├── Boundedness/
│   ├── CauchySchwarzM.lean       (40 LOC)
│   ├── ArchimedeanBound.lean     (30 LOC)
│   └── GeneratingCone.lean       (40 LOC)
├── Topology/
│   ├── StateTopology.lean        (40 LOC)
│   ├── Compactness.lean          (40 LOC)
│   └── Continuity.lean           (30 LOC)
├── Seminorm/
│   ├── StateSeminorm.lean        (40 LOC)
│   ├── SeminormProps.lean        (30 LOC)
│   └── Closure.lean              (35 LOC)
├── Dual/
│   ├── Forward.lean              (30 LOC)
│   ├── SpanIntersection.lean     (35 LOC)
│   ├── SeparatingFunctional.lean (40 LOC)
│   ├── RieszApplication.lean     (40 LOC)
│   ├── ComplexExtension.lean     (35 LOC)
│   └── Normalization.lean        (35 LOC)
├── Representation/
│   ├── Constrained.lean          (40 LOC)
│   ├── VectorState.lean          (30 LOC)
│   └── GNSConstrained.lean       (40 LOC)
└── Main/
    ├── DualCharacterization.lean (30 LOC)
    └── Theorem.lean              (25 LOC)
```

**Total: 24 files, ~895 LOC**

---

## File Specifications

### Algebra/FreeStarAlgebra.lean (50 LOC)

```lean
/-! # Free *-Algebra with Self-Adjoint Generators -/

import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Star.Basic

/-- Free *-algebra on n self-adjoint generators over ℂ.
    Quotient of FreeAlgebra ℂ (Fin n) by star relations. -/
def FreeStarAlgebra (n : ℕ) := sorry

namespace FreeStarAlgebra
variable {n : ℕ}

instance : StarRing (FreeStarAlgebra n) := sorry

/-- The j-th generator gⱼ -/
def generator (j : Fin n) : FreeStarAlgebra n := sorry

/-- Generators are self-adjoint -/
theorem isSelfAdjoint_generator (j : Fin n) :
    IsSelfAdjoint (generator j) := sorry

/-- Algebra embedding from generators -/
def ι : Fin n → FreeStarAlgebra n := generator

/-- Universal property: lift to *-algebra homomorphisms -/
def lift {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    (f : Fin n → A) (hf : ∀ j, IsSelfAdjoint (f j)) :
    FreeStarAlgebra n →⋆ₐ[ℂ] A := sorry

theorem lift_generator {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    (f : Fin n → A) (hf : ∀ j, IsSelfAdjoint (f j)) (j : Fin n) :
    lift f hf (generator j) = f j := sorry

end FreeStarAlgebra
```

---

### Algebra/QuadraticModule.lean (50 LOC)

```lean
/-! # Quadratic Module M -/

import AfTests.ArchimedeanClosure.Algebra.FreeStarAlgebra
import Mathlib.Geometry.Convex.Cone.Basic

variable {n : ℕ}

/-- The quadratic module M = {Σ aᵢ*aᵢ + Σ bⱼₖ*gⱼbⱼₖ : finite sums} -/
def QuadraticModule (n : ℕ) : ConvexCone ℝ (FreeStarAlgebra n) where
  carrier := {m | ∃ (I J K : Finset ℕ) (a : I → FreeStarAlgebra n)
                    (b : J × K → FreeStarAlgebra n),
                m = ∑ i, star (a i) * a i +
                    ∑ jk, star (b jk) * generator jk.1 * b jk}
  smul_mem' := sorry
  add_mem' := sorry

namespace QuadraticModule

/-- Square of any element is in M -/
theorem star_mul_self_mem (a : FreeStarAlgebra n) :
    star a * a ∈ QuadraticModule n := sorry

/-- b*gⱼb is in M for any b and generator gⱼ -/
theorem star_generator_mul_mem (j : Fin n) (b : FreeStarAlgebra n) :
    star b * generator j * b ∈ QuadraticModule n := sorry

/-- M is a cone (closed under positive scaling) -/
theorem smul_mem {c : ℝ} (hc : 0 ≤ c) {m : FreeStarAlgebra n}
    (hm : m ∈ QuadraticModule n) :
    c • m ∈ QuadraticModule n := sorry

/-- M is closed under addition -/
theorem add_mem {m₁ m₂ : FreeStarAlgebra n}
    (h₁ : m₁ ∈ QuadraticModule n) (h₂ : m₂ ∈ QuadraticModule n) :
    m₁ + m₂ ∈ QuadraticModule n := sorry

end QuadraticModule
```

---

### Algebra/Archimedean.lean (40 LOC)

```lean
/-! # Archimedean Property -/

import AfTests.ArchimedeanClosure.Algebra.QuadraticModule

variable {n : ℕ}

/-- Archimedean property: ∀a, ∃N, N·1 - a*a ∈ M -/
class IsArchimedean (n : ℕ) : Prop where
  bound : ∀ a : FreeStarAlgebra n, ∃ N : ℕ, (N : ℝ) • 1 - star a * a ∈ QuadraticModule n

/-- The Archimedean bound for an element -/
noncomputable def archimedeanBound [IsArchimedean n] (a : FreeStarAlgebra n) : ℕ :=
  Nat.find (IsArchimedean.bound a)

/-- The Archimedean bound works -/
theorem archimedeanBound_spec [IsArchimedean n] (a : FreeStarAlgebra n) :
    (archimedeanBound a : ℝ) • 1 - star a * a ∈ QuadraticModule n :=
  Nat.find_spec (IsArchimedean.bound a)

/-- Consequence: a*a is bounded by N·1 in spectral order -/
theorem star_mul_self_le_bound [IsArchimedean n] (a : FreeStarAlgebra n) :
    star a * a ≤ (archimedeanBound a : ℝ) • 1 := sorry

end
```

---

### State/MPositiveState.lean (50 LOC)

```lean
/-! # M-Positive States -/

import AfTests.ArchimedeanClosure.Algebra.QuadraticModule

variable {n : ℕ}

/-- An M-positive state: linear functional with φ(1)=1 and φ(m)≥0 for m∈M -/
structure MPositiveState (n : ℕ) where
  toFun : FreeStarAlgebra n →ₗ[ℂ] ℂ
  map_one : toFun 1 = 1
  map_m_nonneg : ∀ m ∈ QuadraticModule n, 0 ≤ (toFun m).re
  map_m_real : ∀ m ∈ QuadraticModule n, (toFun m).im = 0

namespace MPositiveState

instance : FunLike (MPositiveState n) (FreeStarAlgebra n) ℂ where
  coe φ := φ.toFun
  coe_injective' := sorry

variable (φ : MPositiveState n)

@[simp] theorem apply_one : φ 1 = 1 := φ.map_one

theorem apply_m_nonneg {m : FreeStarAlgebra n} (hm : m ∈ QuadraticModule n) :
    0 ≤ (φ m).re := φ.map_m_nonneg m hm

theorem apply_m_real {m : FreeStarAlgebra n} (hm : m ∈ QuadraticModule n) :
    (φ m).im = 0 := φ.map_m_real m hm

/-- φ(a*a).re ≥ 0 since a*a ∈ M -/
theorem apply_star_mul_self_nonneg (a : FreeStarAlgebra n) :
    0 ≤ (φ (star a * a)).re :=
  φ.apply_m_nonneg (QuadraticModule.star_mul_self_mem a)

end MPositiveState

/-- The set S_M of all M-positive states -/
def MPositiveStateSet (n : ℕ) : Set (MPositiveState n) := Set.univ
```

---

### State/MPositiveStateProps.lean (30 LOC)

```lean
/-! # Properties of M-Positive States -/

import AfTests.ArchimedeanClosure.State.MPositiveState

variable {n : ℕ} (φ : MPositiveState n)

/-- φ(a*) = conj(φ(a)) - conjugate symmetry -/
theorem MPositiveState.map_star (a : FreeStarAlgebra n) :
    φ (star a) = starRingEnd ℂ (φ a) := sorry

/-- φ(a) is real when a is self-adjoint -/
theorem MPositiveState.apply_real_of_isSelfAdjoint {a : FreeStarAlgebra n}
    (ha : IsSelfAdjoint a) : (φ a).im = 0 := sorry

/-- Linearity -/
theorem MPositiveState.map_add (a b : FreeStarAlgebra n) :
    φ (a + b) = φ a + φ b := φ.toFun.map_add a b

theorem MPositiveState.map_smul (c : ℂ) (a : FreeStarAlgebra n) :
    φ (c • a) = c * φ a := φ.toFun.map_smul c a
```

---

### State/NonEmptiness.lean (40 LOC)

```lean
/-! # Non-emptiness of S_M -/

import AfTests.ArchimedeanClosure.State.MPositiveState

variable {n : ℕ}

/-- Scalar extraction functional: φ₀(a) = coefficient of empty word -/
noncomputable def scalarExtraction : FreeStarAlgebra n →ₗ[ℂ] ℂ := sorry

/-- Scalar extraction gives 1 on the unit -/
theorem scalarExtraction_one : scalarExtraction (1 : FreeStarAlgebra n) = 1 := sorry

/-- Scalar extraction is nonnegative on sums of squares -/
theorem scalarExtraction_star_mul_self_nonneg (a : FreeStarAlgebra n) :
    0 ≤ (scalarExtraction (star a * a)).re := sorry

/-- Scalar extraction vanishes on generator products -/
theorem scalarExtraction_star_gen_mul (j : Fin n) (b : FreeStarAlgebra n) :
    scalarExtraction (star b * generator j * b) = 0 := sorry

/-- The scalar extraction is M-positive -/
theorem scalarExtraction_mpositive :
    ∃ φ : MPositiveState n, True := sorry

/-- S_M is nonempty -/
theorem MPositiveStateSet_nonempty : (MPositiveStateSet n).Nonempty := sorry
```

---

### Boundedness/CauchySchwarzM.lean (40 LOC)

```lean
/-! # Cauchy-Schwarz for M-Positive States -/

import AfTests.ArchimedeanClosure.State.MPositiveStateProps
import AfTests.GNS.State.CauchySchwarz  -- Reuse GNS infrastructure

variable {n : ℕ} (φ : MPositiveState n)

/-- Sesquilinear form from M-positive state -/
def MPositiveState.sesqForm (a b : FreeStarAlgebra n) : ℂ :=
  φ (star a * b)

/-- The sesquilinear form is positive semidefinite -/
theorem MPositiveState.sesqForm_nonneg (a : FreeStarAlgebra n) :
    0 ≤ (φ.sesqForm a a).re := φ.apply_star_mul_self_nonneg a

/-- Cauchy-Schwarz: |φ(b*a)|² ≤ φ(a*a)·φ(b*b) -/
theorem MPositiveState.cauchy_schwarz (a b : FreeStarAlgebra n) :
    Complex.normSq (φ (star b * a)) ≤
      (φ (star a * a)).re * (φ (star b * b)).re := sorry

/-- Corollary: |φ(a)|² ≤ φ(a*a) -/
theorem MPositiveState.apply_sq_le (a : FreeStarAlgebra n) :
    Complex.normSq (φ a) ≤ (φ (star a * a)).re := by
  simpa using φ.cauchy_schwarz a 1
```

---

### Boundedness/ArchimedeanBound.lean (30 LOC)

```lean
/-! # Archimedean Bound for States -/

import AfTests.ArchimedeanClosure.Boundedness.CauchySchwarzM
import AfTests.ArchimedeanClosure.Algebra.Archimedean

variable {n : ℕ} [IsArchimedean n] (φ : MPositiveState n)

/-- φ(a*a) ≤ Nₐ from Archimedean property -/
theorem MPositiveState.apply_star_mul_self_le_bound (a : FreeStarAlgebra n) :
    (φ (star a * a)).re ≤ archimedeanBound a := sorry

/-- Combined bound: |φ(a)|² ≤ φ(a*a) ≤ Nₐ -/
theorem MPositiveState.apply_bound (a : FreeStarAlgebra n) :
    Complex.normSq (φ a) ≤ archimedeanBound a := by
  calc Complex.normSq (φ a)
      ≤ (φ (star a * a)).re := φ.apply_sq_le a
    _ ≤ archimedeanBound a := φ.apply_star_mul_self_le_bound a

/-- |φ(a)| ≤ √Nₐ -/
theorem MPositiveState.apply_abs_le (a : FreeStarAlgebra n) :
    Complex.abs (φ a) ≤ Real.sqrt (archimedeanBound a) := sorry
```

---

### Boundedness/GeneratingCone.lean (40 LOC)

```lean
/-! # M ∩ (A₀)_sa is Generating -/

import AfTests.ArchimedeanClosure.Algebra.QuadraticModule
import Mathlib.Algebra.Star.SelfAdjoint

variable {n : ℕ}

/-- Self-adjoint part of FreeStarAlgebra -/
def selfAdjointPart : Submodule ℝ (FreeStarAlgebra n) :=
  {a | IsSelfAdjoint a}

/-- Key identity: x = ¼(1+x)²  - ¼(1-x)² for self-adjoint x -/
theorem selfAdjoint_decomp {x : FreeStarAlgebra n} (hx : IsSelfAdjoint x) :
    x = (1/4 : ℝ) • (star (1 + x) * (1 + x)) -
        (1/4 : ℝ) • (star (1 - x) * (1 - x)) := sorry

/-- Both terms in decomposition are in M -/
theorem decomp_terms_in_M {x : FreeStarAlgebra n} (hx : IsSelfAdjoint x) :
    star (1 + x) * (1 + x) ∈ QuadraticModule n ∧
    star (1 - x) * (1 - x) ∈ QuadraticModule n := sorry

/-- M ∩ (A₀)_sa generates (A₀)_sa as differences -/
theorem quadraticModule_selfAdjoint_generating :
    ∀ x ∈ selfAdjointPart (n := n),
      ∃ m₁ m₂ ∈ QuadraticModule n ∩ selfAdjointPart, x = m₁ - m₂ := sorry
```

---

### Topology/StateTopology.lean (40 LOC)

```lean
/-! # Topology on State Space -/

import AfTests.ArchimedeanClosure.State.MPositiveState
import Mathlib.Topology.Algebra.Module.WeakDual

variable {n : ℕ}

/-- Pointwise convergence topology on functionals -/
instance : TopologicalSpace (MPositiveState n) :=
  TopologicalSpace.induced
    (fun φ a => φ a)
    (Pi.topologicalSpace)

/-- Evaluation at a is continuous -/
theorem eval_continuous (a : FreeStarAlgebra n) :
    Continuous (fun φ : MPositiveState n => φ a) :=
  continuous_induced_dom.comp (continuous_apply a)

/-- Characterization of convergence -/
theorem tendsto_iff_pointwise {ι : Type*} {l : Filter ι}
    {φ : ι → MPositiveState n} {ψ : MPositiveState n} :
    Filter.Tendsto φ l (𝓝 ψ) ↔
    ∀ a, Filter.Tendsto (fun i => φ i a) l (𝓝 (ψ a)) := sorry
```

---

### Topology/Compactness.lean (40 LOC)

```lean
/-! # Compactness of S_M -/

import AfTests.ArchimedeanClosure.Topology.StateTopology
import AfTests.ArchimedeanClosure.Boundedness.ArchimedeanBound
import Mathlib.Topology.Compactness.Compact

variable {n : ℕ} [IsArchimedean n]

/-- S_M is contained in a product of bounded disks -/
theorem stateSet_subset_product :
    MPositiveStateSet n ⊆
    {φ | ∀ a, Complex.abs (φ a) ≤ Real.sqrt (archimedeanBound a)} := sorry

/-- The product of bounded disks is compact (Tychonoff) -/
theorem product_compact :
    IsCompact {f : FreeStarAlgebra n → ℂ |
      ∀ a, Complex.abs (f a) ≤ Real.sqrt (archimedeanBound a)} := sorry

/-- S_M is closed: intersection of closed sets -/
theorem stateSet_isClosed :
    IsClosed (MPositiveStateSet n) := sorry

/-- Main result: S_M is compact -/
theorem stateSet_isCompact :
    IsCompact (MPositiveStateSet n) := sorry
```

---

### Topology/Continuity.lean (30 LOC)

```lean
/-! # Continuity of M-Positive States in Seminorm -/

import AfTests.ArchimedeanClosure.Seminorm.StateSeminorm

variable {n : ℕ} [IsArchimedean n]

/-- M-positive states are ||·||_M-continuous -/
theorem MPositiveState.continuous_seminorm (φ : MPositiveState n) :
    ∀ a, Complex.abs (φ a) ≤ stateSeminorm a := sorry

/-- Lipschitz bound: |φ(a) - φ(b)| ≤ ||a - b||_M -/
theorem MPositiveState.lipschitz (φ : MPositiveState n) (a b : FreeStarAlgebra n) :
    Complex.abs (φ a - φ b) ≤ stateSeminorm (a - b) := sorry
```

---

### Seminorm/StateSeminorm.lean (40 LOC)

```lean
/-! # The State Seminorm ||·||_M -/

import AfTests.ArchimedeanClosure.State.MPositiveState
import Mathlib.Analysis.Seminorm

variable {n : ℕ} [IsArchimedean n]

/-- The state seminorm: ||a||_M = sup{|φ(a)| : φ ∈ S_M} -/
noncomputable def stateSeminorm : FreeStarAlgebra n → ℝ :=
  fun a => ⨆ φ : MPositiveState n, Complex.abs (φ a)

/-- The seminorm is finite -/
theorem stateSeminorm_finite (a : FreeStarAlgebra n) :
    stateSeminorm a ≤ Real.sqrt (archimedeanBound a) := sorry

/-- Seminorm is nonnegative -/
theorem stateSeminorm_nonneg (a : FreeStarAlgebra n) :
    0 ≤ stateSeminorm a := sorry

/-- Triangle inequality -/
theorem stateSeminorm_add (a b : FreeStarAlgebra n) :
    stateSeminorm (a + b) ≤ stateSeminorm a + stateSeminorm b := sorry

/-- Scalar homogeneity -/
theorem stateSeminorm_smul (c : ℂ) (a : FreeStarAlgebra n) :
    stateSeminorm (c • a) = Complex.abs c * stateSeminorm a := sorry
```

---

### Seminorm/SeminormProps.lean (30 LOC)

```lean
/-! # Properties of State Seminorm -/

import AfTests.ArchimedeanClosure.Seminorm.StateSeminorm

variable {n : ℕ} [IsArchimedean n]

/-- stateSeminorm is a Seminorm -/
noncomputable instance : Seminorm ℂ (FreeStarAlgebra n) where
  toFun := stateSeminorm
  map_zero' := sorry
  add_le' := stateSeminorm_add
  smul' := stateSeminorm_smul
  neg' := sorry

/-- Kernel of seminorm -/
def seminormKernel : Submodule ℂ (FreeStarAlgebra n) :=
  {a | stateSeminorm a = 0}

/-- Elements in kernel are annihilated by all states -/
theorem mem_kernel_iff (a : FreeStarAlgebra n) :
    a ∈ seminormKernel ↔ ∀ φ : MPositiveState n, φ a = 0 := sorry
```

---

### Seminorm/Closure.lean (35 LOC)

```lean
/-! # Closure of Quadratic Module -/

import AfTests.ArchimedeanClosure.Seminorm.SeminormProps
import Mathlib.Analysis.Convex.Cone.Closure

variable {n : ℕ} [IsArchimedean n]

/-- Closure of M in ||·||_M topology -/
def quadraticModuleClosure : Set (FreeStarAlgebra n) :=
  closure (QuadraticModule n : Set (FreeStarAlgebra n))

/-- Closure is a cone -/
theorem closure_is_cone :
    ConvexCone ℝ (FreeStarAlgebra n) := sorry

/-- Kernel is contained in closure -/
theorem kernel_subset_closure :
    (seminormKernel : Set (FreeStarAlgebra n)) ⊆ quadraticModuleClosure := sorry

/-- Closure contains M -/
theorem quadraticModule_subset_closure :
    (QuadraticModule n : Set (FreeStarAlgebra n)) ⊆ quadraticModuleClosure :=
  subset_closure
```

---

### Dual/Forward.lean (30 LOC)

```lean
/-! # Forward Direction: A ∈ M̄ ⟹ φ(A) ≥ 0 -/

import AfTests.ArchimedeanClosure.Seminorm.Closure

variable {n : ℕ} [IsArchimedean n]

/-- If A ∈ M̄, then φ(A) ≥ 0 for all M-positive states φ -/
theorem closure_implies_nonneg {A : FreeStarAlgebra n}
    (hA : IsSelfAdjoint A) (hAcl : A ∈ quadraticModuleClosure) :
    ∀ φ : MPositiveState n, 0 ≤ (φ A).re := by
  intro φ
  obtain ⟨m, hm_in_M, hm_conv⟩ := mem_closure_iff_seq.mp hAcl
  -- φ(mₙ) ≥ 0 for all n, and φ(mₙ) → φ(A)
  -- Hence φ(A) ≥ 0 by limit
  sorry
```

---

### Dual/SpanIntersection.lean (35 LOC)

```lean
/-! # M ∩ span{A} = {0} when A ∉ M̄ -/

import AfTests.ArchimedeanClosure.Dual.Forward

variable {n : ℕ} [IsArchimedean n]

/-- If A ∉ M̄, then no nonzero multiple of A is in M -/
theorem span_cap_M_trivial {A : FreeStarAlgebra n}
    (hA : IsSelfAdjoint A) (hA_not : A ∉ quadraticModuleClosure) :
    (QuadraticModule n : Set _) ∩ Submodule.span ℝ {A} = {0} := by
  ext x
  constructor
  · intro ⟨hx_M, hx_span⟩
    -- If λA ∈ M for λ > 0, then A ∈ M ⊆ M̄, contradiction
    -- If λA ∈ M for λ < 0, then -A ∈ M, so φ(-A) ≥ 0 and φ(A) ≥ 0
    -- implies φ(A) = 0 for all φ, so ||A||_M = 0, hence A ∈ M̄
    sorry
  · intro hx
    simp only [Set.mem_singleton_iff] at hx
    simp [hx]
```

---

### Dual/SeparatingFunctional.lean (40 LOC)

```lean
/-! # Constructing Separating Functional on span{A} -/

import AfTests.ArchimedeanClosure.Dual.SpanIntersection

variable {n : ℕ} [IsArchimedean n]

/-- Distance from A to closure -/
noncomputable def distToClosure {A : FreeStarAlgebra n}
    (hA_not : A ∉ quadraticModuleClosure) : ℝ :=
  sInf {stateSeminorm (A - m) | m ∈ QuadraticModule n}

/-- Distance is positive -/
theorem distToClosure_pos {A : FreeStarAlgebra n}
    (hA_not : A ∉ quadraticModuleClosure) :
    0 < distToClosure hA_not := sorry

/-- Define ψ₀ on span{A} by ψ₀(λA) = -λε -/
noncomputable def separatingOnSpan {A : FreeStarAlgebra n}
    (hA : IsSelfAdjoint A) (hA_not : A ∉ quadraticModuleClosure) :
    Submodule.span ℝ {A} →ₗ[ℝ] ℝ := sorry

/-- ψ₀ is nonnegative on M ∩ span{A} = {0} (trivially) -/
theorem separatingOnSpan_nonneg_on_M {A : FreeStarAlgebra n}
    (hA : IsSelfAdjoint A) (hA_not : A ∉ quadraticModuleClosure) :
    ∀ x ∈ (QuadraticModule n : Set _) ∩ Submodule.span ℝ {A},
      0 ≤ separatingOnSpan hA hA_not ⟨x, sorry⟩ := sorry
```

---

### Dual/RieszApplication.lean (40 LOC)

```lean
/-! # Apply Riesz Extension Theorem -/

import AfTests.ArchimedeanClosure.Dual.SeparatingFunctional
import AfTests.ArchimedeanClosure.Boundedness.GeneratingCone
import Mathlib.Analysis.Convex.Cone.Extension

variable {n : ℕ} [IsArchimedean n]

/-- Apply Riesz extension to get ψ on all of (A₀)_sa -/
theorem riesz_extend {A : FreeStarAlgebra n}
    (hA : IsSelfAdjoint A) (hA_not : A ∉ quadraticModuleClosure) :
    ∃ ψ : selfAdjointPart →ₗ[ℝ] ℝ,
      (∀ m ∈ (QuadraticModule n : Set _) ∩ selfAdjointPart, 0 ≤ ψ ⟨m, sorry⟩) ∧
      ψ ⟨A, hA⟩ < 0 := by
  -- Use generating cone property and Riesz extension
  -- M ∩ (A₀)_sa is generating for (A₀)_sa
  apply riesz_extension
  · -- nonneg condition
    sorry
  · -- dense condition: for all y, ∃x, x + y ∈ M ∩ (A₀)_sa
    -- Follows from generating property
    sorry
```

---

### Dual/ComplexExtension.lean (35 LOC)

```lean
/-! # Extend Real Functional to Complex -/

import AfTests.ArchimedeanClosure.Dual.RieszApplication

variable {n : ℕ} [IsArchimedean n]

/-- Extend ψ : (A₀)_sa → ℝ to φ : A₀ → ℂ -/
noncomputable def complexExtend
    (ψ : selfAdjointPart (n := n) →ₗ[ℝ] ℝ) :
    FreeStarAlgebra n →ₗ[ℂ] ℂ := by
  -- φ(a) = ψ(Re a) + i·ψ(Im a)
  -- where Re a = (a + a*)/2, Im a = (a - a*)/(2i)
  sorry

/-- Complex extension preserves conjugate symmetry -/
theorem complexExtend_conj_symm
    (ψ : selfAdjointPart (n := n) →ₗ[ℝ] ℝ) (a : FreeStarAlgebra n) :
    complexExtend ψ (star a) = starRingEnd ℂ (complexExtend ψ a) := sorry

/-- Complex extension is real on self-adjoints -/
theorem complexExtend_real_on_sa
    (ψ : selfAdjointPart (n := n) →ₗ[ℝ] ℝ) {a : FreeStarAlgebra n}
    (ha : IsSelfAdjoint a) :
    complexExtend ψ a = ψ ⟨a, ha⟩ := sorry
```

---

### Dual/Normalization.lean (35 LOC)

```lean
/-! # Normalize to Get M-Positive State -/

import AfTests.ArchimedeanClosure.Dual.ComplexExtension

variable {n : ℕ} [IsArchimedean n]

/-- ψ(1) > 0 from Archimedean property -/
theorem psi_one_pos
    (ψ : selfAdjointPart (n := n) →ₗ[ℝ] ℝ)
    (hψ : ∀ m ∈ (QuadraticModule n : Set _) ∩ selfAdjointPart, 0 ≤ ψ ⟨m, sorry⟩)
    (hψ_neg : ∃ A, IsSelfAdjoint A ∧ ψ ⟨A, ‹_›⟩ < 0) :
    0 < ψ ⟨1, isSelfAdjoint_one⟩ := sorry

/-- Normalized functional φ₁ = φ/ψ(1) -/
noncomputable def normalizedState
    (ψ : selfAdjointPart (n := n) →ₗ[ℝ] ℝ)
    (hψ_pos : 0 < ψ ⟨1, isSelfAdjoint_one⟩)
    (hψ : ∀ m ∈ (QuadraticModule n : Set _) ∩ selfAdjointPart, 0 ≤ ψ ⟨m, sorry⟩) :
    MPositiveState n := sorry

/-- The normalized state gives negative value on A -/
theorem normalizedState_negative {A : FreeStarAlgebra n}
    (hA : IsSelfAdjoint A) (hψ_A : ψ ⟨A, hA⟩ < 0)
    (ψ : selfAdjointPart (n := n) →ₗ[ℝ] ℝ)
    (hψ_pos : 0 < ψ ⟨1, isSelfAdjoint_one⟩) :
    (normalizedState ψ hψ_pos sorry A).re < 0 := sorry
```

---

### Main/DualCharacterization.lean (30 LOC)

```lean
/-! # Dual Characterization Theorem -/

import AfTests.ArchimedeanClosure.Dual.Forward
import AfTests.ArchimedeanClosure.Dual.Normalization

variable {n : ℕ} [IsArchimedean n]

/-- Main dual characterization: A ∈ M̄ ⟺ φ(A) ≥ 0 for all φ ∈ S_M -/
theorem dual_characterization {A : FreeStarAlgebra n} (hA : IsSelfAdjoint A) :
    A ∈ quadraticModuleClosure ↔
    ∀ φ : MPositiveState n, 0 ≤ (φ A).re := by
  constructor
  · -- Forward: closure_implies_nonneg
    exact closure_implies_nonneg hA
  · -- Backward: by contradiction using Riesz extension
    intro hA_nonneg
    by_contra hA_not
    -- Get separating ψ with ψ(A) < 0
    obtain ⟨ψ, hψ_nonneg, hψ_A_neg⟩ := riesz_extend hA hA_not
    -- Normalize to get φ₁ ∈ S_M with φ₁(A) < 0
    have hψ_pos := psi_one_pos ψ hψ_nonneg ⟨A, hA, hψ_A_neg⟩
    have φ₁ := normalizedState ψ hψ_pos hψ_nonneg
    -- This contradicts hA_nonneg
    exact absurd (hA_nonneg φ₁) (not_le.mpr (normalizedState_negative hA hψ_A_neg ψ hψ_pos))
```

---

### Main/Theorem.lean (25 LOC)

```lean
/-! # Main Theorem: Positivity in Constrained Representations -/

import AfTests.ArchimedeanClosure.Main.DualCharacterization
import AfTests.ArchimedeanClosure.Representation.GNSConstrained

variable {n : ℕ} [IsArchimedean n]

/-- Main Theorem: A is positive in all constrained representations ⟺ A ∈ M̄ -/
theorem main_theorem {A : FreeStarAlgebra n} (hA : IsSelfAdjoint A) :
    A ∈ quadraticModuleClosure ↔
    ∀ π : ConstrainedStarRep n, 0 ≤ π.toStarAlgHom A := by
  rw [dual_characterization hA]
  constructor
  · -- If φ(A) ≥ 0 for all states, then π(A) ≥ 0 for all constrained reps
    intro hA_states π
    -- Vector states from π are M-positive
    -- Use spectral characterization of positivity
    sorry
  · -- If π(A) ≥ 0 for all constrained reps, then φ(A) ≥ 0 for all states
    intro hA_reps φ
    -- GNS representation of φ is constrained
    -- φ(A) = ⟨Ω, π_φ(A)Ω⟩ ≥ 0
    exact gns_constrained_implies_state_nonneg φ A hA hA_reps
```

---

## Summary Statistics

| Phase | Files | LOC |
|-------|-------|-----|
| Algebra | 3 | 140 |
| State | 3 | 120 |
| Boundedness | 3 | 110 |
| Topology | 3 | 110 |
| Seminorm | 3 | 105 |
| Dual | 6 | 215 |
| Representation | 3 | 110 |
| Main | 2 | 55 |
| **Total** | **26** | **~965** |
