# Jordan Algebra Infrastructure Implementation Plan

> **Target:** ~2,250 LOC in 45 granular steps (~50 LOC each)
> **Goal:** Build Jordan algebra infrastructure for Idel thesis formalization
> **Strategy:** Exploit mathlib maximally, build only what's missing

---

## Mathlib Exploitation Summary

### Available (USE DIRECTLY)
| Component | Mathlib Module | Notes |
|-----------|---------------|-------|
| Jordan axioms | `IsJordan`, `IsCommJordan` | `Mathlib.Algebra.Jordan.Basic` |
| Symmetrized product | `SymAlg`, `αˢʸᵐ` | `Mathlib.Algebra.Symmetrized` - gives `a ∘ b = ½(ab+ba)` |
| Hermitian matrices | `Matrix.IsHermitian` | Rich API in `Mathlib.LinearAlgebra.Matrix.Hermitian` |
| Self-adjoint elements | `selfAdjoint R` | `AddSubgroup`, has `Module ℝ` instance |
| Quaternions | `ℍ[R]`, `QuaternionAlgebra` | Full star algebra, C*-algebra |
| Clifford algebras | `CliffordAlgebra Q` | Quadratic forms, spin groups |
| Positive semidefinite | `Matrix.PosSemidef` | Cone structure |
| Convex cones | `ConvexCone R E` | `Mathlib.Geometry.Convex.Cone.Basic` |

### Must Build (~2,250 LOC)
- Bundled `JordanAlgebra` structure with unit
- Formally real Jordan algebras
- Simple/semisimple Jordan algebra theory
- Spin factor construction
- Quaternionic Hermitian matrix Jordan structure
- Reversibility theory
- Classification theorem (Thm 2.13)
- Universal envelope for Jordan algebras

---

## Phase 1: Core Jordan Infrastructure (6 steps, ~300 LOC)

### Step 1.1: Jordan/Basic.lean - Bundled Structure
**File:** `IdelPositiveMaps/Jordan/Basic.lean`
**LOC:** ~50
**Dependencies:** mathlib `IsCommJordan`

```lean
-- Bundled Jordan algebra with unit
class JordanAlgebra (J : Type*) extends AddCommGroup J, Module ℝ J where
  mul : J → J → J
  mul_comm : ∀ a b, mul a b = mul b a
  jordan_identity : ∀ a b, mul (mul a b) (mul a a) = mul a (mul b (mul a a))
  one : J
  one_mul : ∀ a, mul one a = a

-- Notation
scoped notation:70 a " ∘ᴶ " b => JordanAlgebra.mul a b

-- Basic lemmas
theorem mul_one (a : J) : a ∘ᴶ 1 = a
theorem mul_add_left (a b c : J) : (a + b) ∘ᴶ c = a ∘ᴶ c + b ∘ᴶ c
```

### Step 1.2: Jordan/Product.lean - Product Properties
**File:** `IdelPositiveMaps/Jordan/Product.lean`
**LOC:** ~50
**Dependencies:** Step 1.1

```lean
-- Power notation
def jpow (a : J) : ℕ → J
  | 0 => 1
  | n + 1 => a ∘ᴶ jpow a n

-- Operator multiplication
def L (a : J) : J →ₗ[ℝ] J  -- Left multiplication
def R (a : J) : J →ₗ[ℝ] J  -- Right multiplication (= L by commutativity)

-- Key: L_a and L_{a²} commute (from mathlib IsCommJordan)
theorem L_comm_L_sq (a : J) : L a ∘ₗ L (a ∘ᴶ a) = L (a ∘ᴶ a) ∘ₗ L a
```

### Step 1.3: Jordan/Subalgebra.lean - Jordan Subalgebras
**File:** `IdelPositiveMaps/Jordan/Subalgebra.lean`
**LOC:** ~50
**Dependencies:** Step 1.1

```lean
-- Jordan subalgebra
structure JordanSubalgebra (J : Type*) [JordanAlgebra J] where
  carrier : Set J
  one_mem : 1 ∈ carrier
  mul_mem : ∀ {a b}, a ∈ carrier → b ∈ carrier → a ∘ᴶ b ∈ carrier
  add_mem : ∀ {a b}, a ∈ carrier → b ∈ carrier → a + b ∈ carrier
  smul_mem : ∀ (r : ℝ) {a}, a ∈ carrier → r • a ∈ carrier

instance : SetLike (JordanSubalgebra J) J
instance : JordanAlgebra (JordanSubalgebra J)
```

### Step 1.4: Jordan/Ideal.lean - Jordan Ideals
**File:** `IdelPositiveMaps/Jordan/Ideal.lean`
**LOC:** ~50
**Dependencies:** Step 1.3

```lean
-- Jordan ideal: I with J ∘ᴶ I ⊆ I
structure JordanIdeal (J : Type*) [JordanAlgebra J] extends AddSubgroup J where
  mul_mem_left : ∀ (a : J) {b}, b ∈ carrier → a ∘ᴶ b ∈ carrier

-- Quotient Jordan algebra
instance : JordanAlgebra (J ⧸ I)

-- Kernel and image of Jordan homomorphisms
def JordanHom.ker (f : J →ᴶ K) : JordanIdeal J
def JordanHom.range (f : J →ᴶ K) : JordanSubalgebra K
```

### Step 1.5: Jordan/Simple.lean - Simple Jordan Algebras
**File:** `IdelPositiveMaps/Jordan/Simple.lean`
**LOC:** ~50
**Dependencies:** Step 1.4

```lean
-- Simple: only trivial ideals
class IsSimpleJordan (J : Type*) [JordanAlgebra J] : Prop where
  nontrivial : (1 : J) ≠ 0
  ideals_trivial : ∀ I : JordanIdeal J, I = ⊥ ∨ I = ⊤

-- Schur-type lemma
theorem JordanHom.bijective_of_simple [IsSimpleJordan J] [IsSimpleJordan K]
    (f : J →ᴶ K) (hf : f ≠ 0) : Function.Bijective f
```

### Step 1.6: Jordan/Semisimple.lean - Semisimple Structure
**File:** `IdelPositiveMaps/Jordan/Semisimple.lean`
**LOC:** ~50
**Dependencies:** Step 1.5

```lean
-- Semisimple: direct sum of simples
class IsSemisimpleJordan (J : Type*) [JordanAlgebra J] : Prop where
  exists_simple_decomp : ∃ (ι : Type) (S : ι → Type)
    [∀ i, JordanAlgebra (S i)] [∀ i, IsSimpleJordan (S i)],
    Nonempty (J ≃ᴶ ⨁ i, S i)

-- Direct sum of Jordan algebras
instance : JordanAlgebra (⨁ i, J i)

-- Simple components
def simpleComponents (J : Type*) [IsSemisimpleJordan J] : Set (JordanSubalgebra J)
```

---

## Phase 2: Formally Real Jordan Algebras (5 steps, ~250 LOC)

### Step 2.1: Jordan/FormallyReal/Def.lean - Definition
**File:** `IdelPositiveMaps/Jordan/FormallyReal/Def.lean`
**LOC:** ~50
**Dependencies:** Phase 1

```lean
-- Formally real: Σ aᵢ² = 0 ⟹ all aᵢ = 0
class FormallyRealJordan (J : Type*) [JordanAlgebra J] : Prop where
  sum_sq_eq_zero : ∀ (n : ℕ) (a : Fin n → J),
    (∑ i, a i ∘ᴶ a i) = 0 → ∀ i, a i = 0

-- Equivalent: a² = 0 ⟹ a = 0
theorem formally_real_iff_sq_eq_zero_imp_zero :
    FormallyRealJordan J ↔ ∀ a : J, a ∘ᴶ a = 0 → a = 0
```

### Step 2.2: Jordan/FormallyReal/Properties.lean - Basic Properties
**File:** `IdelPositiveMaps/Jordan/FormallyReal/Properties.lean`
**LOC:** ~50
**Dependencies:** Step 2.1

```lean
-- Formally real ⟹ characteristic 0
instance [FormallyRealJordan J] : CharZero J

-- Formally real ⟹ no nilpotents
theorem FormallyRealJordan.no_nilpotent [FormallyRealJordan J]
    (a : J) (n : ℕ) (hn : n > 0) : jpow a (2*n) = 0 → a = 0

-- Formally real is hereditary to subalgebras
instance (S : JordanSubalgebra J) [FormallyRealJordan J] : FormallyRealJordan S
```

### Step 2.3: Jordan/FormallyReal/OrderedCone.lean - Positivity Cone
**File:** `IdelPositiveMaps/Jordan/FormallyReal/OrderedCone.lean`
**LOC:** ~50
**Dependencies:** Step 2.2

```lean
-- Positive cone: sums of squares
def positiveCone (J : Type*) [JordanAlgebra J] : ConvexCone ℝ J where
  carrier := {a | ∃ (n : ℕ) (b : Fin n → J), a = ∑ i, b i ∘ᴶ b i}
  -- ...

-- Formally real ⟺ cone is proper (pointed)
theorem formally_real_iff_cone_proper :
    FormallyRealJordan J ↔ (positiveCone J).IsProper

-- Partial order from cone
instance [FormallyRealJordan J] : PartialOrder J
```

### Step 2.4: Jordan/FormallyReal/Spectrum.lean - Spectral Properties
**File:** `IdelPositiveMaps/Jordan/FormallyReal/Spectrum.lean`
**LOC:** ~50
**Dependencies:** Step 2.3

```lean
-- Spectrum is real for formally real JA
theorem spectrum_real [FormallyRealJordan J] [FiniteDimensional ℝ J]
    (a : J) : spectrum ℝ (L a) ⊆ Set.range (algebraMap ℝ ℂ)

-- Spectral radius equals operator norm
theorem spectralRadius_eq_norm [FormallyRealJordan J]
    (a : J) : spectralRadius ℝ (L a) = ‖L a‖
```

### Step 2.5: Jordan/FormallyReal/Square.lean - Square Roots
**File:** `IdelPositiveMaps/Jordan/FormallyReal/Square.lean`
**LOC:** ~50
**Dependencies:** Step 2.4

```lean
-- Positive elements have square roots
theorem exists_sqrt [FormallyRealJordan J] [FiniteDimensional ℝ J]
    (a : J) (ha : a ∈ positiveCone J) : ∃ b : J, b ∘ᴶ b = a

-- Square root is unique in positive cone
theorem sqrt_unique [FormallyRealJordan J]
    (a b c : J) (hb : b ∈ positiveCone J) (hc : c ∈ positiveCone J)
    (hb' : b ∘ᴶ b = a) (hc' : c ∘ᴶ c = a) : b = c
```

---

## Phase 3: Hermitian Matrix Jordan Algebras (6 steps, ~300 LOC)

### Step 3.1: Jordan/Matrix/JordanProduct.lean - Jordan Product
**File:** `IdelPositiveMaps/Jordan/Matrix/JordanProduct.lean`
**LOC:** ~50
**Dependencies:** mathlib `Matrix.IsHermitian`

```lean
-- Jordan product on matrices: A ∘ B = (AB + BA) / 2
def Matrix.jordanMul (A B : Matrix n n R) : Matrix n n R :=
  (1/2 : R) • (A * B + B * A)

-- Hermitian * Hermitian under Jordan product is Hermitian
theorem IsHermitian.jordanMul (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A.jordanMul B).IsHermitian

-- Jordan product is commutative
theorem Matrix.jordanMul_comm (A B : Matrix n n R) :
    A.jordanMul B = B.jordanMul A
```

### Step 3.2: Jordan/Matrix/Instance.lean - JordanAlgebra Instance
**File:** `IdelPositiveMaps/Jordan/Matrix/Instance.lean`
**LOC:** ~50
**Dependencies:** Step 3.1

```lean
-- The type of Hermitian matrices
abbrev HermitianMatrix (n : Type*) (R : Type*) [Star R] [DecidableEq n] [Fintype n] :=
  {A : Matrix n n R // A.IsHermitian}

-- JordanAlgebra instance
instance : JordanAlgebra (HermitianMatrix n ℂ) where
  mul := fun A B => ⟨A.1.jordanMul B.1, A.2.jordanMul B.2⟩
  mul_comm := by intros; ext; apply Matrix.jordanMul_comm
  jordan_identity := by sorry -- Key proof
  one := ⟨1, isHermitian_one⟩
  one_mul := by sorry
```

### Step 3.3: Jordan/Matrix/RealHermitian.lean - Real Symmetric
**File:** `IdelPositiveMaps/Jordan/Matrix/RealHermitian.lean`
**LOC:** ~50
**Dependencies:** Step 3.2

```lean
-- (M_n(ℝ))_h = symmetric matrices
abbrev SymmetricMatrix (n : Type*) [DecidableEq n] [Fintype n] :=
  HermitianMatrix n ℝ

-- Equivalently: A = Aᵀ
theorem symmetric_iff_transpose (A : Matrix n n ℝ) :
    A.IsHermitian ↔ A = Aᵀ

instance : JordanAlgebra (SymmetricMatrix n)

-- Dimension
theorem SymmetricMatrix.finrank [Fintype n] :
    FiniteDimensional.finrank ℝ (SymmetricMatrix n) = n * (n + 1) / 2
```

### Step 3.4: Jordan/Matrix/ComplexHermitian.lean - Complex Hermitian
**File:** `IdelPositiveMaps/Jordan/Matrix/ComplexHermitian.lean`
**LOC:** ~50
**Dependencies:** Step 3.2

```lean
-- (M_n(ℂ))_h as real Jordan algebra
abbrev ComplexHermitianMatrix (n : Type*) [DecidableEq n] [Fintype n] :=
  HermitianMatrix n ℂ

instance : JordanAlgebra (ComplexHermitianMatrix n)

-- Real vector space structure
instance : Module ℝ (ComplexHermitianMatrix n)

-- Dimension
theorem ComplexHermitianMatrix.finrank [Fintype n] :
    FiniteDimensional.finrank ℝ (ComplexHermitianMatrix n) = n^2
```

### Step 3.5: Jordan/Matrix/FormallyReal.lean - Formally Real Proof
**File:** `IdelPositiveMaps/Jordan/Matrix/FormallyReal.lean`
**LOC:** ~50
**Dependencies:** Steps 3.3, 3.4, Phase 2

```lean
-- Real symmetric matrices are formally real
instance : FormallyRealJordan (SymmetricMatrix n)

-- Complex Hermitian matrices are formally real
instance : FormallyRealJordan (ComplexHermitianMatrix n)

-- Key lemma: A² = 0 for Hermitian ⟹ A = 0
theorem Hermitian.sq_eq_zero_iff (A : HermitianMatrix n ℂ) :
    A.1 * A.1 = 0 ↔ A = 0
```

### Step 3.6: Jordan/Matrix/Trace.lean - Trace Inner Product
**File:** `IdelPositiveMaps/Jordan/Matrix/Trace.lean`
**LOC:** ~50
**Dependencies:** Step 3.5

```lean
-- Inner product: ⟨A, B⟩ = tr(AB)
def HermitianMatrix.inner (A B : HermitianMatrix n ℂ) : ℝ :=
  (Matrix.trace (A.1 * B.1)).re

instance : InnerProductSpace ℝ (HermitianMatrix n ℂ)

-- Cauchy-Schwarz
theorem HermitianMatrix.inner_mul_le_norm_mul_norm ...
```

---

## Phase 4: Quaternionic Hermitian Matrices (5 steps, ~250 LOC)

### Step 4.1: Jordan/Quaternion/Hermitian.lean - Definition
**File:** `IdelPositiveMaps/Jordan/Quaternion/Hermitian.lean`
**LOC:** ~50
**Dependencies:** mathlib `Quaternion`, `Matrix.IsHermitian`

```lean
-- Quaternionic Hermitian: A = A^† where † uses quaternion conjugate
abbrev QuaternionHermitianMatrix (n : Type*) [DecidableEq n] [Fintype n] :=
  HermitianMatrix n ℍ[ℝ]

-- Star on quaternion matrices
instance : Star (Matrix n n ℍ[ℝ]) := ⟨Matrix.conjTranspose⟩

-- Basic properties
theorem QuaternionHermitianMatrix.diagonal_real (A : QuaternionHermitianMatrix n) (i : n) :
    (A.1 i i).re = A.1 i i
```

### Step 4.2: Jordan/Quaternion/JordanProduct.lean - Product
**File:** `IdelPositiveMaps/Jordan/Quaternion/JordanProduct.lean`
**LOC:** ~50
**Dependencies:** Step 4.1

```lean
-- Jordan product (same formula, but quaternions don't commute!)
-- A ∘ B = (AB + BA) / 2 still works because we symmetrize

-- The symmetrization lands in Hermitian matrices
theorem QuaternionHermitian.jordanMul_hermitian
    (A B : QuaternionHermitianMatrix n) :
    ((A.1 * B.1 + B.1 * A.1) / 2).IsHermitian
```

### Step 4.3: Jordan/Quaternion/Instance.lean - JordanAlgebra
**File:** `IdelPositiveMaps/Jordan/Quaternion/Instance.lean`
**LOC:** ~50
**Dependencies:** Step 4.2

```lean
instance : JordanAlgebra (QuaternionHermitianMatrix n) where
  mul := fun A B => ⟨(A.1 * B.1 + B.1 * A.1) / 2, ...⟩
  jordan_identity := by sorry -- Requires careful computation
  -- ...

-- Real module structure
instance : Module ℝ (QuaternionHermitianMatrix n)
```

### Step 4.4: Jordan/Quaternion/FormallyReal.lean - Formally Real
**File:** `IdelPositiveMaps/Jordan/Quaternion/FormallyReal.lean`
**LOC:** ~50
**Dependencies:** Step 4.3

```lean
instance : FormallyRealJordan (QuaternionHermitianMatrix n)

-- Dimension
theorem QuaternionHermitianMatrix.finrank [Fintype n] :
    FiniteDimensional.finrank ℝ (QuaternionHermitianMatrix n) = n * (2*n - 1)
```

### Step 4.5: Jordan/Quaternion/Embedding.lean - Complex Embedding
**File:** `IdelPositiveMaps/Jordan/Quaternion/Embedding.lean`
**LOC:** ~50
**Dependencies:** Step 4.4

```lean
-- Standard embedding: ℍ → M_2(ℂ)
def Quaternion.toComplexMatrix : ℍ[ℝ] →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ

-- Extends to: M_n(ℍ) → M_{2n}(ℂ)
def QuaternionMatrix.toComplexMatrix :
    Matrix n n ℍ[ℝ] →ₐ[ℝ] Matrix (n × Fin 2) (n × Fin 2) ℂ

-- Preserves Hermitian structure
theorem QuaternionHermitian.embedding_isHermitian (A : QuaternionHermitianMatrix n) :
    (QuaternionMatrix.toComplexMatrix A.1).IsHermitian
```

---

## Phase 5: Spin Factors (7 steps, ~350 LOC)

### Step 5.1: Jordan/SpinFactor/Def.lean - Definition
**File:** `IdelPositiveMaps/Jordan/SpinFactor/Def.lean`
**LOC:** ~50
**Dependencies:** mathlib `InnerProductSpace`

```lean
-- Spin factor: ℝ·1 ⊕ V
structure SpinFactor (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  scalar : ℝ
  vector : V

-- Notation
notation "V_" n => SpinFactor (EuclideanSpace ℝ (Fin n))

-- AddCommGroup instance
instance : AddCommGroup (SpinFactor V)

-- Module ℝ instance
instance : Module ℝ (SpinFactor V)
```

### Step 5.2: Jordan/SpinFactor/Product.lean - Jordan Product
**File:** `IdelPositiveMaps/Jordan/SpinFactor/Product.lean`
**LOC:** ~50
**Dependencies:** Step 5.1

```lean
-- Jordan product: (α, v) ∘ (β, w) = (αβ + ⟨v,w⟩, αw + βv)
def SpinFactor.mul (x y : SpinFactor V) : SpinFactor V :=
  ⟨x.scalar * y.scalar + ⟪x.vector, y.vector⟫_ℝ,
   x.scalar • y.vector + y.scalar • x.vector⟩

-- Commutativity is immediate
theorem SpinFactor.mul_comm (x y : SpinFactor V) : x.mul y = y.mul x
```

### Step 5.3: Jordan/SpinFactor/Instance.lean - JordanAlgebra
**File:** `IdelPositiveMaps/Jordan/SpinFactor/Instance.lean`
**LOC:** ~50
**Dependencies:** Step 5.2

```lean
instance : JordanAlgebra (SpinFactor V) where
  mul := SpinFactor.mul
  mul_comm := SpinFactor.mul_comm
  jordan_identity := by
    -- Key computation using inner product properties
    intro ⟨a, v⟩ ⟨b, w⟩
    simp only [SpinFactor.mul]
    ext
    · ring  -- scalar component
    · -- vector component: uses bilinearity
      sorry
  one := ⟨1, 0⟩
  one_mul := by intro x; simp [SpinFactor.mul, inner_zero_right]
```

### Step 5.4: Jordan/SpinFactor/FormallyReal.lean - Formally Real
**File:** `IdelPositiveMaps/Jordan/SpinFactor/FormallyReal.lean`
**LOC:** ~50
**Dependencies:** Step 5.3

```lean
instance : FormallyRealJordan (SpinFactor V) := by
  constructor
  intro n a hsum
  -- If Σ (aᵢ, vᵢ)² = 0, then Σ (aᵢ² + ‖vᵢ‖²) = 0
  -- Each term is nonnegative, so all = 0
  sorry

-- Dimension: dim(V_n) = n + 1
theorem SpinFactor.finrank [FiniteDimensional ℝ V] :
    FiniteDimensional.finrank ℝ (SpinFactor V) =
    FiniteDimensional.finrank ℝ V + 1
```

### Step 5.5: Jordan/SpinFactor/SpinSystem.lean - Spin Systems
**File:** `IdelPositiveMaps/Jordan/SpinFactor/SpinSystem.lean`
**LOC:** ~50
**Dependencies:** Step 5.4

```lean
-- Spin system: orthonormal vectors in V giving generators
structure SpinSystem (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  n : ℕ
  e : Fin n → V
  orthonormal : Orthonormal ℝ e

-- Generators in spin factor: eᵢ = (0, e i)
def SpinSystem.generator (S : SpinSystem V) (i : Fin S.n) : SpinFactor V :=
  ⟨0, S.e i⟩

-- Key relation: eᵢ ∘ eⱼ = δᵢⱼ · 1
theorem SpinSystem.mul_generator (S : SpinSystem V) (i j : Fin S.n) :
    S.generator i ∘ᴶ S.generator j = if i = j then 1 else 0
```

### Step 5.6: Jordan/SpinFactor/Clifford.lean - Clifford Connection
**File:** `IdelPositiveMaps/Jordan/SpinFactor/Clifford.lean`
**LOC:** ~50
**Dependencies:** Step 5.5, mathlib `CliffordAlgebra`

```lean
-- Quadratic form for spin factor
def SpinFactor.quadraticForm (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    QuadraticForm ℝ V := innerProductSpace.toQuadraticForm

-- Connection: V_n embeds into even part of Clifford algebra
def SpinFactor.toCliffordEven (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    SpinFactor V →ₐ[ℝ] CliffordAlgebra.even (SpinFactor.quadraticForm V)
```

### Step 5.7: Jordan/SpinFactor/Embedding.lean - Matrix Embedding
**File:** `IdelPositiveMaps/Jordan/SpinFactor/Embedding.lean`
**LOC:** ~50
**Dependencies:** Step 5.6

```lean
-- V_n embeds into M_{2^⌈n/2⌉}(ℂ) via Pauli matrices
-- For even n: V_n ≅ subalgebra of M_{2^{n/2}}(ℂ)
-- For odd n: V_n ≅ subalgebra of M_{2^{(n+1)/2}}(ℂ) (two copies)

def SpinFactor.toMatrix (n : ℕ) :
    SpinFactor (EuclideanSpace ℝ (Fin n)) →ᴶ HermitianMatrix (Fin (2^((n+1)/2))) ℂ

-- This is injective
theorem SpinFactor.toMatrix_injective (n : ℕ) :
    Function.Injective (SpinFactor.toMatrix n)
```

---

## Phase 6: Reversibility (4 steps, ~200 LOC)

### Step 6.1: Jordan/Reversible/Def.lean - Definition
**File:** `IdelPositiveMaps/Jordan/Reversible/Def.lean`
**LOC:** ~50
**Dependencies:** Phase 1

```lean
-- Reversible: a₁...aₙ + aₙ...a₁ ∈ J for all aᵢ ∈ J
-- (where products are in the enveloping associative algebra)

class IsReversibleJordan (J : Type*) [JordanAlgebra J] : Prop where
  reversible : ∀ (n : ℕ) (a : Fin n → J) (S : AssociativeEnvelope J),
    S.mul_seq a + S.mul_seq (a ∘ Fin.rev) ∈ J

-- Alternative: J is reversible if it's *-isomorphic to self-adjoints of a *-algebra
```

### Step 6.2: Jordan/Reversible/Properties.lean - Properties
**File:** `IdelPositiveMaps/Jordan/Reversible/Properties.lean`
**LOC:** ~50
**Dependencies:** Step 6.1

```lean
-- (M_n(ℝ))_h is reversible
instance : IsReversibleJordan (SymmetricMatrix n)

-- (M_n(ℂ))_h is reversible
instance : IsReversibleJordan (ComplexHermitianMatrix n)

-- (M_n(ℍ))_h is reversible
instance : IsReversibleJordan (QuaternionHermitianMatrix n)

-- Spin factors V_n are reversible iff n ≤ 3
theorem SpinFactor.reversible_iff (n : ℕ) :
    IsReversibleJordan (SpinFactor (EuclideanSpace ℝ (Fin n))) ↔ n ≤ 3
```

### Step 6.3: Jordan/Reversible/Envelope.lean - Enveloping Algebra
**File:** `IdelPositiveMaps/Jordan/Reversible/Envelope.lean`
**LOC:** ~50
**Dependencies:** Step 6.2

```lean
-- Enveloping C*-algebra S(J) for Jordan subalgebra J ⊆ M_d(ℂ)
def EnvelopingCStarAlgebra (J : JordanSubalgebra (HermitianMatrix n ℂ)) :
    CStarSubalgebra (Matrix n n ℂ) :=
  CStarSubalgebra.closure (Algebra.adjoin ℂ J.carrier)

-- For reversible J: J = S(J)_h
theorem reversible_iff_selfadjoint_of_envelope [IsReversibleJordan J] :
    J ≃ᴶ selfAdjoint (EnvelopingCStarAlgebra J)
```

### Step 6.4: Jordan/Reversible/Characterization.lean - Characterization
**File:** `IdelPositiveMaps/Jordan/Reversible/Characterization.lean`
**LOC:** ~50
**Dependencies:** Step 6.3

```lean
-- Theorem 3.4 from Idel: Characterization of reversibility
-- J ⊆ M_d(ℂ) is reversible iff J has no V_n (n≥4) summands

theorem reversible_iff_no_large_spin (J : JordanSubalgebra (HermitianMatrix n ℂ)) :
    IsReversibleJordan J ↔ ∀ k ≥ 4, ¬∃ (S : JordanSubalgebra J),
      S ≃ᴶ SpinFactor (EuclideanSpace ℝ (Fin k))
```

---

## Phase 7: Classification Theorem (7 steps, ~350 LOC)

### Step 7.1: Jordan/Classification/SimpleTypes.lean - List of Types
**File:** `IdelPositiveMaps/Jordan/Classification/SimpleTypes.lean`
**LOC:** ~50
**Dependencies:** Phases 3, 4, 5

```lean
-- The 5 simple formally real Jordan algebras (Theorem 2.13)
inductive SimpleJordanType where
  | realSymmetric (n : ℕ)      -- (M_n(ℝ))_h
  | complexHermitian (n : ℕ)   -- (M_n(ℂ))_h
  | quaternionHermitian (n : ℕ) -- (M_n(ℍ))_h
  | spinFactor (n : ℕ)         -- V_n (n ≥ 2)
  | albert                     -- H_3(𝕆), exceptional

-- Realize as Jordan algebra
def SimpleJordanType.toJordanAlgebra : SimpleJordanType → Type
  | realSymmetric n => SymmetricMatrix (Fin n)
  | complexHermitian n => ComplexHermitianMatrix (Fin n)
  | quaternionHermitian n => QuaternionHermitianMatrix (Fin n)
  | spinFactor n => SpinFactor (EuclideanSpace ℝ (Fin n))
  | albert => AlbertAlgebra  -- defined elsewhere
```

### Step 7.2: Jordan/Classification/RealSymmetric.lean - (M_n(ℝ))_h Simple
**File:** `IdelPositiveMaps/Jordan/Classification/RealSymmetric.lean`
**LOC:** ~50
**Dependencies:** Step 7.1

```lean
-- (M_n(ℝ))_h is simple for n ≥ 1
instance (n : ℕ) [NeZero n] : IsSimpleJordan (SymmetricMatrix (Fin n))

-- Proof sketch: only ideals are {0} and whole algebra
-- Uses that trace pairing is nondegenerate
```

### Step 7.3: Jordan/Classification/ComplexHermitian.lean - (M_n(ℂ))_h Simple
**File:** `IdelPositiveMaps/Jordan/Classification/ComplexHermitian.lean`
**LOC:** ~50
**Dependencies:** Step 7.1

```lean
-- (M_n(ℂ))_h is simple for n ≥ 1
instance (n : ℕ) [NeZero n] : IsSimpleJordan (ComplexHermitianMatrix (Fin n))
```

### Step 7.4: Jordan/Classification/QuaternionHermitian.lean - (M_n(ℍ))_h Simple
**File:** `IdelPositiveMaps/Jordan/Classification/QuaternionHermitian.lean`
**LOC:** ~50
**Dependencies:** Step 7.1

```lean
-- (M_n(ℍ))_h is simple for n ≥ 1
instance (n : ℕ) [NeZero n] : IsSimpleJordan (QuaternionHermitianMatrix (Fin n))
```

### Step 7.5: Jordan/Classification/SpinFactors.lean - V_n Simple
**File:** `IdelPositiveMaps/Jordan/Classification/SpinFactors.lean`
**LOC:** ~50
**Dependencies:** Step 7.1

```lean
-- V_n is simple for n ≥ 2
instance (n : ℕ) (hn : n ≥ 2) : IsSimpleJordan (SpinFactor (EuclideanSpace ℝ (Fin n)))

-- V_1 ≅ ℝ × ℝ (not simple, decomposes)
theorem SpinFactor_one_not_simple : ¬IsSimpleJordan (SpinFactor (EuclideanSpace ℝ (Fin 1)))
```

### Step 7.6: Jordan/Classification/AlbertAlgebra.lean - Exceptional
**File:** `IdelPositiveMaps/Jordan/Classification/AlbertAlgebra.lean`
**LOC:** ~50
**Dependencies:** Step 7.1

```lean
-- Albert algebra H_3(𝕆) - 27-dimensional exceptional Jordan algebra
-- We only need the structure, not detailed proofs for thesis

structure AlbertAlgebra where
  -- 3×3 Hermitian matrices over octonions
  -- Simplified: just declare the type

-- It exists and is simple (we won't fully prove this)
instance : JordanAlgebra AlbertAlgebra := sorry
instance : IsSimpleJordan AlbertAlgebra := sorry
instance : FormallyRealJordan AlbertAlgebra := sorry

-- Dimension
theorem AlbertAlgebra.finrank : FiniteDimensional.finrank ℝ AlbertAlgebra = 27 := sorry
```

### Step 7.7: Jordan/Classification/Theorem.lean - Main Classification
**File:** `IdelPositiveMaps/Jordan/Classification/Theorem.lean`
**LOC:** ~50
**Dependencies:** Steps 7.2-7.6

```lean
-- THEOREM 2.13: Jordan-von Neumann-Wigner Classification
-- Every simple finite-dimensional formally real Jordan algebra over ℝ
-- is isomorphic to exactly one of the 5 types

theorem jordan_classification (J : Type*) [JordanAlgebra J] [FiniteDimensional ℝ J]
    [FormallyRealJordan J] [IsSimpleJordan J] :
    ∃ t : SimpleJordanType, Nonempty (J ≃ᴶ t.toJordanAlgebra)

-- Uniqueness: the type is determined by dimension and structure
theorem jordan_classification_unique (t₁ t₂ : SimpleJordanType)
    (h : Nonempty (t₁.toJordanAlgebra ≃ᴶ t₂.toJordanAlgebra)) : t₁ = t₂
```

---

## Phase 8: Universal Envelope (5 steps, ~250 LOC)

### Step 8.1: Jordan/Envelope/Def.lean - Definition
**File:** `IdelPositiveMaps/Jordan/Envelope/Def.lean`
**LOC:** ~50
**Dependencies:** Phase 1, mathlib `FreeAlgebra`

```lean
-- Universal enveloping algebra of Jordan algebra J
-- Quotient of free associative algebra by Jordan relations

def UniversalEnvelope (J : Type*) [JordanAlgebra J] : Type* :=
  FreeAlgebra ℝ J ⧸ JordanRelations J

-- The canonical map ι : J → U(J)
def UniversalEnvelope.ι (J : Type*) [JordanAlgebra J] :
    J → UniversalEnvelope J

-- ι preserves Jordan product: ι(a∘b) = (ι(a)·ι(b) + ι(b)·ι(a))/2
```

### Step 8.2: Jordan/Envelope/Existence.lean - Construction
**File:** `IdelPositiveMaps/Jordan/Envelope/Existence.lean`
**LOC:** ~50
**Dependencies:** Step 8.1

```lean
-- U(J) is an associative algebra
instance : Ring (UniversalEnvelope J)
instance : Algebra ℝ (UniversalEnvelope J)

-- The relations
inductive JordanRelations (J : Type*) [JordanAlgebra J] :
    FreeAlgebra ℝ J → FreeAlgebra ℝ J → Prop
  | jordan_prod (a b : J) : JordanRelations
      (FreeAlgebra.ι a * FreeAlgebra.ι b + FreeAlgebra.ι b * FreeAlgebra.ι a)
      (2 • FreeAlgebra.ι (a ∘ᴶ b))
  | linear (r : ℝ) (a b : J) : JordanRelations
      (FreeAlgebra.ι (r • a + b))
      (r • FreeAlgebra.ι a + FreeAlgebra.ι b)
```

### Step 8.3: Jordan/Envelope/UniversalProperty.lean - Universal Property
**File:** `IdelPositiveMaps/Jordan/Envelope/UniversalProperty.lean`
**LOC:** ~50
**Dependencies:** Step 8.2

```lean
-- Universal property: any Jordan homomorphism to an associative algebra
-- factors uniquely through U(J)

def UniversalEnvelope.lift {A : Type*} [Ring A] [Algebra ℝ A]
    (f : J →ᴶ selfAdjoint A) : UniversalEnvelope J →ₐ[ℝ] A

theorem UniversalEnvelope.lift_ι (f : J →ᴶ selfAdjoint A) (a : J) :
    UniversalEnvelope.lift f (ι a) = f a

theorem UniversalEnvelope.lift_unique (g : UniversalEnvelope J →ₐ[ℝ] A)
    (hg : ∀ a, g (ι a) = f a) : g = UniversalEnvelope.lift f
```

### Step 8.4: Jordan/Envelope/Simple.lean - For Simple Algebras
**File:** `IdelPositiveMaps/Jordan/Envelope/Simple.lean`
**LOC:** ~50
**Dependencies:** Step 8.3, Phase 7

```lean
-- For simple J, U(J) is simple or product of two simples

-- U((M_n(ℝ))_h) ≅ M_n(ℝ)
theorem envelope_real_symmetric (n : ℕ) :
    UniversalEnvelope (SymmetricMatrix (Fin n)) ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℝ

-- U((M_n(ℂ))_h) ≅ M_n(ℂ)
theorem envelope_complex_hermitian (n : ℕ) :
    UniversalEnvelope (ComplexHermitianMatrix (Fin n)) ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ

-- U((M_n(ℍ))_h) ≅ M_n(ℍ)
theorem envelope_quaternion_hermitian (n : ℕ) :
    UniversalEnvelope (QuaternionHermitianMatrix (Fin n)) ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℍ[ℝ]
```

### Step 8.5: Jordan/Envelope/Dimension.lean - Dimension Formulas
**File:** `IdelPositiveMaps/Jordan/Envelope/Dimension.lean`
**LOC:** ~50
**Dependencies:** Step 8.4

```lean
-- Dimension formulas for universal envelopes

-- dim U(V_n) for spin factors
theorem envelope_spin_finrank (n : ℕ) :
    FiniteDimensional.finrank ℝ (UniversalEnvelope (SpinFactor (EuclideanSpace ℝ (Fin n)))) =
    if Even n then 2^n else 2^(n+1)

-- General bound
theorem envelope_finrank_le [FiniteDimensional ℝ J] :
    FiniteDimensional.finrank ℝ (UniversalEnvelope J) ≤
    (FiniteDimensional.finrank ℝ J)^2
```

---

## Summary

| Phase | Steps | LOC | Description |
|-------|-------|-----|-------------|
| 1 | 6 | 300 | Core Jordan infrastructure |
| 2 | 5 | 250 | Formally real Jordan algebras |
| 3 | 6 | 300 | Hermitian matrix Jordan algebras |
| 4 | 5 | 250 | Quaternionic Hermitian matrices |
| 5 | 7 | 350 | Spin factors |
| 6 | 4 | 200 | Reversibility |
| 7 | 7 | 350 | Classification theorem |
| 8 | 5 | 250 | Universal envelope |
| **Total** | **45** | **2,250** | |

---

## Dependencies Graph

```
Phase 1 (Core)
    ↓
Phase 2 (Formally Real)
    ↓
    ├── Phase 3 (Matrix JA) ←── mathlib Matrix.IsHermitian
    │       ↓
    ├── Phase 4 (Quaternion) ←── mathlib Quaternion
    │       ↓
    └── Phase 5 (Spin) ←── mathlib CliffordAlgebra
            ↓
        Phase 6 (Reversible)
            ↓
        Phase 7 (Classification)
            ↓
        Phase 8 (Envelope)
```

---

## Notes

1. **Mathlib exploitation**: We use `IsCommJordan`, `Matrix.IsHermitian`, `selfAdjoint`, `CliffordAlgebra`, `QuaternionAlgebra` directly
2. **Albert algebra**: We stub this as it's not needed for the thesis main results (focuses on complex subalgebras)
3. **Each step is ~50 LOC**: Fits the 200 LOC file limit with room for imports and documentation
4. **Parallel development**: Phases 3, 4, 5 can be developed in parallel after Phase 2
