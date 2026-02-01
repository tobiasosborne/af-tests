# Sorry Elimination Plan: Classification Simplicity

**Target files:**
- `AfTests/Jordan/Classification/RealSymmetric.lean` (1 sorry - `isSimple`)
- `AfTests/Jordan/Classification/ComplexHermitian.lean` (1 sorry - `isSimple`)

**Goal:** Prove that `RealSymmetricMatrix n` and `ComplexHermitianMatrix n` are simple Jordan algebras.

---

## 1. Current State Analysis

### 1.1 RealSymmetric.lean:75-81

```lean
instance isSimple [DecidableEq n] [Nonempty n] : IsSimpleJordan (RealSymmetricMatrix n) := by
  apply isSimpleJordan_of_ideal_trichotomy
  · exact nontrivial
  · intro I
    -- Every ideal is bottom or top
    -- Full proof requires spectral theory or matrix unit calculations
    sorry
```

**Goal state:**
```
I : JordanIdeal (RealSymmetricMatrix n)
|- I = bottom or I = top
```

### 1.2 ComplexHermitian.lean:72-78

```lean
instance isSimple [DecidableEq n] [Nonempty n] : IsSimpleJordan (ComplexHermitianMatrix n) := by
  apply isSimpleJordan_of_ideal_trichotomy
  · exact nontrivial
  · intro I
    -- Every ideal is bottom or top
    -- Full proof requires spectral theory or matrix unit calculations
    sorry
```

**Goal state:**
```
I : JordanIdeal (ComplexHermitianMatrix n)
|- I = bottom or top
```

---

## 2. Mathematical Background

### 2.1 Why Matrix Algebras are Simple

The simplicity of H_n(R) (and H_n(C)) follows from:

1. **Every nonzero Hermitian matrix has nonzero eigenvalues**
2. **Spectral decomposition:** Any Hermitian A can be written as A = sum_i lambda_i * P_i where P_i are rank-1 projections
3. **Rank-1 projections generate:** Using the Jordan product, any rank-1 projection can generate all of H_n
4. **Trace inner product:** The non-degenerate trace inner product allows "detecting" nonzero elements

### 2.2 Standard Proof Approaches

**Approach A: Matrix Units**
- Use standard matrix units E_{ij} (or their symmetrized versions)
- Show that any nonzero ideal contains a rank-1 projection
- Show rank-1 projections generate all matrix units
- Matrix units generate all of H_n

**Approach B: Spectral Decomposition**
- For nonzero A in ideal I, use spectral decomposition
- A = sum lambda_i P_i gives P_i in the ideal (by repeated multiplication)
- Rank-1 projections in I generate the identity
- Hence I = top

**Approach C: Use Mathlib's Simple Ring Theory**
- `IsSimpleRing.matrix` (Mathlib): M_n(R) is simple if R is simple
- Relate Jordan ideals to ring ideals

---

## 3. Recommended Approach: Matrix Units

Matrix units are more elementary and avoid spectral theory dependencies. This approach works for both real and complex cases.

### 3.1 Key Lemmas Needed

| Lemma | Statement | Estimated LOC |
|-------|-----------|---------------|
| `symmetric_matrix_unit` | Define symmetric matrix units S_{ij} | 15 |
| `hermitian_matrix_unit` | Define Hermitian matrix units H_{ij} | 15 |
| `ideal_contains_projection` | Nonzero ideal contains rank-1 projection | 30 |
| `projection_generates_units` | Rank-1 projection generates all matrix units | 40 |
| `units_generate_all` | Matrix units generate all of H_n | 20 |

### 3.2 Matrix Units for Symmetric/Hermitian Matrices

For real symmetric matrices:
```
S_{ii} = E_{ii}                    (diagonal)
S_{ij} = E_{ij} + E_{ji}  (i != j) (off-diagonal, symmetric)
```

For complex Hermitian matrices:
```
H_{ii} = E_{ii}                              (diagonal, real)
H_{ij}^R = E_{ij} + E_{ji}                   (off-diagonal, real part)
H_{ij}^I = i*E_{ij} - i*E_{ji}               (off-diagonal, imaginary part)
```

These form bases for the respective spaces.

---

## 4. Step-by-Step Elimination Plan

### Phase 1: Matrix Unit Infrastructure (20-30 LOC)

**File:** `AfTests/Jordan/Matrix/Units.lean` (new file)

```lean
-- Step 1.1: Define symmetric matrix units (10 LOC)
def symmetricUnit (i j : n) : RealSymmetricMatrix n :=
  if i = j then
    ⟨Matrix.single i i 1, ...⟩  -- Diagonal
  else
    ⟨Matrix.single i j 1 + Matrix.single j i 1, ...⟩  -- Off-diagonal

-- Step 1.2: Prove symmetric units are indeed symmetric (10 LOC)
theorem symmetricUnit_isSymm (i j : n) : (symmetricUnit i j).val.IsSymm

-- Step 1.3: Define Hermitian matrix units for C (10 LOC)
def hermitianUnitReal (i j : n) : ComplexHermitianMatrix n := ...
def hermitianUnitImag (i j : n) (hij : i != j) : ComplexHermitianMatrix n := ...
```

### Phase 2: Jordan Product Closure (20-30 LOC)

**File:** `AfTests/Jordan/Matrix/Units.lean` (continued)

```lean
-- Step 2.1: Product of symmetric units (15 LOC)
theorem jmul_symmetricUnit (i j k l : n) :
    jmul (symmetricUnit i j) (symmetricUnit k l) = ...

-- Step 2.2: Trace of symmetric unit products (10 LOC)
theorem trace_symmetricUnit_mul (i j k l : n) :
    Matrix.trace (symmetricUnit i j).val * (symmetricUnit k l).val = ...
```

### Phase 3: Ideal Contains Projection (30-40 LOC)

**File:** `AfTests/Jordan/Classification/RealSymmetric.lean` or new helper file

```lean
-- Step 3.1: Nonzero element has nonzero diagonal entry or off-diagonal (15 LOC)
theorem exists_nonzero_entry (A : RealSymmetricMatrix n) (hA : A != 0) :
    (exists i, A.val i i != 0) or (exists i j, i != j and A.val i j != 0)

-- Step 3.2: From nonzero entry, construct element in ideal with nonzero trace (20 LOC)
theorem ideal_has_positive_trace {I : JordanIdeal (RealSymmetricMatrix n)}
    (hI : I != bottom) :
    exists A in I, Matrix.trace A.val != 0

-- Step 3.3: From positive trace element, extract a projection (20 LOC)
theorem ideal_contains_diagonal {I : JordanIdeal (RealSymmetricMatrix n)}
    (hI : I != bottom) :
    exists i, symmetricUnit i i in I
```

### Phase 4: Projection Generates All (40-50 LOC)

```lean
-- Step 4.1: E_{ii} generates E_{ij} + E_{ji} via (E_{ii} + E_{jj}) o (E_{ij} + E_{ji}) (20 LOC)
theorem diagonal_generates_offdiagonal (i j : n) (hij : i != j)
    (hi : symmetricUnit i i in I) (hj : symmetricUnit j j in I) :
    symmetricUnit i j in I

-- Step 4.2: Two diagonals generate third via trace (25 LOC)
theorem two_diagonals_generate_all (i j : n) (hij : i != j)
    (hi : symmetricUnit i i in I) (hj : symmetricUnit j j in I) :
    forall k, symmetricUnit k k in I

-- Step 4.3: All generators means top (5 LOC)
theorem generators_imply_top (h : forall i j, symmetricUnit i j in I) : I = top
```

### Phase 5: Main Theorem Assembly (15-20 LOC)

```lean
-- Step 5.1: RealSymmetric.isSimple (10 LOC)
instance isSimple [DecidableEq n] [Nonempty n] : IsSimpleJordan (RealSymmetricMatrix n) := by
  apply isSimpleJordan_of_ideal_trichotomy
  · exact nontrivial
  · intro I
    rcases eq_or_ne I bottom with rfl | hI
    · left; rfl
    · right
      have := ideal_contains_diagonal hI
      have := two_diagonals_generate_all ...
      exact generators_imply_top ...

-- Step 5.2: ComplexHermitian.isSimple (similar) (10 LOC)
```

---

## 5. Mathlib Resources

### 5.1 Matrix Units in Mathlib

```lean
-- Mathlib.Data.Matrix.Basis
Matrix.single (i : m) (j : n) (a : alpha) : Matrix m n alpha
Matrix.single_apply_same : Matrix.single i j c i j = c
Matrix.single_apply_of_row_ne : hi : i != i' -> Matrix.single i j a i' j' = 0
Matrix.transpose_single : (Matrix.single i j a).transpose = Matrix.single j i a
```

### 5.2 Simple Ring Theory

```lean
-- Mathlib.RingTheory.SimpleRing.Matrix
IsSimpleRing.matrix : [IsSimpleRing A] -> IsSimpleRing (Matrix n n A)

-- Mathlib.RingTheory.SimpleRing.Defs
isSimpleRing_iff : IsSimpleRing R <-> IsSimpleOrder (TwoSidedIdeal R)
```

### 5.3 Matrix Trace

```lean
-- Mathlib.LinearAlgebra.Matrix.Trace
Matrix.trace : Matrix n n R -> R
Matrix.trace_add : trace (A + B) = trace A + trace B
Matrix.trace_transpose : trace A.transpose = trace A
```

---

## 6. Alternative Approach: Spectral Theory

If the matrix units approach proves difficult, the spectral approach is available:

### 6.1 Spectral Lemmas Available

```lean
-- Mathlib.LinearAlgebra.Matrix.Spectrum
Matrix.IsHermitian.spectral_theorem : A = U * diag(eigenvalues) * U*
Matrix.IsHermitian.eigenvalues : n -> R  -- Real eigenvalues

-- Mathlib.LinearAlgebra.Matrix.PosDef
Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg
```

### 6.2 Spectral Proof Outline

1. **Nonzero A in I:** Has at least one nonzero eigenvalue lambda_k
2. **Extract eigenspace projection:** P_k in I (by polynomial calculus on A)
3. **P_k is rank-1 or higher:** If rank > 1, decompose further
4. **Rank-1 projections span:** Show identity is in I

This approach is more powerful but requires more infrastructure.

---

## 7. Estimated Effort

| Phase | Description | LOC | Sessions |
|-------|-------------|-----|----------|
| 1 | Matrix Unit Infrastructure | 30 | 0.5 |
| 2 | Jordan Product Closure | 30 | 0.5 |
| 3 | Ideal Contains Projection | 40 | 1 |
| 4 | Projection Generates All | 50 | 1 |
| 5 | Main Theorem Assembly | 20 | 0.5 |
| **Total** | | **170** | **3-4** |

---

## 8. Dependencies and Blockers

### 8.1 Prerequisites (Already Available)

- `JordanIdeal` definition and basic lemmas (Ideal.lean)
- `isSimpleJordan_of_ideal_trichotomy` (Simple.lean)
- `RealSymmetricMatrix` and `ComplexHermitianMatrix` types (Matrix/*.lean)
- `HermitianMatrix.jmul` and Jordan algebra instance (Matrix/Instance.lean)
- `Matrix.single` and matrix unit lemmas (Mathlib)

### 8.2 May Need to Prove

- `Matrix.single` for Hermitian matrices is Hermitian
- Jordan product of matrix units formula
- Trace non-degeneracy in ideal detection

### 8.3 Not Blocked By

These sorries do NOT depend on the spectral theorem chain (Peirce/Primitive/Spectral).
They are independent and can be proven with elementary matrix theory.

---

## 9. Verification Checklist

After implementation, verify:

- [ ] `lake build AfTests.Jordan.Classification.RealSymmetric` passes
- [ ] `lake build AfTests.Jordan.Classification.ComplexHermitian` passes
- [ ] `grep -n "sorry" AfTests/Jordan/Classification/*.lean` returns nothing
- [ ] No new axioms introduced
- [ ] All helper lemmas are used (no dead code)

---

## 10. Session Plan

### Session A (Phase 1-2): Matrix Unit Infrastructure
- Create `AfTests/Jordan/Matrix/Units.lean`
- Define `symmetricUnit` and `hermitianUnit`
- Prove basic properties (symmetry, Hermitian, trace)

### Session B (Phase 3): Ideal Structure
- Prove `exists_nonzero_entry`
- Prove `ideal_has_positive_trace`
- Prove `ideal_contains_diagonal`

### Session C (Phase 4): Generation
- Prove `diagonal_generates_offdiagonal`
- Prove `two_diagonals_generate_all`
- Prove `generators_imply_top`

### Session D (Phase 5): Assembly
- Complete `RealSymmetricMatrix.isSimple`
- Complete `ComplexHermitianMatrix.isSimple`
- Final testing and cleanup

---

## References

- Hanche-Olsen & Stormer, "Jordan Operator Algebras", Section 3.1
- Jordan, von Neumann, Wigner, "On an Algebraic Generalization..." (1934)
- `examples3/Jordan Operator Algebras/joa-m/joa-m.md` (local copy)
