# Jordan Algebra Learnings

Research findings from formalizing Jordan algebras in Lean 4.

## Mathlib Jordan Content (as of v4.26.0)

### What Exists

| File | Content |
|------|---------|
| `Mathlib/Algebra/Jordan/Basic.lean` | `IsJordan`, `IsCommJordan` axioms |
| `Mathlib/Algebra/Symmetrized.lean` | `SymAlg` construction: `a ∘ b = ½(ab + ba)` |
| `Mathlib/Algebra/Ring/CentroidHom.lean` | Centroid homomorphisms |

**Key Difference from af-tests:**
- Mathlib uses property-based `IsJordan` (non-unital, unbundled)
- af-tests uses bundled `JordanAlgebra` (unital, over ℝ)

### What's Missing in Mathlib

1. Formally real Jordan algebras
2. Spectral theorem for Jordan algebras
3. Exceptional Jordan algebras (e.g., 3×3 octonion matrices)
4. Positivity cones in Jordan algebras

---

## Spectral Theorem Options

### Option A: Concrete (Hermitian Matrices)

Use existing mathlib infrastructure:

```lean
-- Key theorems for Hermitian matrices
Matrix.IsHermitian.spectral_theorem           -- Diagonalization
Matrix.IsHermitian.eigenvalues                -- Real eigenvalues
Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg  -- A ≥ 0 ↔ λᵢ ≥ 0
```

**Pros:** Already proven, well-tested
**Cons:** Only works for matrix algebras, not abstract Jordan algebras

### Option B: Axiomatize Spectral Decomposition

Add axiom to `FormallyRealJordan`:

```lean
class FormallyRealJordan (J : Type*) [JordanAlgebra J] where
  sq_sum_eq_zero_iff : ∀ a : J, jsq a = 0 → a = 0
  -- NEW: Spectral decomposition exists
  spectral_decomp : ∀ a : J, ∃ (n : ℕ) (e : Fin n → J) (λ : Fin n → ℝ),
    CSOI e ∧ a = ∑ i, λ i • e i
```

**Pros:** Clean abstraction, enables proofs
**Cons:** Must verify axiom for each concrete algebra

### Option C: Prove Spectral Theorem (Koecher-Vinberg)

Full proof requires:
1. Finite-dimensional assumption
2. Trace form positive-definiteness
3. Idempotent theory
4. Peirce decomposition

**Pros:** Most complete
**Cons:** ~500+ LOC, major undertaking

### Recommendation

**Option A for matrix algebras** (eliminates sorries in concrete cases)
**Option B for abstract theory** (clean axiomatization)

---

## FormallyRealJordan: Direct Proofs for Concrete Types

### Current Status (Session 50)

All concrete Jordan algebras now prove `FormallyRealJordan` **directly**, without
using the sorry-containing `of_sq_eq_zero` theorem:

| Type | File | Method |
|------|------|--------|
| `HermitianMatrix n 𝕜` | `Matrix/FormallyReal.lean` | Matrix order + `sum_eq_zero_iff_of_nonneg` |
| `SpinFactor n` | `SpinFactor/FormallyReal.lean` | Scalar part ≥ 0 + `sum_eq_zero_iff_of_nonneg` |
| `QuaternionHermitianMatrix n` | `Quaternion/FormallyReal.lean` | normSq ≥ 0 + `sum_eq_zero_iff_of_nonneg` |

### Key Pattern

For each concrete type, prove that Jordan squares have a "non-negative" component:
1. For matrices: `A*A` is positive semidefinite
2. For spin factors: `(sq x).1 = x.1² + ⟨x.2, x.2⟩ ≥ 0`
3. For quaternion matrices: `(A*A)ᵢᵢ = Σⱼ normSq(Aᵢⱼ) ≥ 0`

Then use mathlib's `Finset.sum_eq_zero_iff_of_nonneg` to conclude that if sum = 0,
each term = 0.

### Abstract Sorries (Known Gap)

The remaining sorries are in the **abstract** case only:
1. `FormallyReal/Def.lean:74-79` - `of_sq_eq_zero`
2. `FormallyReal/Spectrum.lean:158` - `spectral_sq_eigenvalues_nonneg`

### Key Mathlib Theorems for Spectral Properties

```lean
-- From Mathlib.Analysis.Matrix.Spectrum
Matrix.IsHermitian.spectral_theorem (hA : A.IsHermitian) :
    A = U * diagonal (eigenvalues) * U⁻¹

Matrix.IsHermitian.eigenvalues (hA : A.IsHermitian) : n → ℝ

Matrix.IsHermitian.eigenvalues_eq_zero_iff (hA : A.IsHermitian) :
    hA.eigenvalues = 0 ↔ A = 0

-- From Mathlib.LinearAlgebra.Matrix.PosDef
Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg (hA : A.IsHermitian) :
    A.PosSemidef ↔ 0 ≤ hA.eigenvalues

Matrix.PosSemidef.eigenvalues_nonneg (hA : A.PosSemidef) (i : n) :
    0 ≤ hA.isHermitian.eigenvalues i
```

### Abstract Case Strategy

For abstract Jordan algebras, the sorries require one of:

1. **Axiomatize**: Add spectral decomposition as an axiom to `FormallyRealJordan`
2. **Prove**: Full Koecher-Vinberg spectral theorem (~500+ LOC)
3. **Accept**: Leave sorries as documented gaps (abstract theory incomplete)

**Recommendation:** Accept the abstract sorries for now. The concrete cases
(Hermitian matrices) are complete, which is sufficient for most applications.

---

## Polynomial Tools Available

| Tool | File | Use |
|------|------|-----|
| `minpoly` | `FieldTheory/Minpoly/Basic.lean` | Minimal polynomial |
| `charpoly` | `LinearAlgebra/Charpoly/Basic.lean` | Characteristic polynomial |
| `LinearMap.aeval_self_charpoly` | Charpoly/Basic | Cayley-Hamilton |
| `spectralRadius` | `Analysis/Normed/Algebra/Spectrum.lean` | Spectral radius |

---

## Cone/Order Theory Available

| Concept | File | Use |
|---------|------|-----|
| `ProperCone` | `Analysis/Convex/Cone/Basic.lean` | Closed pointed cones |
| `riesz_extension` | `Analysis/Convex/Cone/Extension.lean` | Positive functional extension |
| `hyperplane_separation'` | `Analysis/Convex/Cone/InnerDual.lean` | Farkas' lemma |

---

## Diamond Problem (af-475a)

**Issue:** `JordanAlgebra (QuaternionHermitianMatrix n)` times out.

**Cause:** Generic `jordanAlgebraHermitianMatrix` requires `[Field R]`.
Quaternions are `DivisionRing` (non-commutative), causing search timeout.

**Solution Options:**
1. Define explicit instance bypassing generic path
2. Use `@[local instance]` with explicit parameters
3. Restructure typeclass hierarchy

---

## Key Import Patterns

```lean
-- For spectral theory
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Spectrum

-- For cone/positivity
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Convex.Cone.InnerDual

-- For polynomial tools
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
```

---

## Linearized Jordan Identity (Session 51)

### What We Have

The mathlib theorem `two_nsmul_lie_lmul_lmul_add_add_eq_zero` provides:
```lean
2 • (⁅L_a, L_{bc}⁆ + ⁅L_b, L_{ca}⁆ + ⁅L_c, L_{ab}⁆) = 0
```

Applied to `jsq a`, this gives `linearized_on_jsq`:
```lean
-- Relates x ∘ (Y ∘ a²) to Y ∘ (x ∘ a²)
jmul a (jmul (jmul b c) (jsq a)) - jmul (jmul b c) (jmul a (jsq a)) + ... = 0
```

### Key Theorems Added (OperatorIdentities.lean)

| Theorem | What it says |
|---------|--------------|
| `linearized_on_jsq` | The raw identity with factor of 2 |
| `linearized_core` | Same without the factor of 2 |
| `linearized_rearranged` | Sum form: `Σ x∘(Y∘a²) = Σ Y∘(x∘a²)` |

### What `linearized_jordan_aux` Needs

The `linearized_jordan_aux` theorem in FundamentalFormula.lean has structure:
```lean
-- Relates (x ∘ Y) ∘ a² to x ∘ (Y ∘ a²)
jmul (jmul a (jmul b c)) (jsq a) + ... = jmul a (jmul (jmul b c) (jsq a)) + ...
```

This is a **different** associativity question:
- `linearized_rearranged`: swaps order inside (x vs Y)
- `linearized_jordan_aux`: changes parenthesization

The first term is handled by Jordan identity. The remaining terms need a
different proof approach - possibly iterating Jordan or using a different
substitution in the linearized identity.

### Status

- **Proven**: `linearized_on_jsq`, `linearized_core`, `linearized_rearranged`
- **Needs work**: `linearized_jordan_aux` (different structure)
- **Blocked**: `fundamental_formula` depends on `linearized_jordan_aux`

---

## Related Docs

See also: `SPECTRAL_IMPLEMENTATION_PLAN.md`, `LEARNINGS_peirce.md`

## References

- Hanche-Olsen & Størmer, *Jordan Operator Algebras*
- McCrimmon, *A Taste of Jordan Algebras*
