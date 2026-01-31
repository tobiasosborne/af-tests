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
- **Proven**: `four_variable_identity`, `operator_formula` (Session 56, see below)
- **Needs work**: `linearized_jordan_aux` (different structure)
- **Blocked**: `fundamental_formula` depends on `linearized_jordan_aux`

---

## ⚠️ CRITICAL: Bilinear Identity is FALSE (Session 54)

### The Conjecture (WRONG)

The operator calculus chain (af-gmzr → af-dmot → af-secn) assumed:
```
2⋅a∘((ab)∘(ac)) = (ab)∘(a∘(ac)) + (ac)∘(a∘(ab))
```

**This identity is NOT TRUE in general Jordan algebras.**

### Impact

| Issue | Status | Notes |
|-------|--------|-------|
| af-gmzr | ✅ Valid | `[L_{a²}, L_b] = 2[L_a, L_{ab}]` is correct |
| af-dmot | ❌ Invalid | `linearized_jordan_aux` proof strategy wrong |
| af-secn | ❌ Blocked | `fundamental_formula` depends on af-dmot |
| spectral_sq_eigenvalues_nonneg | ⚠️ Check | May depend on this chain |

### What Went Wrong

1. Identity was **verified in 1D** (commutative case) ✓
2. Assumed to generalize to non-commutative Jordan algebras
3. **Not a consequence** of Jordan identity or linearizations

### Next Steps

1. Search Hanche-Olsen & Størmer for correct operator identities
2. Find alternative proof of fundamental_formula in literature
3. Re-evaluate the entire spectral theory dependency chain
4. See issue **af-hhwi** (P0)

---

## Related Docs

See also: `SPECTRAL_IMPLEMENTATION_PLAN.md`, `LEARNINGS_peirce.md`

---

## Hanche-Olsen Operator Identities (Session 56)

### Identities Formalized in `LinearizedJordan.lean`

| Identity | Reference | Lean Name | Status |
|----------|-----------|-----------|--------|
| Four-variable identity | H-O 2.34 | `four_variable_identity` | ✓ Proven |
| Operator formula | H-O 2.35 | `operator_formula` | ✓ Proven |
| T_a, T_{a²} commute | H-O 2.4.1 | `L_L_jsq_comm` | ✓ Proven |

### Four-Variable Identity (2.34)

```
a ∘ ((b∘c) ∘ d) + b ∘ ((c∘a) ∘ d) + c ∘ ((a∘b) ∘ d)
  = (b∘c) ∘ (a∘d) + (c∘a) ∘ (b∘d) + (a∘b) ∘ (c∘d)
```

**Key insight:** The RHS is symmetric in all four variables. This symmetry is
what enables deriving identity (2.35).

**Proof technique:**
1. Apply linearized Jordan identity (2.33) to element d
2. Extract element-wise equation by canceling the factor of 2
3. Rearrange terms using `sub_eq_zero`

### Operator Formula (2.35)

```
T_a T_{b∘c} + T_b T_{c∘a} + T_c T_{a∘b} = T_{a∘(b∘c)} + T_b T_a T_c + T_c T_a T_b
```

**Proof technique:**
1. Use four_variable_identity with original variables (gives LHS = RHS_sym)
2. Use four_variable_identity with a↔d swapped (gives different LHS = same RHS_sym)
3. Conclude the two LHS expressions are equal
4. Apply commutativity to transform one LHS to the desired form

### Power Associativity (Corollary)

From (2.35), setting b = a^{n-2}, c = a gives that T_{a^n} is a polynomial
in T_a and T_{a²}. Since T_a and T_{a²} commute (proven as `L_L_jsq_comm`),
all powers T_{a^k} commute with each other. This proves Jordan algebras are
power associative.

### Proof Patterns for Non-Commutative Algebra

**Challenge:** Standard tactics like `ring` and `linarith` don't work for
Jordan algebras because multiplication isn't associative.

**Working patterns:**

1. **For additive goals with differences:**
   ```lean
   have hsum : expr = 0 := by ...
   have hgoal : LHS - RHS = 0 := by convert hsum using 1; abel
   exact sub_eq_zero.mp hgoal
   ```

2. **For commutativity rewrites:**
   ```lean
   conv_lhs =>
     rw [jmul_comm a b]  -- Comment what this does
     rw [jmul_comm (jmul x y) z]  -- Outer product commutativity
   ```

3. **Canceling factor of 2:**
   ```lean
   have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
   have : (2 : ℕ) • expr = 0 := by ...
   rwa [two_nsmul, ← two_smul ℝ, smul_eq_zero_iff_right h2] at this
   ```

---

## Simple and Reversible Jordan Algebras (Session 55)

### IsSimpleJordan

A Jordan algebra is **simple** if:
1. It is nontrivial (∃ a ≠ 0)
2. Every ideal is either ⊥ or ⊤

Key theorems in `Jordan/Simple.lean`:
- `IsSimpleJordan.jone_ne_zero` - Identity is nonzero (proved directly from nontriviality)
- `IsSimpleJordan.ideal_eq_top_of_ne_bot` - Nonzero ideals are ⊤

### IsReversible

A Jordan algebra is **reversible** if it embeds into an associative algebra A such that:
1. Jordan product preserved: f(a∘b) = ½(f(a)f(b) + f(b)f(a))
2. Image closed under reversal: abc + cba ∈ image(f)

This is stronger than being "special" (just embedding). All simple Jordan algebras
except the exceptional Albert algebra (3×3 octonion Hermitian matrices) are reversible.

### FormallyRealJordan' Instance Removed

The instance `FormallyRealJordan' → FormallyRealJordan` was **removed** because it
used sorries in `of_sq_eq_zero`. Concrete types (HermitianMatrix, SpinFactor,
QuaternionHermitianMatrix) define `FormallyRealJordan` directly.

---

## Session 57: Fundamental Jordan Identity Analysis

### What Was Proven

Added three theorems to `LinearizedJordan.lean`:

| Theorem | Statement | Notes |
|---------|-----------|-------|
| `fundamental_jordan` | `(a² ∘ b) ∘ a = a² ∘ (b ∘ a)` | Element form of H-O 2.4.2 |
| `fundamental_jordan'` | `a ∘ (a² ∘ b) = a² ∘ (a ∘ b)` | Alternative form |
| `fundamental_jordan_original` | `(a ∘ b) ∘ a² = a ∘ (b ∘ a²)` | Original Jordan axiom |

These are direct corollaries of `L_L_jsq_comm` (T_a and T_{a²} commute).

### Why `linearized_jordan_aux` Has a Sorry

**Key discovery:** The `linearized_jordan_aux` theorem requires the bilinear identity
that Session 54 showed is FALSE.

The theorem states:
```
(a(bc))a² + (b(ac))a² + (c(ab))a² = a((bc)a²) + b((ac)a²) + c((ab)a²)
```

**Analysis:**
- First term `(a(bc))a² = a((bc)a²)` by Jordan identity ✓
- Other terms require: `(b(ac))a² = b((ac)a²)` and `(c(ab))a² = c((ab)a²)`
- These are NOT Jordan identity instances!

Using `operator_commutator_jsq`: `[L_{a²}, L_b] = 2[L_a, L_{ab}]`, we can show the
remaining terms require:
```
2·a((ab)(ac)) = (ab)(a(ac)) + (ac)(a(ab))
```

**This is exactly the bilinear identity from Session 54 that was proven FALSE.**

### Path Forward for U Fundamental Formula

The U fundamental formula `U_{U_a(b)} = U_a ∘ U_b ∘ U_a` requires one of:

1. **MacDonald's theorem** (af-3c28): Polynomial identities linear in one variable
   that hold in special Jordan algebras hold in all Jordan algebras
2. **Direct proof**: ~2 page calculation in McCrimmon's book
3. **Leave as sorry**: Status quo, acceptable for abstract theory

**Recommendation:** Focus on MacDonald's theorem (af-3c28) as it enables many
other results and is a foundational tool.

---

## Session 58: Square Roots in Formally Real Jordan Algebras

### File Created: `FormallyReal/Square.lean`

Created 115-line file defining square roots for positive elements.

### Main Definitions

| Definition | Type | Description |
|------------|------|-------------|
| `IsPositiveSqrt a b` | `Prop` | `b² = a` and `b` is positive (sum of squares) |
| `HasPositiveSqrt a` | `Prop` | `∃ b, IsPositiveSqrt a b` |

### Theorems Proven (0 sorries)

| Theorem | Statement |
|---------|-----------|
| `isPositiveSqrt_zero` | `0` has `0` as positive square root |
| `isPositiveSqrt_jone` | `1` has `1` as positive square root (if `1` is positive) |
| `PositiveElement.of_hasPositiveSqrt` | If `a` has a positive sqrt, then `a` is positive |

### Theorems with Sorries (2)

| Theorem | Needs |
|---------|-------|
| `isPositiveSqrt_unique` | Full uniqueness proof (currently partial: shows `(b-c)(b+c) = 0`) |
| `HasPositiveSqrt.of_positiveElement` | Spectral theorem for existence |

### Key Proof Technique

For the partial uniqueness proof, we show:
```
(b - c)(b + c) = b² - c² = 0
```
using the expansion:
```lean
jmul (b - c) (b + c)
  = jmul b b - jmul c b + (jmul b c - jmul c c)  -- bilinearity
  = jmul b b - jmul c b + (jmul c b - jmul c c)  -- commutativity hypothesis
  = jmul b b - jmul c c                           -- abel cancellation
  = jsq b - jsq c = 0
```

The final step (concluding `b = c` from `(b-c)(b+c) = 0`) requires either:
1. `b + c` invertible (always true for positive elements in JB-algebras)
2. Power-associativity to show `(b-c)² = 0` implies `b = c`

### Connection to Spectral Theory

The H-O spectral theorem (3.2.4) states: for `a` in a JB-algebra, `C(a) ≅ C(Sp a)`.
For positive elements, `Sp a ⊆ [0,∞)`, so we can apply `√` to get the square root.

This is the foundation for:
- Order structure on JB-algebras
- Functional calculus
- The key identity `U_a b ≥ 0` for `a, b ≥ 0`

---

## Session 59: Semisimple Jordan Algebras

### File Created: `Jordan/Semisimple.lean`

Created 175-line file defining semisimple Jordan algebras.

### Main Definitions

| Definition | Type | Description |
|------------|------|-------------|
| `JordanIdeal.idealSum I K` | `JordanIdeal J` | Sum of two ideals |
| `JordanIdeal.idealInf I K` | `JordanIdeal J` | Intersection of two ideals |
| `JordanIdeal.Independent I K` | `Prop` | `idealInf I K = ⊥` |
| `JordanIdeal.IsDirectSum I K` | `Prop` | `Independent I K ∧ idealSum I K = ⊤` |
| `IsSemisimpleJordan J` | `Prop` | Every ideal has a complement |

### Key Design Decisions

1. **Complement-based definition**: We define semisimple as "every ideal has a complementary
   ideal" rather than "direct sum of simples". This is equivalent for finite-dimensional
   algebras but the complement definition is easier to work with in general.

2. **Avoided lattice notation**: Instead of using `⊔` and `⊓` notation (which requires
   lattice instances), we defined `idealSum` and `idealInf` explicitly. This keeps the
   file self-contained without needing to set up a full lattice structure.

3. **Simple implies semisimple**: In a simple algebra, every ideal is ⊥ or ⊤, so:
   - If I = ⊥, complement is ⊤ (trivially independent, sum is ⊤)
   - If I = ⊤, complement is ⊥ (trivially independent, sum is ⊤)

### Theorems Proven (0 sorries)

| Theorem | Statement |
|---------|-----------|
| `mem_idealSum` | `x ∈ I+K ↔ ∃ a ∈ I, ∃ b ∈ K, x = a + b` |
| `mem_idealInf` | `x ∈ I ∩ K ↔ x ∈ I ∧ x ∈ K` |
| `independent_iff` | `I ∩ K = ⊥ ↔ ∀ x ∈ I, x ∈ K → x = 0` |
| `isDirectSum_iff` | Characterization in terms of unique decomposition |
| `IsSemisimpleJordan.jone_ne_zero` | Identity is nonzero in semisimple algebras |
| `IsSimpleJordan.isSemisimpleJordan` | Simple algebras are semisimple |

### Future Extensions

The semisimple structure enables:
- Wedderburn-type decomposition: J ≅ J₁ × ... × Jₙ with Jᵢ simple
- Characterization: finite-dimensional semisimple ↔ no nilpotent ideals
- Product constructions: direct products of semisimple algebras

---

## References

- Hanche-Olsen & Størmer, *Jordan Operator Algebras* (see `examples3/Jordan Operator Algebras/`)
- McCrimmon, *A Taste of Jordan Algebras*
