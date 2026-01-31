# Jordan Algebra Learnings

Research findings from formalizing Jordan algebras in Lean 4.

---

## 🚨 CRITICAL: AXIOM GAPS (Session 67)

**AXIOMS ARE EXTREME GAPS!** Adding axioms to typeclasses without concrete instances
means theorems are vacuously true. This is WORSE than sorries.

### Current Axiom Gaps (P0 issues created)

| Class | Axiom | Issue | Status |
|-------|-------|-------|--------|
| `JordanTrace` | trace_add, trace_smul, trace_jmul_comm, trace_jone_pos | af-5zpv | NO INSTANCES |
| `JordanTrace` | trace_L_selfadjoint | af-2dzb | NO INSTANCES |
| `FormallyRealTrace` | trace_jsq_nonneg, trace_jsq_eq_zero_iff | af-pxqu | NO INSTANCES |

### Rule: NEVER add typeclass axioms without concrete instances

When adding axioms to a typeclass:
1. **IMMEDIATELY** create a concrete instance proving the axiom
2. If you can't prove it for concrete types, **DON'T ADD THE AXIOM**
3. Create a P0 issue if axiom is added without instance

### Impact

All theorems using `[JordanTrace J]` or `[FormallyRealTrace J]` are currently
vacuously true because no instances exist. This includes:
- `eigenspace_orthogonal`
- `eigenspace_traceInner_zero`
- `traceInner_jmul_left`

---

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

## Spectral Theory Roadmap (Session 59 Analysis)

### The Path to Zero Sorries

**Key insight:** Peirce decomposition (H-O Section 2.6) is a **prerequisite** for the spectral
theorem (H-O Section 3.2). The book proves Peirce first because it's the algebraic foundation.

### Beads Dependency Chain

```
af-dxb5 (P0/P1 rules) ← UNBLOCKED, START HERE
    └── af-qvqz (P1/2 rules)
            └── af-bqjd (Peirce decomposition theorem)
                    └── af-nnvl (Eigenspace definition)
                            └── af-9pfg (Eigenspace orthogonality)
                                    └── af-pyaw (Spectral theorem) [P1]
                                            └── af-4g40 (Sorry elimination) [P1]
```

### 21-Step Implementation Plan (~940 LOC total)

#### Phase 0: Foundation (~50 LOC)
| Step | File | What |
|------|------|------|
| 0.1 | `Peirce.lean:125` | `peirce_polynomial_identity`: L_e(L_e-1/2)(L_e-1)=0 |

**Technique:** Polarize Jordan identity with a→e+x, extract x-linear terms, use e²=e.

#### Phase 1: P0/P1 Rules (af-dxb5, ~130 LOC)
| Step | What | Technique |
|------|------|-----------|
| 1.1 | `peirce_mult_P0_P0` | Use linearized_jordan_operator |
| 1.2 | `peirce_mult_P1_P1` | Symmetric to P0×P0 |
| 1.3 | `peirce_mult_P0_P1 = 0` | **Hardest** - orthogonality property |

#### Phase 2: P1/2 Rules (af-qvqz, ~130 LOC)
| Step | What | Technique |
|------|------|-----------|
| 2.1 | `peirce_mult_P0_P12` | Eigenvalue algebra |
| 2.2 | `peirce_mult_P1_P12` | Eigenvalue algebra |
| 2.3 | `peirce_mult_P12_P12` | (1/2)·(1/2) → {0,1} |

#### Phase 3: Peirce Theorem (af-bqjd, ~130 LOC)
- Define `PeirceDecomposition` structure
- Prove existence and uniqueness

#### Phase 4: Eigenspaces (af-nnvl, af-9pfg, ~190 LOC)
- Define `Eigenspace a λ`
- Prove submodule properties
- Prove orthogonality and finiteness

#### Phase 5: Spectral Theorem (af-pyaw, ~180 LOC)
- Define `Spectrum a`
- Prove spectrum is real
- Prove `spectral_decomposition_exists`
- Prove `spectral_sq_eigenvalues_nonneg`

#### Phase 6: Sorry Elimination (af-4g40, ~130 LOC)
- `of_sq_eq_zero` in `FormallyReal/Def.lean`
- `isPositiveSqrt_unique` in `FormallyReal/Square.lean`
- `HasPositiveSqrt.of_positiveElement`

### Sorries by Category (Current: 25)

| Category | Count | Blocked By |
|----------|-------|------------|
| Peirce multiplication | 7 | Phase 0 (polynomial identity) |
| Primitive idempotents | 3 | Phase 1-2 |
| Formally real (abstract) | 3 | Phase 5-6 |
| Square roots | 2 | Phase 6 |
| Fundamental formula | 2 | Independent (MacDonald) |
| Operator identities | 2 | Phase 1 |
| Classification | 2 | Phase 3 |
| Other | 4 | Various |

### Critical Path

**Sessions 60-62:** Peirce polynomial + P0/P1 rules (Phase 0-1)
**Sessions 63-64:** P1/2 rules (Phase 2)
**Sessions 65-67:** Peirce theorem + eigenspaces (Phase 3-4)
**Sessions 68-70:** Spectral theorem + sorry elimination (Phase 5-6)

**Estimated:** 10-12 sessions to eliminate all spectral-chain sorries.

---

## Session 60: Peirce Polynomial Identity Proof

### The Key Identity

For idempotent `e` (e² = e), we need to prove:
```
L_e(L_e - 1/2)(L_e - 1) = 0
```
Equivalently: `2 L_e³(x) - 3 L_e²(x) + L_e(x) = 0` for all x.

### Proof Strategy (VERIFIED CORRECT)

**Use `four_variable_identity` from LinearizedJordan.lean with a = b = e, c = x, d = e:**

```
four_variable_identity e e x e gives:
e ∘ ((e ∘ x) ∘ e) + e ∘ ((x ∘ e) ∘ e) + x ∘ ((e ∘ e) ∘ e) =
(e ∘ x) ∘ (e ∘ e) + (x ∘ e) ∘ (e ∘ e) + (e ∘ e) ∘ (x ∘ e)
```

**Simplify using e² = e and jmul_comm:**
```
e ∘ ((e ∘ x) ∘ e) + e ∘ ((e ∘ x) ∘ e) + (e ∘ x) =
(e ∘ x) ∘ e + (e ∘ x) ∘ e + e ∘ (e ∘ x)
```

**Use `jmul_jmul_e_x_e` (already proven in Peirce.lean:102):**
```
(e ∘ x) ∘ e = e ∘ (e ∘ x)
```

**This gives:**
```
2 · e ∘ (e ∘ (e ∘ x)) + (e ∘ x) = 2 · e ∘ (e ∘ x) + e ∘ (e ∘ x)
2 · L_e³(x) + L_e(x) = 3 · L_e²(x)
```

**Rearranging:** `2 L_e³(x) - 3 L_e²(x) + L_e(x) = 0` ✓

### Required Import

**CRITICAL:** Peirce.lean needs `import AfTests.Jordan.LinearizedJordan` to access `four_variable_identity`.

### Implementation Notes

1. The goal after `ring_nf` has form involving `(1/2 : ℝ)` scalars
2. Need to convert between `ℕ`-smul and `ℝ`-smul using `Nat.cast_smul_eq_nsmul`
3. The `linarith` tactic should handle the arithmetic once setup correctly
4. Key lemmas needed:
   - `four_variable_identity` (LinearizedJordan.lean)
   - `jmul_jmul_e_x_e` (Peirce.lean:102)
   - `IsIdempotent` unfolding: `he : jmul e e = e`

### H-O Reference

Section 2.6.2 (page 47-48) derives this from equation (2.64):
```
T_p = U_p + ½(ι - U_p - U_p⊥) + 0·U_p⊥
```
This shows T_p has eigenvalues {0, 1/2, 1}, hence the minimal polynomial divides x(x-1/2)(x-1).

### Current State

- Added import to Peirce.lean (line 8)
- Wrote proof skeleton at lines 126-164
- **ERROR on line 144:** The rewrite `rw [jmul_comm x e, hcomm] at h4v` fails because after the first `simp` the term `jmul x e` no longer appears

### Fix for Line 144 Error

The problem is the order of simplifications. After line 138's `simp`, h4v already has `jmul e x` not `jmul x e`.

**DELETE line 144** (the problematic rw). The h4v is already in the right form after line 141.

After line 141, h4v should have form:
```
jmul e (jmul e (jmul e x)) + jmul e (jmul e (jmul e x)) + jmul e x =
jmul e (jmul e x) + jmul e (jmul e x) + jmul e (jmul e x)
```

This is exactly `2·L_e³(x) + L_e(x) = 3·L_e²(x)`, which gives the Peirce polynomial.

### Debugging Commands

```bash
# Check errors
lake build AfTests.Jordan.Peirce

# Or use lean LSP
lean_diagnostic_messages on Peirce.lean
lean_goal on specific lines to see goal state
```

### CRITICAL: linarith doesn't work on Jordan elements!

`linarith` only works on ordered rings/fields (like ℝ). Jordan algebra elements are NOT ordered, so you CANNOT use `linarith` on them.

**Instead use:**
- `abel` for additive manipulations
- `sub_eq_zero.mpr` to convert `a = b` to `a - b = 0`
- Direct `calc` chains with rewrites

### Correct Proof Pattern

The goal after `ring_nf` is:
```
jmul e (jmul e (jmul e x) - jmul e x) - (1/2) • (jmul e (jmul e x) - jmul e x) = 0
```

From h4v we have:
```
L³ + L³ + L = L² + L² + L²
```
i.e. `2·L³ + L = 3·L²`

Use `sub_eq_zero.mpr` and `abel` to rearrange:
```lean
have key : 2 • L³ - 3 • L² + L = 0 := by
  have h := h4v  -- 2·L³ + L = 3·L²
  -- convert using sub_eq_zero
  ...
```

Then expand the goal using `jmul_sub`, `smul_sub`, `sub_smul` and show it equals `key`.

### Session 60 Proof Attempt Status

**File modified:** `AfTests/Jordan/Peirce.lean` lines 126-195

**What works:**
- Import added: `import AfTests.Jordan.LinearizedJordan` (line 8)
- `four_variable_identity e e x e` gives the right identity
- `key : 2 • L³ - 3 • L² + L = 0` is proven (uses `ℕ`-smul)
- `key' : (2:ℝ) • L³ - (3:ℝ) • L² + L = 0` attempts conversion

**What's failing:**
The calc chain steps have type mismatch issues between `ℕ`-smul and `ℝ`-smul.

**Alternative approach for next agent:**

Instead of the complex calc chain, try:
```lean
-- After key' is proven with ℝ coefficients
-- Goal is: L³ - L² - ((1/2)L² - (1/2)L) = 0
-- Direct computation:
have h : jmul e (jmul e (jmul e x)) - jmul e (jmul e x) -
         ((1/2 : ℝ) • jmul e (jmul e x) - (1/2 : ℝ) • jmul e x) =
         (1/2 : ℝ) • (2 • jmul e (jmul e (jmul e x)) - 3 • jmul e (jmul e x) + jmul e x) := by
  -- Use: L³ - L² - (1/2)L² + (1/2)L = (1/2)(2L³ - 3L² + L)
  -- Verify: (1/2)*2*L³ = L³ ✓
  -- (1/2)*3*L² = (3/2)L² = L² + (1/2)L² ✓
  -- (1/2)*L = (1/2)L ✓
  module  -- or use module axioms manually
rw [h, key', smul_zero]
```

The `module` tactic might work here. Or use `simp only [smul_sub, smul_add, smul_smul]` then `norm_num` then `abel`.

---

## Session 61: Peirce Polynomial PROVEN + P0×P1 Orthogonality Strategy

### VICTORY: `peirce_polynomial_identity` Proven!

**File:** `AfTests/Jordan/Peirce.lean:126-188`

The proof is COMPLETE (0 sorries). Key technique:

1. Use `four_variable_identity e e x e` to derive `2L³ + L = 3L²`
2. Rearrange to `2L³ - 3L² + L = 0` (in ℕ-smul form)
3. Convert to ℝ-smul and show goal equals `(1/2) • (2L³ - 3L² + L) = 0`

**Working Lean patterns discovered:**
```lean
-- Convert ℕ-smul to ℝ-smul:
simp only [← Nat.cast_smul_eq_nsmul ℝ] at key

-- Derive L³ = L² - L from four_variable_identity:
have constr1 : jmul e (jmul e c) = jmul e c - c := by
  calc jmul e (jmul e c) = jmul e (jmul e c) + c - c := by abel
    _ = jmul e c - c := by rw [h4v]

-- Use jmul_sub for linearity:
jmul_sub e _ _  -- NOT jmul_sub (which doesn't exist), use rw [jmul_sub]
```

### P0×P1 Orthogonality: Mathematical Strategy DISCOVERED

**Theorem:** `peirce_mult_P0_P1` - if a ∈ P₀(e), b ∈ P₁(e), then a∘b = 0

**Proof Strategy (VERIFIED MATHEMATICALLY CORRECT):**

Let c = a∘b. Using `four_variable_identity e a b e` with e∘a = 0, e∘b = b, e² = e:

```
e ∘ ((a∘b)∘e) + a ∘ ((b∘e)∘e) + b ∘ ((e∘a)∘e) = (a∘b)∘e² + (b∘e)∘(a∘e) + (e∘a)∘(b∘e)
```

Simplifying with e∘a = 0, b∘e = b (from e∘b = b and commutativity):
```
e ∘ (c∘e) + a∘b + 0 = c∘e + 0 + 0
e ∘ (e∘c) + c = e∘c        (using jmul_comm c e = jmul e c)
```

**Key constraint:** `L_e²(c) + c = L_e(c)`, equivalently `L_e²(c) = L_e(c) - c`

**Chain of deductions:**

1. `L_e²(c) = L_e(c) - c` (from four_variable_identity)
2. `L_e³(c) = L_e(L_e(c) - c) = L_e²(c) - L_e(c) = (L_e(c) - c) - L_e(c) = -c`
3. From Peirce polynomial: `2L³ - 3L² + L = 0`
4. Substituting: `2(-c) - 3(L_e(c) - c) + L_e(c) = -2c - 3L + 3c + L = c - 2L = 0`
5. Therefore: `c = 2L_e(c)`, meaning `L_e(c) = c/2`
6. Then: `L_e²(c) = L_e(c/2) = L_e(c)/2 = c/4` (by linearity)
7. But also: `L_e²(c) = L_e(c) - c = c/2 - c = -c/2`
8. So: `c/4 = -c/2`, hence `3c/4 = 0`, therefore `c = 0` ✓

**ALTERNATIVE SHORTER PATH (discovered during debugging):**

From steps 1-4, we get `c = 2L_e(c)`.
From step 1: `L_e²(c) = L_e(c) - c`

Computing two ways:
- Way 1: `2L_e²(c) = 2L_e(L_e(c)) = L_e(2L_e(c)) = L_e(c)` (since c = 2L_e(c))
- Way 2: `2L_e²(c) = 2(L_e(c) - c) = 2L_e(c) - 2c = c - 2c = -c` (using c = 2L_e(c))

So `L_e(c) = -c`. But also `2L_e(c) = c`, so `-2c = c`, hence `3c = 0`, so `c = 0` ✓

### Lean Tactic Issues Encountered

**Problem:** Module element manipulations don't work with `linarith` or `ring`.

**Solutions found:**
- Use `abel` for additive manipulations
- Use `calc` chains with explicit rewrites
- `sub_eq_zero.mpr` / `sub_eq_zero.mp` for equality ↔ subtraction
- `smul_eq_zero.mp` to conclude element = 0 from scalar • element = 0

**Problem:** ℕ-smul vs ℝ-smul coercion issues.

**Solution:**
```lean
simp only [← Nat.cast_smul_eq_nsmul ℝ] at hypothesis
-- Converts (n : ℕ) • x to (n : ℝ) • x
```

**Problem:** `3 • x` doesn't automatically equal `x + x + x`.

**Solution:**
```lean
have h3 : (3 : ℕ) • y = y + y + y := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul]
```

### Current State of Peirce.lean

| Theorem | Status | Notes |
|---------|--------|-------|
| `peirce_polynomial_identity` | ✅ PROVEN | Lines 126-188 |
| `peirce_mult_P0_P0` | sorry | Needs similar analysis |
| `peirce_mult_P1_P1` | sorry | Needs similar analysis |
| `peirce_mult_P0_P1` | IN PROGRESS | Math correct, Lean tactics messy |
| `peirce_mult_P12_P12` | sorry | |
| `peirce_mult_P0_P12` | sorry | |
| `peirce_mult_P1_P12` | sorry | |

### Sorry Count

- **Before session:** 25 sorries
- **After session:** 24 sorries (peirce_polynomial_identity eliminated)
- **Progress on:** peirce_mult_P0_P1 (proof strategy complete, implementation partial)

### Files Modified

- `AfTests/Jordan/Peirce.lean` - peirce_polynomial_identity proven, P0_P1 work in progress
- `docs/Jordan/LEARNINGS.md` - This documentation

---

## Session 70: Research Resolution — Correct Primitive Theory from H-O

### H-O 2.9.4 — The Correct Theory

**Lemma 2.9.4 (H-O)** for finite-dimensional formally real Jordan algebras:

| Part | Statement |
|------|-----------|
| (i) | No nilpotent elements |
| (ii) | p is minimal (primitive) iff {pAp} = ℝp |
| (iii) | Every element lies in a maximal associative subalgebra ℝp₁ ⊕ ... ⊕ ℝpₙ with pairwise orthogonal primitives |
| **(iv)** | **For orthogonal primitives p, q:** a ∈ {pAq} ⟹ a² = λ(p+q) with λ ≥ 0. Either {pAq} = 0 or p, q strongly connected. |
| (v) | For primitive p and any a: {pa²p} = λp with λ ≥ 0 |
| (vi) | a = Σαᵢpᵢ (orthogonal primitives) is a square iff all αᵢ ≥ 0 |

### Key Definitions

**Strongly connected (H-O 2.8.1):** Orthogonal idempotents p, q are strongly connected if
∃v ∈ {pAq} with v² = p + q.

### Why "Primitive Dichotomy" is FALSE

The naive statement "two primitives are orthogonal or equal" fails because:
1. Two distinct primitives CAN be non-orthogonal (have nontrivial product)
2. Non-orthogonality doesn't force equality

The correct statements are:
1. In a **maximal associative subalgebra**, primitives ARE pairwise orthogonal
2. For **orthogonal** primitives, either {pAq} = 0 or strongly connected
3. In a **simple** algebra, all primitives in a CSOI are strongly connected

### Updated Primitive.lean

Replaced `primitive_dichotomy` with correct H-O theorems:
- `IsStronglyConnected` — Definition of strongly connected
- `orthogonal_primitive_peirce_sq` — a² = λ(p+q) for a ∈ {pAq}
- `orthogonal_primitive_structure` — H-O 2.9.4(iv) dichotomy

### Path Forward for Spectral Theory

The decomposition theorems `exists_primitive_decomp` and `csoi_refine_primitive`
are still valid goals — they produce **pairwise orthogonal** primitive families.
These don't need the false "primitives are orthogonal or equal" statement.

---

## Session 69: primitive_dichotomy Proof Strategy is WRONG

### 🚨 CRITICAL FINDING

**The proof strategy from Session 68 is INCORRECT.**

The claim "If `jmul e f ≠ 0`, then `jmul e f ∈ P₁(e) ∩ P₁(f)`" is **FALSE**.

For `jmul e f ∈ P₁(e)` we need `jmul e (jmul e f) = jmul e f`.
But: `jmul e (jmul e f) = (1/4)f₁₂ + f₁` while `jmul e f = (1/2)f₁₂ + f₁`.
These are equal **only if f₁₂ = 0** (f has no P₁₂(e) component).

### Counterexample

In 2×2 symmetric matrices over ℝ:
- e = diag(1,0)
- f = [[1/2,1/2],[1/2,1/2]]

Both are primitive (rank-1 projections), but:
- `jmul e f = [[1/2,1/4],[1/4,0]] ≠ 0` (not orthogonal)
- `jmul e f ≠ e` and `jmul e f ≠ f`
- `e ≠ f`

This **violates the dichotomy** as stated!

### What's Proven (3/4 cases)

| Case | Status |
|------|--------|
| `jmul e f = 0` | ✅ Orthogonal |
| `jmul e f = e` | ✅ e = f (primitivity of f) |
| `jmul e f = f` | ✅ e = f (primitivity of e) |
| `jmul e f ∉ {0,e,f}` | ❌ BLOCKED - may be impossible |

### Next Step: Research H-O (af-pdw2)

Read H-O Sections 2.9 and 3.1 to find the **correct** theorem statement.
Possible correct statements:
1. "Orthogonal or unitarily equivalent" (standard JB result)
2. Requires additional hypotheses (same spectral family)
3. Only holds for JB-algebras with completeness

---

## Session 68: Spectral Theorem Structure & Primitive.lean Analysis

### Key Finding: Peirce is Complete, Primitive is the Blocker

**Peirce.lean has 0 sorries.** All H-O Section 2.6 material is proven:
- `peirce_polynomial_identity` — L_e(L_e - 1/2)(L_e - 1) = 0
- All multiplication rules: P0×P0, P1×P1, P0×P1, P1/2×P1/2, P0×P1/2, P1×P1/2
- `peirce_decomposition` — Every element decomposes into P0 + P1/2 + P1
- `peirce_direct_sum` — The decomposition is a direct sum

### ~~Blocking Sorries: Primitive.lean (3 sorries)~~ (See Session 69 - strategy wrong)

| Theorem | What it says | ~~Proof using Peirce~~ |
|---------|--------------|-------------------|
| `primitive_dichotomy` | Two primitives are orthogonal or equal | ~~If `jmul e f ≠ 0`, then `jmul e f ∈ P₁(e) ∩ P₁(f)`.~~ **WRONG - see Session 69** |
| `exists_primitive_decomp` | Every idempotent = sum of primitives | Induction on dim. If e not primitive, ∃ proper idempotent f with `jmul e f = f`. Then e-f orthogonal to f. Apply induction. |
| `csoi_refine_primitive` | CSOI can be refined to primitive CSOI | Apply `exists_primitive_decomp` to each element. |

### Dependency Chain for Spectral Theory

```
Peirce.lean (0 sorries) ✅
    │
    ▼
Primitive.lean (3 sorries) ← CRITICAL PATH
    │
    ▼
SpectralTheorem.lean (7 sorries)
    │
    ▼
Complete spectral theory
```

### SpectralTheorem.lean Structure (Session 68)

Created 133 LOC file with:
- `spectrum a` := eigenvalueSet a (eigenvalues of L_a)
- `spectral_decomposition_exists` — needs primitive CSOI construction
- `spectrum_eq_eigenvalueSet` — uniqueness
- `spectral_sq` — a² has squared eigenvalues
- `spectrum_sq_nonneg` — PROVEN (squares are non-negative)

### Strategy for Filling Spectral Sorries

Once Primitive.lean sorries are filled:
1. `spectral_decomposition_exists`: Use `csoi_refine_primitive` on any CSOI containing
   spectral projections (from eigenspace decomposition)
2. `spectrum_eq_eigenvalueSet`: Eigenvalues of CSOI decomposition = eigenvalues of L_a
3. `spectral_sq`: Orthogonality gives (Σ λᵢ eᵢ)² = Σ λᵢ² eᵢ

---

## Session 71: Import Fix & Proof Structure for Primitives

### Import Cycle Fixed

**Problem:** Peirce.lean imported Primitive.lean, preventing Primitive.lean from using
Peirce multiplication rules.

**Solution:** Removed the unused import `import AfTests.Jordan.Primitive` from Peirce.lean.
Peirce.lean doesn't actually use anything from Primitive - it only depends on Product
and LinearizedJordan.

This enables the natural dependency:
```
LinearizedJordan.lean
    │
    ▼
Peirce.lean (Peirce multiplication rules)
    │
    ▼
Primitive.lean (uses Peirce rules for primitivity characterization)
```

### Key Helper Lemma: `primitive_peirce_one_scalar`

Added theorem statement (with sorry):
```lean
theorem primitive_peirce_one_scalar [FinDimJordanAlgebra J] [FormallyRealJordan J]
    {e : J} (he : IsPrimitive e) {x : J} (hx : x ∈ PeirceSpace e 1) :
    ∃ r : ℝ, x = r • e
```

This is H-O 2.9.4(ii): primitivity ⟺ {eAe} = ℝe

**Why it's key:** This lemma enables the proof of `orthogonal_primitive_peirce_sq`:
- For a ∈ Peirce½(e) ∩ Peirce½(f), we get a² ∈ P₀(e) ⊕ P₁(e)
- The P₁(e) component is in ℝe by this lemma
- Similarly for f

### Proof Structure for `orthogonal_primitive_peirce_sq`

The theorem is now structured with clear steps:
1. Show a ∈ PeirceSpace e (1/2) and a ∈ PeirceSpace f (1/2)
2. By `peirce_mult_P12_P12`, jsq a ∈ P₀(e) ⊕ P₁(e) and jsq a ∈ P₀(f) ⊕ P₁(f)
3. Decompose jsq a = c₀e + c₁e and jsq a = c₀f + c₁f
4. By `primitive_peirce_one_scalar`: c₁e = r₁ • e and c₁f = r₂ • f
5. Show r₁ = r₂ (remaining work)
6. Show μ ≥ 0 by formal reality (remaining work)

### Potential Circularity Concern

The proof of `primitive_peirce_one_scalar` may require showing that finite-dim
formally real Jordan algebras of dim > 1 have non-trivial idempotents. This comes
from spectral theory, creating a potential circular dependency.

**Options to investigate:**
1. Direct proof using Peirce decomposition (if P₁(e) has orthogonal elements)
2. Axiomatize for now and revisit
3. Check H-O Section 2.9 for exact proof technique

### Files Modified

- `AfTests/Jordan/Peirce.lean` — Removed unused import
- `AfTests/Jordan/Primitive.lean` — Added Peirce import, helper lemma, structured proof

---

## Session 72: Canonical H-O Proof for primitive_peirce_one_scalar

### The Theorem (H-O 2.9.4(ii))

> An idempotent p is minimal (primitive) iff {pAp} = ℝp

### H-O's Actual Proof Strategy

**Key dependency:** Lemma 2.9.3 (ring-theoretic structure theorem)

> **Lemma 2.9.3:** An Abelian ring without nilpotents satisfying DCC on ideals
> decomposes as a direct sum of fields: R = F₁ ⊕ ... ⊕ Fₙ with orthogonal
> identity elements e₁,...,eₙ.

**Proof of 2.9.4(ii):**
1. {pAp} is commutative associative (Peirce theory - we have this)
2. Has no nilpotents (formal reality, H-O 2.9.4(i) - we have this)
3. Finite-dimensional → DCC on ideals ✓
4. **Apply 2.9.3** → {pAp} = F₁ ⊕ ... ⊕ Fₙ (direct sum of fields)
5. Identity of {pAp} is p = e₁ + ... + eₙ
6. **Minimality of p** → n = 1 (otherwise eᵢ would be sub-idempotent)
7. So {pAp} is a single field F over ℝ
8. **Formally real** → F ≠ ℂ (since i² = -1 violates formal reality)
9. Only finite-dim formally real field over ℝ is ℝ itself (H-O 2.2.6)
10. Hence {pAp} = ℝp ∎

### What's Needed in Lean

1. **Lemma 2.9.3 equivalent:** "Finite-dimensional commutative ℝ-algebra without
   nilpotents is isomorphic to ℝⁿ" - check mathlib for this
2. **H-O 2.9.4(i):** "Formally real Jordan algebras have no nilpotents" -
   straightforward from definition
3. **H-O 2.2.6:** "Only finite-dim formally real fields over ℝ are ℝ" -
   standard result, may be in mathlib

### What We Proved This Session

- `spectral_sq` - structural theorem about squaring spectral decompositions
- `jsq_sum_orthog_idem` - (∑ λᵢ eᵢ)² = ∑ λᵢ² eᵢ
- `sum_jmul` - left multiplication distributes over sums

---

## Session 73: H-O Source Verification

### Verified H-O Formulas (from `examples3/Jordan Operator Algebras/joa-m/joa-m.md`)

| Equation | H-O Ref | Formula |
|----------|---------|---------|
| (2.33) | Linearized Jordan | `[T_a, T_{b∘c}] + [T_b, T_{c∘a}] + [T_c, T_{a∘b}] = 0` |
| (2.34) | Four-variable | `a∘((b∘c)∘d) + b∘((c∘a)∘d) + c∘((a∘b)∘d) = (b∘c)∘(a∘d) + ...` |
| (2.35) | Operator formula | `T_a T_{b∘c} + T_b T_{c∘a} + T_c T_{a∘b} = T_{a∘(b∘c)} + T_b T_a T_c + T_c T_a T_b` |
| (2.39) | U operator | `U_a = 2T_a² - T_{a²}` |
| (2.60) | T_p spectral | `T_p = (1/2)(ι + U_p - U_{p⊥})` |
| (2.61) | U_p idempotent | `U_p² = U_p`, `U_p U_{p⊥} = 0` |
| (2.62) | T_p U_p | `T_p U_p = U_p T_p = U_p` |
| (2.63) | Commutator | `2[T_p, T_{p∘a}] = [T_p, T_a]` |

### ⚠️ NOT DIRECTLY IN H-O (need derivation or removal)

| Theorem | File:Line | Status |
|---------|-----------|--------|
| `L_e_L_a_L_e` | OperatorIdentities.lean:170 | NOT in H-O - needs derivation from (2.35) or removal |
| `opComm_double_idempotent` | OperatorIdentities.lean:177 | Circular with above |

These theorems have sorries and claim formulas not directly stated in H-O.
They **might** be derivable from (2.35) but this needs verification.

### Rule: Verify Against Source Before Proving

Before filling a sorry:
1. **Find the exact theorem** in `examples3/Jordan Operator Algebras/joa-m/joa-m.md`
2. **Quote the equation number** (e.g., "(2.35)")
3. **Note the section** (e.g., "2.4.4")
4. If not found, either derive from known formulas or flag as potentially wrong

### Verified Theorems in Codebase

| Lean theorem | H-O reference | Status |
|--------------|---------------|--------|
| `four_variable_identity` | (2.34) | ✓ Verified |
| `operator_formula` | (2.35) | ✓ Verified |
| `linearized_jordan_operator` | (2.33) | ✓ Verified |
| `peirce_polynomial_identity` | 2.6.2 / (2.64) | ✓ Verified |
| `primitive_peirce_one_scalar` | 2.9.4(ii) | ✓ Statement verified |

### Session 73 Summary

**No code changes.** Verified H-O book access at:
`examples3/Jordan Operator Algebras/joa-m/joa-m.md`

Key finding: Two sorried theorems (`L_e_L_a_L_e`, `opComm_double_idempotent`) are
not directly in H-O. Need to either derive them or remove them.

---

## Session 74: Deep Analysis of `primitive_peirce_one_scalar`

### H-O 2.9.4(ii) Proof Located and Analyzed

Found exact proof in H-O book (lines 2221-2233 in joa-m.md):

> "Conversely, assume that p is minimal, and let a ∈ {pAp}. Since the algebra
> generated by a and p satisfies the conditions of 2.9.3, it is a direct sum of
> fields, and in particular the identity p of this algebra is a sum of the
> identities q₁,...,qₙ of these fields. By the minimality of p we must have n = 1,
> so the algebra generated by p and a is a field. The only finite-dimensional
> fields over ℝ are ℝ and ℂ however (2.2.6), and the latter must be eliminated
> because it is not formally real. Hence this field is ℝp."

### Proof Structure for Implementation

**Prerequisites from H-O:**
1. **Lemma 2.9.3:** Abelian ring without nilpotents + DCC → direct sum of fields
2. **Lemma 2.9.4(i):** Formally real Jordan algebras have no nilpotents
3. **Result 2.2.6:** Only finite-dim formally real fields over ℝ are ℝ itself

**For any a ∈ PeirceSpace e 1 (= {eAe}):**
1. The subalgebra generated by a and e is commutative (Jordan algebras)
2. Has no nilpotents (from 2.9.4(i) and formal reality)
3. Finite-dimensional → Artinian → satisfies DCC
4. By 2.9.3 → product of fields F₁ ⊕ ... ⊕ Fₙ
5. Each Fᵢ is finite-dim over ℝ with identity eᵢ
6. Sum of eᵢ = p (the identity of the algebra)
7. Minimality of p: no proper idempotent → n = 1
8. So algebra = single field F
9. Formally real → F ≠ ℂ → F = ℝ
10. Hence a ∈ ℝp

### Key Mathlib Results Identified

```lean
-- For step 4: Artinian reduced → semisimple → product of fields
IsArtinianRing.equivPi (R : Type*) [CommRing R] [IsArtinianRing R] [IsReduced R] :
  R ≃+* ((I : MaximalSpectrum R) → R / I)

-- Alternative: Artinian + reduced + local → field
IsArtinianRing.isField_of_isReduced_of_isLocalRing
```

### Implementation Path

1. **Define ring structure on PeirceSpace e 1:**
   - Multiplication: jmul restricted (closed by `peirce_mult_P1_P1`)
   - Identity: e (membership by `idempotent_in_peirce_one`)
   - Associativity: From power associativity + e as identity

2. **Prove reduced (no nilpotents):**
   - Use formal reality: a^m = 0 implies a = 0
   - H-O 2.9.4(i) proof: if a^(m-1) ≠ 0, a^m = 0, then a^k = 0 for k = ⌈m/2⌉
   - Since (a^k)² = a^(2k) ⊇ a^m = 0, formal reality gives a^k = 0

3. **Apply mathlib's structure theorem:**
   - PeirceSpace e 1 finite-dim ℝ-module → IsNoetherianRing → IsArtinianRing
   - Apply `IsArtinianRing.equivPi`

4. **Use minimality:**
   - Each factor has identity eᵢ which is idempotent
   - p = Σ eᵢ and eᵢ ∘ p = eᵢ
   - Minimality of p → all eᵢ = 0 or p → single field

5. **Eliminate ℂ by formal reality:**
   - In ℂ, i² = -1 violates formal reality
   - Only option is ℝ

### Alternative: Dimensional Argument

Simpler but less direct:
1. Suppose dim(PeirceSpace e 1) > 1
2. Take x linearly independent from e
3. The algebra generated by x is commutative + no nilpotents + finite-dim
4. This is a field over ℝ (by above analysis)
5. Finite-dim formally real field over ℝ = ℝ
6. So x ∈ ℝ·1 = ℝ·e (since e is identity in this algebra)
7. Contradiction with x independent from e
8. Hence dim = 1, so PeirceSpace e 1 = ℝ·e

### Issues Created (17 total)

**Foundation (ready now):**
- af-wjdv, af-8mz4: identity lemmas
- af-8bry, af-g16d: Mul and One definitions
- af-60x0: AddCommGroup
- af-niay: no nilpotents
- af-n2e3: FiniteDimensional

**Ring structure:**
- af-1tzf: KEY associativity proof
- af-qrr5, af-elpg, af-n3xe, af-gwqf: ring axioms

**Artinian theory:**
- af-t68m: IsReduced
- af-nl8m: IsArtinian
- af-5669: equivPi structure theorem

**Final:**
- af-agxd, af-pdie: field classification
- af-2oyk: minimality argument
- af-sgff: FILL primitive_peirce_one_scalar

---

## References

- Hanche-Olsen & Størmer, *Jordan Operator Algebras* (see `examples3/Jordan Operator Algebras/`)
- McCrimmon, *A Taste of Jordan Algebras*
