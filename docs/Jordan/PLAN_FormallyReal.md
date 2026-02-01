# FormallyReal Sorry Elimination Plan

## Overview

This document provides detailed step-by-step plans for eliminating the 5 sorries across
the `FormallyReal/*.lean` files:

| File | Sorries | Nature |
|------|---------|--------|
| `Def.lean` | 2 | Cone salience (circular dependency) |
| `Square.lean` | 2 | Square root uniqueness and existence |
| `Spectrum.lean` | 1 | Spectral eigenvalue non-negativity |

---

## 1. FormallyReal/Def.lean - Cone Salience Sorries (Lines 75, 80)

### Context

The theorem `of_sq_eq_zero` attempts to prove that if `jsq a = 0 -> a = 0` for all `a`,
then the full `sum_sq_eq_zero` property holds. This requires showing that sums of squares
form a **salient cone** (if x and -x are both sums of squares, then x = 0).

### Sorry 1 (Line 75) - Fin.last case

**Goal state:**
```lean
case succ.refine_1
J : Type u_1
inst : JordanAlgebra J
h : forall (a : J), JordanAlgebra.jsq a = 0 -> a = 0
n : Nat
ih : forall (a : Fin n -> J), sum i, JordanAlgebra.jsq (a i) = 0 -> forall (i : Fin n), a i = 0
a : Fin (n + 1) -> J
hsum : JordanAlgebra.jsq (a 0) + sum i, JordanAlgebra.jsq (a i.succ) = 0
i : Fin (n + 1)
|- a (Fin.last n) = 0
```

**What needs to be proven:**
From `jsq (a 0) + sum i, jsq (a i.succ) = 0`, conclude `a (Fin.last n) = 0`.

### Sorry 2 (Line 80) - Fin.castSucc case

**Goal state:**
```lean
case succ.refine_2
J : Type u_1
inst : JordanAlgebra J
h : forall (a : J), JordanAlgebra.jsq a = 0 -> a = 0
n : Nat
ih : forall (a : Fin n -> J), sum i, JordanAlgebra.jsq (a i) = 0 -> forall (i : Fin n), a i = 0
a : Fin (n + 1) -> J
hsum : JordanAlgebra.jsq (a 0) + sum i, JordanAlgebra.jsq (a i.succ) = 0
i : Fin (n + 1)
j : Fin n
|- a j.castSucc = 0
```

**What needs to be proven:**
From the same sum constraint, conclude `a j.castSucc = 0`.

### The Core Mathematical Issue

Both sorries require showing that **a sum of squares = 0 implies each summand = 0**.
This is **NOT derivable** from just `jsq a = 0 -> a = 0` without additional structure.

**Counterexample intuition:** In an abstract Jordan algebra with no ordering, one could
have `jsq a + jsq b = 0` with `jsq a = -jsq b` if negative squares existed.

The key insight is that this direction of the equivalence **requires** either:
1. An explicit ordering (squares are non-negative)
2. Spectral theory (eigenvalues of squares are non-negative real numbers)
3. Concrete structure (matrices, spin factors, etc.)

### Circular Dependency Analysis

The proof path creates a circular dependency:

```
of_sq_eq_zero (needs cone salience)
     |
     v
positiveCone_salient (in OrderedCone.lean, line 87)
     |
     v
uses FormallyRealJordan.sum_sq_eq_zero
     |
     v
(which is what of_sq_eq_zero is trying to define!)
```

**Verified in OrderedCone.lean lines 92-112:** The `positiveCone_salient` theorem
uses `FormallyRealJordan.sum_sq_eq_zero` to prove that the cone of squares is salient.
This means we **cannot** use cone salience to prove `of_sq_eq_zero`.

### Elimination Strategy

**Option A: Accept as Fundamental Axiom Gap (Recommended)**

Leave the sorries as documented gaps. The theorem `of_sq_eq_zero` is primarily for
documentation - concrete Jordan algebras (Hermitian matrices, spin factors) prove
`FormallyRealJordan` directly without using this theorem.

**LOC:** 0 (documentation only)

**Option B: Add Ordering Axiom**

Add an ordering axiom to `FormallyRealJordan`:
```lean
class FormallyRealJordan (J : Type*) [JordanAlgebra J] : Prop where
  sum_sq_eq_zero : forall (n : Nat) (a : Fin n -> J),
    (sum i, jsq (a i)) = 0 -> forall i, a i = 0
  -- Alternative: require partial order directly
```

**LOC:** ~10 (axiom change) + ~50 (verify concrete instances)

**Option C: Spectral Theory Approach**

Require spectral decomposition exists (finite-dimensional case):
1. Add `[FinDimJordanAlgebra J]` hypothesis
2. Use spectral theorem: every element decomposes as `sum lambda_i * e_i`
3. Squares have non-negative eigenvalues (squares of reals)
4. Sum of non-negative things = 0 implies each = 0

**LOC:** ~200 (requires Phases 1-6 of spectral implementation)

**Blocking:** Requires `SpectralTheorem.lean` to be complete.

### Recommended Path

**Keep sorries documented.** The existing pattern works:
- Concrete types define `FormallyRealJordan` directly
- The `FormallyRealJordan' -> FormallyRealJordan` instance was removed
- Abstract theory accepts this as a fundamental gap

---

## 2. FormallyReal/Square.lean - Square Root Sorries (Lines 102, 118)

### Sorry 1 (Line 102) - Square Root Uniqueness

**Location:** `isPositiveSqrt_unique` theorem

**Goal state:**
```lean
J : Type u_1
inst1 : JordanAlgebra J
inst : FormallyRealJordan J
a b c : J
hb : IsPositiveSqrt a b
hc : IsPositiveSqrt a c
hcomm : jmul b c = jmul c b
hcomm2 : jmul (jsq b) c = jmul c (jsq b)
hbeq : jsq b = a
hceq : jsq c = a
hsq_eq : jsq b = jsq c
hdiff : jmul (b - c) (b + c) = 0
|- b = c
```

**What has been established:**
- `b^2 = c^2 = a`
- `(b - c)(b + c) = 0`

**What needs to be proven:**
From `(b-c)(b+c) = 0`, conclude `b = c`.

### Elimination Strategy for Uniqueness

**Mathematical approach:**

The key insight is that for positive elements in a JB-algebra, `b + c` is **invertible**
(or at least "cancellable"). This is because:
1. b, c are positive (sums of squares)
2. b + c is also positive
3. Positive elements with `e` as identity have spectrum bounded away from 0

However, we need one of:

**Step 1: Show (b-c)^2 = 0 directly (~30 LOC)**

From `(b-c)(b+c) = 0` and commutativity assumptions:
```lean
-- Goal: (b-c)^2 = 0
-- Expand: (b-c)^2 = b^2 - 2bc + c^2 = a - 2bc + a = 2a - 2bc = 2(a - bc)
-- Need: a = bc, i.e., b^2 = bc (since b^2 = a)
-- This holds iff b = c (circular!) or b(b-c) = 0
```

This approach leads to circularity.

**Step 2: Alternative - Use Positivity (~50 LOC)**

If `b + c` is positive and nonzero, and `(b-c)(b+c) = 0`, then:
1. `b - c` is in the annihilator of `b + c`
2. For formally real algebras, the annihilator of a positive element is `{0}`
3. Hence `b - c = 0`

**Key lemma needed:**
```lean
theorem annihilator_of_positive_is_zero [FormallyRealJordan J]
    {x y : J} (hx : PositiveElement x) (hx_ne : x != 0)
    (hxy : jmul x y = 0) : y = 0
```

**Proof of key lemma:**
- `y` decomposes into Peirce spaces of idempotents in the spectral decomposition of x
- For the Peirce 0 space of any primitive in x's decomposition, `jmul p y = 0` for all y there
- But `jmul x y = 0` with positive x means y is in the intersection of all Peirce 0 spaces
- This intersection is `{0}` when x is "full" (has full support)

**LOC estimate:** 50-80 LOC (requires spectral theory infrastructure)

**Blocking:** Requires Peirce theory + spectral projections

### Sorry 2 (Line 118) - Square Root Existence

**Location:** `HasPositiveSqrt.of_positiveElement` theorem

**Goal state:**
```lean
J : Type u_1
inst : JordanAlgebra J
a : J
ha : PositiveElement a
|- HasPositiveSqrt a
```

**What needs to be proven:**
Every positive element (sum of squares) has a positive square root.

### Elimination Strategy for Existence

This is a consequence of the **spectral theorem** for JB-algebras:

**Step 1: Spectral decomposition of a (~30 LOC)**
```lean
-- a is positive, so has spectral decomposition a = sum lambda_i * e_i
-- with lambda_i >= 0 (non-negative eigenvalues)
obtain (sd : SpectralDecomp a, h_nonneg : forall i, 0 <= sd.eigenvalues i) :=
  spectral_decomp_of_positive ha
```

**Step 2: Define sqrt(a) using functional calculus (~30 LOC)**
```lean
-- Define b = sum (sqrt lambda_i) * e_i
let b := sum i, Real.sqrt (sd.eigenvalues i) * sd.csoi.idem i
```

**Step 3: Verify b^2 = a (~20 LOC)**
```lean
-- b^2 = (sum sqrt(lambda_i) * e_i)^2 = sum lambda_i * e_i = a
-- Uses orthogonality of CSOI
```

**Step 4: Verify b is positive (~20 LOC)**
```lean
-- b = sum (sqrt lambda_i) * e_i
-- Each sqrt(lambda_i) * e_i is a square: (lambda_i^{1/4})^2 * e_i^2 = sqrt(lambda_i) * e_i
-- Hence b is a sum of squares
```

**Total LOC:** ~100

**Blocking:** Requires spectral theorem (Phase 6 of implementation plan)

### Summary for Square.lean

| Sorry | Approach | LOC | Blocking |
|-------|----------|-----|----------|
| Line 102 | Annihilator lemma | 50-80 | Spectral theory |
| Line 118 | Functional calculus | ~100 | Spectral theorem |

---

## 3. FormallyReal/Spectrum.lean - Eigenvalue Non-negativity (Line 136)

### Context

**Location:** `FormallyRealJordan.spectral_sq_eigenvalues_nonneg` theorem

**Goal state:**
```lean
J : Type u_1
inst1 : JordanAlgebra J
inst : FormallyRealJordan J
a : J
sd : SpectralDecomp (jsq a)
i : Fin sd.n
|- 0 <= sd.eigenvalues i
```

**What needs to be proven:**
The eigenvalues in the spectral decomposition of a square are non-negative.

### Mathematical Background

This follows from the spectral theorem:
1. Every element `a` has a spectral decomposition: `a = sum lambda_i * e_i`
2. Then `a^2 = sum lambda_i^2 * e_i` (by orthogonality of CSOI)
3. The eigenvalues of `a^2` are `{lambda_i^2}`
4. All squares of reals are non-negative: `lambda_i^2 >= 0`

### Elimination Strategy

**Step 1: Establish spectral decomposition of a (~20 LOC)**
```lean
-- Get spectral decomposition of a (the element being squared)
obtain (sd_a : SpectralDecomp a) := spectral_decomp_exists a
```

**Step 2: Show a^2 has squared eigenvalues (~30 LOC)**
```lean
-- Theorem: spectral_sq_eigenvalues
-- a^2 has eigenvalues {lambda_i^2} with the same CSOI as a
theorem spectral_sq_eigenvalues (sd_a : SpectralDecomp a) :
    exists sd_sq : SpectralDecomp (jsq a),
      sd_sq.csoi = sd_a.csoi /\ forall i, sd_sq.eigenvalues i = (sd_a.eigenvalues i)^2
```

**Step 3: Conclude non-negativity (~10 LOC)**
```lean
-- sd.eigenvalues i = (sd_a.eigenvalues j)^2 for some j
-- Squares of reals are non-negative
exact sq_nonneg _
```

**Total LOC:** ~60

**Blocking:** Requires `spectral_sq_eigenvalues` theorem (Phase 6)

### Current Code Analysis

Looking at `Spectrum.lean` lines 127-136, the structure is already in place:
- `SpectralDecomp` is defined
- `jordanSpectrum` extracts eigenvalues
- The theorem statement is correct

The sorry is there because we don't yet have:
1. `spectral_decomp_exists` for the original element `a`
2. `spectral_sq_eigenvalues` relating `a^2`'s decomposition to `a`'s

---

## Dependency Analysis

### Overall Dependency Chain

```
Peirce.lean (0 sorries, COMPLETE)
    |
    v
Primitive.lean (4 sorries)
    |-- primitive_peirce_one_dim_one
    |-- orthogonal_primitive_peirce_sq
    |-- exists_primitive_decomp
    |-- csoi_refine_primitive
    |
    v
SpectralTheorem.lean (needs creation)
    |-- spectral_decomp_exists
    |-- spectral_sq_eigenvalues
    |
    v
FormallyReal/Spectrum.lean (sorry line 136)
    |
    v
FormallyReal/Square.lean (sorries lines 102, 118)
    |
    v
FormallyReal/Def.lean (sorries lines 75, 80) [Circular - see above]
```

### Key Blocker: `primitive_peirce_one_dim_one`

The critical sorry is `primitive_peirce_one_dim_one` in Primitive.lean (line 322).
This blocks the entire spectral theory chain.

**Current state:** The proof outline is in place:
1. Get quadratic relation from finite dimension (TODO)
2. Discriminant analysis (mostly done in `lagrange_idempotent_in_peirce_one`)
3. One algebraic computation sorry at line 261

---

## Detailed Step-by-Step Elimination Plans

### Plan A: Complete Primitive Theory First

**Session 1: Fix lagrange_idempotent_in_peirce_one sorry (Line 261)**

1. Read Primitive.lean lines 250-262
2. Goal: `(1 / Delta) * (s + mu ^ 2) = -(1 / Real.sqrt Delta) * mu`
3. Algebraic verification:
   - mu = (r - sqrt(Delta))/2
   - mu^2 = (r^2 - 2r*sqrt(Delta) + Delta)/4
   - s + mu^2 = s + (r^2 - 2r*sqrt(Delta) + Delta)/4
   - Use Delta = r^2 + 4s, so 4s = Delta - r^2
   - s = (Delta - r^2)/4
   - s + mu^2 = (Delta - r^2)/4 + (r^2 - 2r*sqrt(Delta) + Delta)/4
              = (2*Delta - 2r*sqrt(Delta))/4 = (Delta - r*sqrt(Delta))/2
   - (1/Delta) * (s + mu^2) = (Delta - r*sqrt(Delta))/(2*Delta)
                            = 1/2 - r/(2*sqrt(Delta))
   - -(1/sqrt(Delta)) * mu = -(r - sqrt(Delta))/(2*sqrt(Delta))
                           = -r/(2*sqrt(Delta)) + 1/2
   - These are equal!

4. Implementation: Use `field_simp` and `ring` for the computation
5. LOC: ~20

**Session 2: Add quadratic relation extraction lemma**

1. Add to Primitive.lean:
```lean
theorem exists_quadratic_in_peirce_one [FinDimJordanAlgebra J]
    {e : J} (he : IsIdempotent e) {x : J} (hx : x ∈ PeirceSpace e 1) (hx_ne : x != 0) :
    exists r s : Real, jsq x = r * x + s * e
```

2. Proof outline:
   - P_1(e) is finite-dimensional (submodule of fin-dim module)
   - {e, x, x^2} spans at most 3-dim subspace
   - If dim P_1(e) >= 3: no constraint, but for primitive e, dim = 1
   - By finite dimension, powers of x are linearly dependent
   - Extract minimal polynomial relation

3. LOC: ~40

**Session 3: Complete primitive_peirce_one_dim_one**

1. Use `exists_quadratic_in_peirce_one` to get `jsq x = r * x + s * e`
2. Case split on discriminant Delta = r^2 + 4s:
   - If Delta <= 0: Use `peirce_one_sq_nonpos_imp_zero`
   - If Delta > 0: Use `lagrange_idempotent_in_peirce_one`
3. Both cases give `x in Real * e`
4. LOC: ~40

### Plan B: Complete Spectral Theory

After Primitive theory is complete:

**Session 4: Create SpectralTheorem.lean**

1. Define `spectrum a` as eigenvalue set of L_a
2. Prove spectrum is finite (finite-dimensional)
3. Prove `spectral_decomp_exists` using primitive CSOI
4. LOC: ~100

**Session 5: Prove spectral properties of squares**

1. Prove `spectral_sq_eigenvalues`: a^2 eigenvalues = squared eigenvalues of a
2. Proof uses CSOI orthogonality: (sum lambda_i e_i)^2 = sum lambda_i^2 e_i
3. LOC: ~50

**Session 6: Eliminate Spectrum.lean sorry**

1. Apply `spectral_sq_eigenvalues` to get eigenvalues are squares
2. Conclude non-negativity from `sq_nonneg`
3. LOC: ~20

### Plan C: Complete Square.lean

**Session 7: Prove annihilator lemma**

1. Add theorem: if x positive and nonzero, jmul x y = 0 implies y = 0
2. Uses spectral structure of positive elements
3. LOC: ~50

**Session 8: Complete isPositiveSqrt_unique**

1. Apply annihilator lemma to `b + c` and `b - c`
2. Conclude `b - c = 0`
3. LOC: ~30

**Session 9: Complete HasPositiveSqrt.of_positiveElement**

1. Use spectral decomposition of positive element
2. Define sqrt via functional calculus
3. Verify properties
4. LOC: ~50

---

## Summary Table

| File | Line | Sorry | Dependencies | LOC Est. | Priority |
|------|------|-------|--------------|----------|----------|
| Def.lean | 75 | cone salience (last) | Circular | 0 (accept gap) | Low |
| Def.lean | 80 | cone salience (castSucc) | Circular | 0 (accept gap) | Low |
| Square.lean | 102 | uniqueness | Spectral + annihilator | 80 | Medium |
| Square.lean | 118 | existence | Spectral theorem | 100 | Medium |
| Spectrum.lean | 136 | eigenvalues nonneg | Spectral theorem | 60 | High |

### Recommended Execution Order

1. **Fix lagrange_idempotent sorry** (Line 261 in Primitive.lean) - ~20 LOC
2. **Add quadratic extraction lemma** - ~40 LOC
3. **Complete primitive_peirce_one_dim_one** - ~40 LOC
4. **Create SpectralTheorem.lean** - ~100 LOC
5. **Eliminate Spectrum.lean sorry** - ~60 LOC
6. **Square.lean existence** - ~100 LOC
7. **Square.lean uniqueness** - ~80 LOC
8. **Def.lean sorries** - Document as accepted gaps

**Total new LOC needed:** ~440

**Total sessions estimated:** 7-9 (at 50 LOC/session)

---

## Circular Dependency Resolution

The Def.lean sorries create a circular dependency that **cannot be resolved** within
the current type class structure. The recommended approach is:

1. **Keep `of_sq_eq_zero` as a documented theorem with sorries**
2. **Remove the `FormallyRealJordan' -> FormallyRealJordan` instance** (already done)
3. **Concrete types prove `FormallyRealJordan` directly** (already done)
4. **Document in LEARNINGS.md** that abstract formally real theory has this gap

This is mathematically sound because:
- The equivalence `sum_sq_eq_zero <-> sq_eq_zero -> 0` holds in proper cone contexts
- Our concrete instances (matrices, spin factors) don't use this direction
- The abstract gap reflects genuine mathematical subtlety (need ordering/spectral theory)

---

## References

- Hanche-Olsen & Stormer, *Jordan Operator Algebras*, Sections 2.9, 3.2
- `LEARNINGS.md` - Sessions 50-84 document the evolution of this understanding
- `SPECTRAL_IMPLEMENTATION_PLAN.md` - Full 7-phase implementation roadmap
